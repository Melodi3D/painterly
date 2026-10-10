
"""
PAINTERLY V15.4
By Melodi Clark
"""

import maya.cmds as cmds
import maya.api.OpenMaya as om

import math
import random
import bisect
import traceback


# SETTINGS

SEED = 1540
COVERAGE = 1.0
SEGMENTS = 4

HIDE_PREVIOUS = True

# Direction the cat faces in WORLD SPACE.
# Options: "+X", "-X", "+Z", "-Z"
HEAD_DIRECTION = "+Z"

BASE_LIFT = 0.00022
DIRECTION_JITTER = 16.0

# Name, count, length, width, height
# Body widths increased approximately 35%.

OIL_LAYERS = [
    ("BodyBase",   8500, 0.021, 0.0100, 0.00055),
    ("BodyMedium", 7200, 0.014, 0.0068, 0.00040),
    ("BodyDetail", 5600, 0.008, 0.0035, 0.00025),
]

# Larger fine face strokes.
FACE_LAYERS = [
    ("FaceFine",  5200, 0.0055, 0.0024, 0.00016),
    ("FaceMicro", 3800, 0.0035, 0.0014, 0.00010),
]

HEAD_START = 0.70
FACE_START = 0.79

REGIONS = {
    "BODY": {
        "density": 1.0,
        "length": 1.0,
        "width": 1.0,
        "height": 1.0,
    },
    "HEAD": {
        "density": 1.0,
        "length": 0.60,
        "width": 0.75,
        "height": 0.50,
    },
    "FACE": {
        "density": 0.60,
        "length": 0.45,
        "width": 0.60,
        "height": 0.40,
    },
    "LEGS": {
        "density": 1.0,
        "length": 0.65,
        "width": 0.65,
        "height": 0.60,
    },
    "PAWS": {
        "density": 0.90,
        "length": 0.42,
        "width": 0.48,
        "height": 0.50,
    },
    "TAIL": {
        "density": 1.0,
        "length": 0.65,
        "width": 0.65,
        "height": 0.60,
    },
}


# HELPERS


def get_dag(node):
    selection = om.MSelectionList()
    selection.add(node)
    return selection.getDagPath(0)


def normalized(vector):
    if vector.length() < 1e-10:
        return om.MVector(0, 1, 0)
    return vector.normal()


def get_selected_meshes():
    selection = cmds.ls(
        selection=True,
        long=True,
        objectsOnly=True
    ) or []

    meshes = []

    for obj in selection:

        if cmds.nodeType(obj) == "mesh":
            shapes = [obj]

        else:
            shapes = cmds.listRelatives(
                obj,
                allDescendents=True,
                shapes=True,
                noIntermediate=True,
                fullPath=True,
                type="mesh"
            ) or []

        for shape in shapes:
            if shape in meshes:
                continue

            if not cmds.getAttr(
                shape + ".intermediateObject"
            ):
                meshes.append(shape)

    if not meshes:
        raise RuntimeError(
            "Select the ORIGINAL polygon mesh first."
        )

    return meshes


# MATERIALS

def get_materials(mesh_fn, path):

    try:
        shaders, face_ids = mesh_fn.getConnectedShaders(
            path.instanceNumber()
        )

        names = [
            om.MFnDependencyNode(shader).name()
            for shader in shaders
        ]

        if names:
            return names, list(face_ids)

    except Exception as error:
        print("Material lookup warning:", error)

    groups = cmds.listConnections(
        path.fullPathName(),
        type="shadingEngine"
    ) or []

    return (
        [groups[0] if groups else "initialShadingGroup"],
        [0] * mesh_fn.numPolygons
    )


# ============================================================
# REGION DETECTION
# ============================================================

def get_region(position, bounds):

    min_x, min_y, min_z = bounds[:3]
    max_x, max_y, max_z = bounds[3:]

    sx = max(max_x - min_x, 1e-8)
    sy = max(max_y - min_y, 1e-8)
    sz = max(max_z - min_z, 1e-8)

    x = (position.x - min_x) / sx
    y = (position.y - min_y) / sy
    z = (position.z - min_z) / sz

    if HEAD_DIRECTION == "+X":
        forward = x
    elif HEAD_DIRECTION == "-X":
        forward = 1.0 - x
    elif HEAD_DIRECTION == "-Z":
        forward = 1.0 - z
    else:
        forward = z

    if forward > FACE_START and y > 0.46:
        return "FACE"

    if forward > HEAD_START and y > 0.45:
        return "HEAD"

    if y < 0.12:
        return "PAWS"

    if y < 0.40:
        return "LEGS"

    if forward < 0.14 and y > 0.45:
        return "TAIL"

    return "BODY"


# TRIANGLE CACHE


def build_triangle_cache(mesh_fn, face_materials):

    points = mesh_fn.getPoints(om.MSpace.kWorld)
    counts, ids = mesh_fn.getTriangles()

    try:
        uv_set = mesh_fn.currentUVSetName()
    except Exception:
        uv_set = None

    triangles = []
    cumulative = []
    total_area = 0.0
    cursor = 0

    for face_id, count in enumerate(counts):

        uv_map = {}

        if uv_set:
            try:
                vertices = mesh_fn.getPolygonVertices(face_id)

                for local, vertex_id in enumerate(vertices):
                    uv_map[int(vertex_id)] = (
                        mesh_fn.getPolygonUV(
                            face_id,
                            local,
                            uv_set
                        )
                    )

            except Exception:
                pass

        for _ in range(int(count)):

            ia = int(ids[cursor])
            ib = int(ids[cursor + 1])
            ic = int(ids[cursor + 2])
            cursor += 3

            a, b, c = [
                om.MVector(points[i])
                for i in (ia, ib, ic)
            ]

            cross = (b - a) ^ (c - a)
            area = cross.length() * 0.5

            if area < 1e-12:
                continue

            ua, ub, uc = [
                uv_map.get(i, (0.5, 0.5))
                for i in (ia, ib, ic)
            ]

            du1 = ub[0] - ua[0]
            dv1 = ub[1] - ua[1]
            du2 = uc[0] - ua[0]
            dv2 = uc[1] - ua[1]

            determinant = du1 * dv2 - du2 * dv1

            if abs(determinant) > 1e-9:
                flow = (
                    (c - a) * du1
                    - (b - a) * du2
                ) / determinant
            else:
                flow = om.MVector(0, 1, 0)

            material_id = (
                face_materials[face_id]
                if face_id < len(face_materials)
                else 0
            )

            triangles.append((
                a, b, c,
                ua, ub, uc,
                cross.normal(),
                flow,
                material_id
            ))

            total_area += area
            cumulative.append(total_area)

    if not triangles:
        raise RuntimeError(
            "No valid triangles found."
        )

    return triangles, cumulative, total_area



# SURFACE SAMPLING


def sample_surface(cache, count, rng):

    triangles, cumulative, total = cache

    for i in range(count):

        target = (
            (i + rng.random()) / float(count)
        ) * total

        index = min(
            len(triangles) - 1,
            bisect.bisect_left(cumulative, target)
        )

        (
            a, b, c,
            ua, ub, uc,
            normal,
            flow,
            material_id
        ) = triangles[index]

        r = math.sqrt(rng.random())
        s = rng.random()

        w0 = 1.0 - r
        w1 = r * (1.0 - s)
        w2 = r * s

        position = (
            a * w0
            + b * w1
            + c * w2
        )

        uv = (
            ua[0] * w0
            + ub[0] * w1
            + uc[0] * w2,

            ua[1] * w0
            + ub[1] * w1
            + uc[1] * w2
        )

        yield (
            position,
            normal,
            flow,
            uv,
            material_id
        )


# STROKE ORIENTATION


def get_stroke_axes(normal, flow, rng):

    along = flow - normal * (flow * normal)

    if along.length() < 1e-8:
        along = (
            om.MVector(0, 1, 0)
            - normal * normal.y
        )

    if along.length() < 1e-8:
        along = normal ^ om.MVector(1, 0, 0)

    along = normalized(along)
    side = normalized(normal ^ along)

    angle = math.radians(
        rng.uniform(
            -DIRECTION_JITTER,
            DIRECTION_JITTER
        )
    )

    along = normalized(
        along * math.cos(angle)
        + side * math.sin(angle)
    )

    side = normalized(normal ^ along)

    return along, side



# CONFORM TO ORIGINAL SURFACE


def conform_to_mesh(mesh_fn, guess, lift, fallback):

    try:
        closest, _ = mesh_fn.getClosestPoint(
            om.MPoint(guess),
            om.MSpace.kWorld
        )

        normal, _ = mesh_fn.getClosestNormal(
            closest,
            om.MSpace.kWorld
        )

        normal = normalized(normal)

        return om.MPoint(
            closest + normal * lift
        )

    except Exception:
        return om.MPoint(
            guess + fallback * lift
        )


# BUILD PAINT LAYER


def build_paint_layer(
    mesh_fn,
    cache,
    materials,
    parent_group,
    diagonal,
    bounds,
    settings,
    rng,
    face_only=False
):

    (
        label,
        base_count,
        length_ratio,
        width_ratio,
        height_ratio
    ) = settings

    count = max(
        1,
        int(base_count * COVERAGE)
    )

    buckets = {}
    accepted = 0

    if face_only:

        samples = []
        attempts = 0
        max_attempts = count * 120

        while (
            len(samples) < count
            and attempts < max_attempts
        ):

            batch = min(
                1000,
                count - len(samples) + 100
            )

            for sample in sample_surface(
                cache,
                batch,
                rng
            ):

                attempts += 1

                if get_region(
                    sample[0],
                    bounds
                ) == "FACE":

                    samples.append(sample)

                    if len(samples) >= count:
                        break

                if attempts >= max_attempts:
                    break

    else:
        samples = sample_surface(
            cache,
            count,
            rng
        )

    for (
        center,
        normal,
        flow,
        uv,
        material_id
    ) in samples:

        region = get_region(center, bounds)

        if not face_only:
            if rng.random() > REGIONS[region]["density"]:
                continue

        accepted += 1

        if (
            material_id < 0
            or material_id >= len(materials)
        ):
            material_id = 0

        bucket = buckets.setdefault(
            material_id,
            {
                "vertices": [],
                "faces": [],
                "connects": [],
                "u": [],
                "v": [],
                "uvconnects": []
            }
        )

        along, side = get_stroke_axes(
            normal,
            flow,
            rng
        )

        if face_only:
            length_scale = 1.0
            width_scale = 1.0
            height_scale = 1.0

        else:
            region_settings = REGIONS[region]

            length_scale = region_settings["length"]
            width_scale = region_settings["width"]
            height_scale = region_settings["height"]

        length = (
            diagonal
            * length_ratio
            * length_scale
            * rng.uniform(0.80, 1.15)
        )

        width = (
            diagonal
            * width_ratio
            * width_scale
            * rng.uniform(0.85, 1.15)
        )

        height = (
            diagonal
            * height_ratio
            * height_scale
            * rng.uniform(0.85, 1.15)
        )

        bend = (
            rng.uniform(-0.12, 0.12)
            * width
        )

        base = len(bucket["vertices"])

        for j in range(SEGMENTS + 1):

            t = j / float(SEGMENTS)

            envelope = max(
                0.015,
                math.sin(math.pi * t) ** 0.55
            )

            center_guess = (
                center
                + along * ((t - 0.5) * length)
                + side * (
                    bend * math.sin(math.pi * t)
                )
            )

            for lateral, ridge in (
                (-0.5, 0),
                (0, 1),
                (0.5, 0)
            ):

                guess = (
                    center_guess
                    + side * (
                        lateral
                        * width
                        * envelope
                    )
                )

                lift = (
                    diagonal * BASE_LIFT
                    + height * ridge * envelope
                )

                bucket["vertices"].append(
                    conform_to_mesh(
                        mesh_fn,
                        guess,
                        lift,
                        normal
                    )
                )

                bucket["u"].append(
                    uv[0] + lateral * 0.00005
                )

                bucket["v"].append(
                    uv[1] + (t - 0.5) * 0.0001
                )

        for j in range(SEGMENTS):

            a = base + j * 3
            b = a + 3

            triangles = (
                (a, b, a + 1),
                (b, b + 1, a + 1),
                (a + 1, b + 1, a + 2),
                (b + 1, b + 2, a + 2)
            )

            for triangle in triangles:

                bucket["faces"].append(3)
                bucket["connects"].extend(triangle)
                bucket["uvconnects"].extend(triangle)

    created = 0

    for material_id, bucket in buckets.items():

        if not bucket["vertices"]:
            continue

        transform_obj = om.MFnTransform().create()

        om.MFnDagNode(transform_obj).setName(
            "V15_4_"
            + label
            + "_Mat"
            + str(material_id)
            + "#"
        )

        output_mesh = om.MFnMesh()

        output_mesh.create(
            bucket["vertices"],
            bucket["faces"],
            bucket["connects"],
            parent=transform_obj
        )

        output_mesh.setName(
            "V15_4_" + label + "Shape#"
        )

        transform = om.MFnDagNode(
            transform_obj
        ).fullPathName()

        transform = cmds.parent(
            transform,
            parent_group
        )[0]

        shapes = cmds.listRelatives(
            transform,
            shapes=True,
            fullPath=True,
            noIntermediate=True
        ) or []

        if shapes:

            shape = shapes[0]

            try:
                output_fn = om.MFnMesh(
                    get_dag(shape)
                )

                try:
                    uv_set = output_fn.currentUVSetName()
                except Exception:
                    uv_set = "map1"

                output_fn.setUVs(
                    bucket["u"],
                    bucket["v"],
                    uv_set
                )

                output_fn.assignUVs(
                    bucket["faces"],
                    bucket["uvconnects"],
                    uv_set
                )

                output_fn.updateSurface()

            except Exception as error:
                print("UV warning:", error)

            for attribute in (
                "primaryVisibility",
                "doubleSided",
                "aiOpaque"
            ):

                if cmds.attributeQuery(
                    attribute,
                    node=shape,
                    exists=True
                ):

                    try:
                        cmds.setAttr(
                            shape + "." + attribute,
                            1
                        )
                    except Exception:
                        pass

        try:
            cmds.sets(
                transform,
                edit=True,
                forceElement=materials[material_id]
            )

        except Exception as error:
            print("Material warning:", error)

        created += 1

    print(
        "V15.4", label,
        "| strokes:", accepted,
        "| meshes:", created
    )

    return created


# MAIN

def run_v15_4():

    sources = get_selected_meshes()

    if HIDE_PREVIOUS:

        patterns = (
            "PainterlyV12_GRP*",
            "PainterlyV13_GRP*",
            "PainterlyV14*",
            "PainterlyV15_GRP*",
            "PainterlyV15_1_GRP*",
            "PainterlyV15_2_GRP*",
            "PainterlyV15_3_GRP*",
            "PainterlyV15_4_GRP*"
        )

        for pattern in patterns:

            for old in cmds.ls(
                pattern,
                type="transform"
            ) or []:

                try:
                    cmds.hide(old)
                except Exception:
                    pass

    root = cmds.group(
        empty=True,
        name="PainterlyV15_4_GRP#"
    )

    rng = random.Random(SEED)
    total_meshes = 0

    for source in sources:

        try:
            print("\nV15.4 source:", source)

            path = get_dag(source)
            mesh_fn = om.MFnMesh(path)

            materials, face_materials = get_materials(
                mesh_fn,
                path
            )

            cache = build_triangle_cache(
                mesh_fn,
                face_materials
            )

            bounds = cmds.exactWorldBoundingBox(
                source
            )

            diagonal = math.sqrt(
                sum(
                    (
                        bounds[i + 3]
                        - bounds[i]
                    ) ** 2
                    for i in range(3)
                )
            )

            if diagonal < 1e-9:
                raise RuntimeError(
                    "Source mesh has zero size."
                )

            subgroup = cmds.group(
                empty=True,
                name="V15_4_Object_GRP#",
                parent=root
            )

            for settings in OIL_LAYERS:

                total_meshes += build_paint_layer(
                    mesh_fn,
                    cache,
                    materials,
                    subgroup,
                    diagonal,
                    bounds,
                    settings,
                    rng,
                    face_only=False
                )

            for settings in FACE_LAYERS:

                total_meshes += build_paint_layer(
                    mesh_fn,
                    cache,
                    materials,
                    subgroup,
                    diagonal,
                    bounds,
                    settings,
                    rng,
                    face_only=True
                )

        except Exception:
            traceback.print_exc()

    cmds.select(clear=True)

    print("\n================================")
    print("PAINTERLY V15.4 COMPLETE")
    print("================================")
    print("Paint meshes:", total_meshes)
    print("Group:", root)

    if total_meshes == 0:
        print("WARNING: No paint geometry created.")

    return root


# RUN


run_v15_4()
