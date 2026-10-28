module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace.FixedPoints
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace.OrbitMap
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace.PointDegrees
public import Theory.Representation.Quotient

/-!
# The point-stabilizer route to the A₇ six-space

Transport the original component action along its specified A₇ isomorphism.
The point-stabilizer simple-degree gap gives a fixed vector or covector;
the seven-translate construction and the natural pairing then give an actual
linear intertwiner. Transport back with the same component marking.

The proved point-stabilizer degree gap discharges the remaining premise of
`sevenSixSpace`, while the conditional assembly remains available separately.
The ambient natural extension is already handled in `Seven.NaturalExtension`.

Source: Aschbacher–Smith K.1.2, printed p.452 (PDF p.463), citing GM02,
Theorem 6.2 and Table 6.3.
-/

public section
open Representation

namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource

universe u v

/-- Apply the point-stabilizer degree gap to the literal source input. The
result retains the actor isomorphism and an actual equivariant linear bijection. -/
theorem sevenSixSpace_of_pointSimpleDegrees
    (hdegrees : SevenSixSpace.PointSimpleDegrees.{v}) :
    RecognitionInputs.Seven.SixSpace.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h eL hd
  let σ : Representation (ZMod 2) SevenSixSpace.Actor V :=
    (ρ.comp L.subtype).comp eL.symm.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff eL.symm.toMonoidHom eL.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have hfixed := SevenSixSpace.fixed_or_dual hdegrees
    (σ.comp SevenSixSpace.PointStabilizer.subtype) hd
  obtain ⟨e⟩ := SevenSixSpace.of_point_fixed_or_dual σ hd hfixed
  refine ⟨{
    groupEquiv := eL
    linearEquiv := e.toLinearEquiv
    intertwines := ?_ }⟩
  intro g w
  have he := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' (eL g)) w
  change e.toLinearEquiv ((ρ.comp L.subtype) (eL.symm (eL g)) w) =
    alternatingNatural 7 (eL g) (e.toLinearEquiv w) at he
  simpa only [eL.symm_apply_apply] using he

/-- The irreducible binary A₇ six-space is its natural module, with an actual
actor isomorphism and linear intertwiner. This discharges the six-dimensional
recognition input in K.1.2 without an additional representation catalogue. -/
theorem sevenSixSpace : RecognitionInputs.Seven.SixSpace.{u,v} :=
  sevenSixSpace_of_pointSimpleDegrees SevenSixSpace.pointSimpleDegrees

end CFSG.Quasithin.ChapterK.Alternating
