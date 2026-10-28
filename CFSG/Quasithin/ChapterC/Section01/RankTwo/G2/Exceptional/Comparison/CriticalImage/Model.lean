module
public import Theory.Representation.G2BinaryPointFlagDisplacement
public import Theory.Representation.G2BinaryIsotropicThree.PairHyperplanes
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# Fixed spaces of the specified binary G₂ offender

Conjugate the given offender to the actual A–B–C root subgroup. The invariant
polar form makes its fixed three-space self-orthogonal, and the octonion root
calculation identifies the pointwise stabilizer with that same offender.
These facts apply to the full G₂(2) action on trace-zero octonions modulo scalars.
Source: MS93 (3.2)(vii), (3.3), printed pp.863–868; AS B.4.6(13).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.Comparison.CriticalImage

abbrev rho := Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2)

private theorem fixed_conjugate (g : Atlas.G2.Model (ZMod 2))
    (A : Subgroup (Atlas.G2.Model (ZMod 2))) :
    fixedSpace rho (A.map (MulAut.conj g).toMonoidHom) =
      (fixedSpace rho A).map (rho g) := by
  let E := LinearEquiv.ofBijective (rho g) (rho.apply_bijective g)
  symm
  apply fixedSpace_map_equivariant rho rho (MulAut.conj g).toMonoidHom E
  intro a v
  change rho g (rho a v) = rho (g*a*g⁻¹) (rho g v)
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]

/-- The fixed space of the specified natural offender is self-orthogonal. -/
theorem offender_fixed_orthogonal (A : Subgroup (Atlas.G2.Model (ZMod 2)))
    (hA : IsOffender rho A) :
    LinearMap.BilinForm.orthogonal Atlas.G2.Natural.BinaryPointFlag.pairing
      (fixedSpace rho A) = fixedSpace rho A := by
  obtain ⟨g,rfl⟩ := Atlas.G2.NaturalOffenders.offender_conjugate_elementary
    (F := ZMod 2) (n := 1) (by norm_num) (by decide) A hA
  rw [fixed_conjugate,Atlas.G2.Natural.BinaryIsotropicThree.fixed_elementary_eq_target]
  let U := Atlas.G2.Natural.BinaryIsotropicThree.target false
  have hU (v : Fin 6 → ZMod 2) :
      (∀ w ∈ U, Atlas.G2.Natural.BinaryPointFlag.pairing w v = 0) ↔ v ∈ U := by
    have hs (w v : Fin 6 → ZMod 2) :
        Atlas.G2.Natural.BinaryPointFlag.pairing w v =
          Atlas.G2.Natural.BinaryPointFlag.pairing v w := by
      simp only [Atlas.G2.Natural.BinaryPointFlag.pairing_apply]
      ring
    simp only [hs]
    have hseed : U = Atlas.G2.Natural.BinaryPointFlag.seed := by
      ext w
      change (w 3 = 0 ∧ w 4 = 0 ∧ w 5 = 0) ↔ _
      exact (Atlas.G2.Natural.BinaryPointFlag.mem_seed w).symm
    rw [hseed]
    exact Atlas.G2.Natural.BinaryPointFlag.orthogonal_seed v
  ext v
  constructor
  · intro hv
    refine ⟨rho g⁻¹ v,?_,rho.self_inv_apply g v⟩
    apply (hU _).mp
    intro w hw
    have he := Atlas.G2.Natural.BinaryPointFlag.pairing_invariant g w (rho g⁻¹ v)
    rw [rho.self_inv_apply] at he
    exact he.symm.trans (hv (rho g w) ⟨w,hw,rfl⟩)
  · rintro ⟨v,hv,rfl⟩ w ⟨w,hw,rfl⟩
    rw [Atlas.G2.Natural.BinaryPointFlag.pairing_invariant]
    exact (hU v).mpr hv w hw

/-- The pointwise stabilizer of an offender's full fixed space is that offender. -/
theorem offender_pointwise_fixed (A : Subgroup (Atlas.G2.Model (ZMod 2)))
    (hA : IsOffender rho A) (x : Atlas.G2.Model (ZMod 2))
    (hx : ∀ v ∈ fixedSpace rho A, rho x v = v) : x ∈ A := by
  obtain ⟨g,rfl⟩ := Atlas.G2.NaturalOffenders.offender_conjugate_elementary
    (F := ZMod 2) (n := 1) (by norm_num) (by decide) A hA
  rw [fixed_conjugate,Atlas.G2.Natural.BinaryIsotropicThree.fixed_elementary_eq_target] at hx
  have hg : g⁻¹*x*g ∈ Atlas.G2.EvenTwoRank.elementary (ZMod 2) := by
    apply (Atlas.G2.Natural.BinaryIsotropicThree.pointwise_target_eq_elementary _).mp
    intro v hv
    have hh := hx (rho g v) ⟨v,hv,rfl⟩
    simp only [map_mul,Module.End.mul_apply,hh,rho.inv_self_apply]
  refine ⟨g⁻¹*x*g,hg,?_⟩
  simp [MulAut.conj_apply,mul_assoc]


end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.Comparison.CriticalImage
