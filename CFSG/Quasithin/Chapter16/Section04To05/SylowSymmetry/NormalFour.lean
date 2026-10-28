module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.NormalFour.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.NormalFour.Outer

/-!
# The order argument in the relative Sylow upgrade

For the genuine intersection setup and a conjugate in Delta-zero, this
module constructs the actual inner projection and proves its order saturation.
The chosen-Sylow omega containment and multiplication-coordinate containment
are discharged in `Preparation`. The elementary-image contradiction and
nonsplit lift are proved in `Elementary`. The actual action on `Out(L)` in
`Outer` then gives the relative index bound from the intrinsic cover input.

The normal-four construction, TI geometry and final centrality deduction
remain separate obligations. Thus the exported construction is a preparatory
result for 16.4.10, not yet the source Sylow conclusion. The explicit earlier
inputs are 16.4.2(1), I.7.7(4),(6), and `CoverInput`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 16.4.10, printed pp.1192–1193.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

omit [Finite G] in
/-- The intrinsic cover center is the actual central overlap in the ambient group. -/
theorem SylowSymmetry.NormalFour.CoverInput.center_two_ambient
    (d : SylowSymmetry.NormalFour.CoverInput L) :
    IsPGroup 2 ↥(L ⊓ centralizer (L : Set G)) := by
  have he : (center L).map L.subtype = L ⊓ centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨l.property, mem_centralizer_iff.mpr ?_⟩
      intro y hy
      exact congrArg L.subtype (mem_center_iff.mp hl ⟨y, hy⟩)
    · intro hx
      refine ⟨⟨x, hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx.2 y y.property)
  exact he ▸ d.center_two.map L.subtype

/-- The contrary branch through the exact order saturation. The normalizer
identity and isomorphism are 16.4.2(1), while abelianness and relative normality
are I.7.7(4),(6). The cover input concerns the actual center and outer group. -/
theorem IntersectionSetup.exists_saturated_projection
    (h : IntersectionSetup T z L g R)
    (hd : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (hn : commutingSylow T L ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    (hp : commutingSylow T L ⊓ centralizer (R : Set G) < commutingSylow T L)
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    [IsMulCommutative R]
    (hSn : ((commutingSylow T L ⊓ centralizer (R : Set G)).subgroupOf
      (commutingSylow T L)).Normal)
    (d : SylowSymmetry.NormalFour.CoverInput L) :
    Nonempty (SylowSymmetry.NormalFour.SaturatedProjection (commutingSylow T L) L
      (innerPart L R) (commutingSylow T L ⊓ centralizer (R : Set G))) := by
  let C := commutingSylow T L
  let S := C ⊓ centralizer (R : Set G)
  let A := innerPart L R
  have hA : A ≤ R := inf_le_left
  have hOA : omegaOneAmbient R ≤ A :=
    le_inf (omegaOneAmbient_le R) (h.omega_le_of_mem_deltaZero hd)
  have hconf := h.projection_configuration_of_deltaZero hd hn hp d.center_two_ambient
  let : (L.subgroupOf S).Normal := hconf.overlap_normal
  obtain ⟨π⟩ := hconf.exists_projection
  have hCp : IsPGroup 2 C := T.isPGroup'.to_le inf_le_left
  let : IsMulCommutative A := IsMulCommutative.of_comm (fun a b =>
    Subtype.ext (setLike_mul_comm (s := R) (hA a.property) (hA b.property)))
  let : IsMulCommutative S := IsMulCommutative.of_comm (fun a b =>
    e.symm.injective (by simp only [map_mul, mul_comm]))
  let : IsElementaryAbelian 2 (omega₁ A (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hcard := SylowSymmetry.omega_card_eq_of_inner hA hOA e
  have hlift := π.exists_nonsplit_lift hconf hCp hSn (omega₁ A (p := 2)) hcard
  have hindex := h.innerPart_relIndex_le_two (d.outer_bound_of_nonsplit hlift)
  obtain ⟨hZ, hS, hfull⟩ := π.saturation_of_inner hconf hCp hSn hA hOA e hindex
  exact ⟨⟨hconf, π, hCp, inferInstance, hSn, hZ, hS, hfull⟩⟩

end CFSG.Quasithin.Chapter16.Intersections
