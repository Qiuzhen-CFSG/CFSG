module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Correspondence
public import Theory.SpecificGroups.SymmetricFive.SquareNormalizer

/-!
# Membership in the original quotient-labeled parabolics

Each canonical parabolic has image the normalizer of its quotient pentagon
and has index two in its product with Q. Thus arbitrary order-five lifts of
the pentagon belong to this parabolic. For a square u=t² whose original
quotient root has order four, u belongs precisely when its quotient image
normalizes the pentagon. These statements keep the original maps and lifts.
Source: the two-member E(z) family in J.4.7, printed p.443.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers.Choices
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)

private theorem map_conjugate {K L : Type*} [Group K] [Group L]
    (f : K →* L) (A : Subgroup K) (h : K) :
    (A.conjBy h).map f = (A.map f).conjBy (f h) := by
  unfold conjBy
  rw [map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

/-- Every canonical original parabolic stays in the original H. -/
theorem parabolicFor_le_H (P : Sylow 5 S5) : parabolicFor p B5 P ≤ d.toTypeRuSetup.H :=
  conj_smul_le_of_le (p.F₁_le_H B5) (pentagonConjugator B5 P)

include s hi in
/-- The literal quotient image is exactly the chosen pentagon's normalizer. -/
theorem parabolicFor_image (P : Sylow 5 S5) :
    ((parabolicFor p B5 P).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap =
      normalizer ((P : Subgroup S5) : Set S5) := by
  let h := pentagonConjugator B5 P
  have he : ((p.F₁ B5).conjBy (h : G)).subgroupOf d.toTypeRuSetup.H =
      ((p.F₁ B5).subgroupOf d.toTypeRuSetup.H).conjBy h :=
    (conj_smul_subgroupOf (p.F₁_le_H B5) h).symm
  change (((p.F₁ B5).conjBy (h : G)).subgroupOf d.toTypeRuSetup.H).map _ = _
  rw [he, map_conjugate, s.F₁_image p B5 hi]
  change (normalizer ((basePentagon B5 : Subgroup S5) : Set S5)).map (MulAut.conj (d.ru2.quotientMap h)).toMonoidHom = _
  rw [map_equiv_normalizer_eq]
  have hp := congrArg Sylow.toSubgroup (pentagonConjugator_spec B5 P)
  exact congrArg (fun A : Subgroup S5 => normalizer (A : Set S5)) hp

include s hi in
/-- The product with the original Q is the full inverse image of this normalizer. -/
theorem parabolicFor_product_preimage (P : Sylow 5 S5) :
    (normalizer ((P : Subgroup S5) : Set S5)).comap d.ru2.quotientMap =
      (parabolicFor p B5 P ⊔ d.toTypeRuSetup.Q).subgroupOf d.toTypeRuSetup.H := by
  rw [← parabolicFor_image p s B5 hi P, comap_map_eq, d.ru2.quotient_kernel,
    subgroupOf_sup (parabolicFor_le_H p B5 P) (pCoreIn_le 2 _)]

include s hi in
/-- The original index two survives all H-conjugations. -/
theorem parabolicFor_relIndex (P : Sylow 5 S5) :
    (parabolicFor p B5 P).relIndex (parabolicFor p B5 P ⊔ d.toTypeRuSetup.Q) = 2 := by
  let h := pentagonConjugator B5 P
  have hQ : d.toTypeRuSetup.Q.conjBy (h : G) = d.toTypeRuSetup.Q :=
    mem_normalizer_iff_map_conj_eq.mp (d.ru2.six.normalized h.property)
  have hp : parabolicFor p B5 P ⊔ d.toTypeRuSetup.Q =
      (p.F₁ B5 ⊔ d.toTypeRuSetup.Q).map (MulAut.conj (h : G)).toMonoidHom := by
    rw [Subgroup.map_sup, show d.toTypeRuSetup.Q.map (MulAut.conj (h : G)).toMonoidHom =
      d.toTypeRuSetup.Q from hQ]
    rfl
  rw [hp]
  change ((p.F₁ B5).map (MulAut.conj (h : G)).toMonoidHom).relIndex _ = _
  rw [relIndex_map_map_of_injective _ _ (MulAut.conj (h : G)).injective]
  exact s.F₁_relIndex_sup_Q p B5 hi

include s hi in
/-- Squaring in the product lands in its original conjugate endpoint. -/
theorem square_mem_parabolicFor (P : Sylow 5 S5) {x : G}
    (hx : x ∈ parabolicFor p B5 P ⊔ d.toTypeRuSetup.Q) : x^2 ∈ parabolicFor p B5 P := by
  let E := parabolicFor p B5 P
  let : (E.subgroupOf (E ⊔ d.toTypeRuSetup.Q)).Normal :=
    normal_of_index_eq_two (parabolicFor_relIndex p s B5 hi P)
  have hh := (E.subgroupOf (E ⊔ d.toTypeRuSetup.Q)).pow_index_mem ⟨x,hx⟩
  change x ^ E.relIndex (E ⊔ d.toTypeRuSetup.Q) ∈ E at hh
  rwa [parabolicFor_relIndex p s B5 hi P] at hh

include s hi in
/-- Any original five-subgroup with this pentagon image belongs to the
corresponding parabolic, independently of its particular lift. -/
theorem five_le_parabolicFor_of_image (P : Sylow 5 S5) (B : Subgroup G)
    (hB : B ≤ d.toTypeRuSetup.H) (hc : Nat.card B = 5)
    (himage : (B.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap ≤ (P : Subgroup S5)) :
    B ≤ parabolicFor p B5 P := by
  intro b hb
  let bH : d.toTypeRuSetup.H := ⟨b,hB hb⟩
  have him : d.ru2.quotientMap bH ∈ normalizer ((P : Subgroup S5) : Set S5) :=
    (P : Subgroup S5).le_normalizer (himage (mem_map_of_mem _ hb))
  have hpre : b ∈ parabolicFor p B5 P ⊔ d.toTypeRuSetup.Q := by
    have hh : bH ∈ (normalizer ((P : Subgroup S5) : Set S5)).comap d.ru2.quotientMap := him
    rw [parabolicFor_product_preimage p s B5 hi P] at hh
    exact hh
  have hb2 := square_mem_parabolicFor p s B5 hi P hpre
  have hb5 : b^5=1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨b,hb⟩ : B)))
    simpa only [hc,coe_pow,coe_one] using hh
  have hb6 := (parabolicFor p B5 P).pow_mem hb2 3
  have he : (b^2)^3=b := by rw [← pow_mul,show 2*3=5+1 by rfl,pow_succ,hb5,one_mul]
  exact he ▸ hb6

include s hi in
/-- The original square belongs exactly to the parabolic selected by its
quotient pentagon normalization. -/
theorem square_mem_iff (t : d.toTypeRuSetup.H) (ht : orderOf (d.ru2.quotientMap t)=4)
    (P : Sylow 5 S5) :
    (t : G)^2 ∈ parabolicFor p B5 P ↔
      d.ru2.quotientMap (t^2) ∈ normalizer ((P : Subgroup S5) : Set S5) := by
  constructor
  · intro hh
    rw [← parabolicFor_image p s B5 hi P]
    exact mem_map_of_mem _ hh
  · intro hh
    have htN : d.ru2.quotientMap t ∈ normalizer ((P : Subgroup S5) : Set S5) :=
      Theory.SpecificGroups.SymmetricFive.SquareNormalizer.square_normalizer P
        (Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_sylow P)
        _ ht (by simpa only [map_pow] using hh)
    have hpre : (t : G) ∈ parabolicFor p B5 P ⊔ d.toTypeRuSetup.Q := by
      have hh : t ∈ (normalizer ((P : Subgroup S5) : Set S5)).comap d.ru2.quotientMap := htN
      rw [parabolicFor_product_preimage p s B5 hi P] at hh
      exact hh
    exact square_mem_parabolicFor p s B5 hi P hpre

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
