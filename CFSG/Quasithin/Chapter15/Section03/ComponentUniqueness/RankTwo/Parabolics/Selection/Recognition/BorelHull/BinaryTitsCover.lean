module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.Cover
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.Stabilizers
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.SelfNormalizing

/-!
# Binary linear and Tits normalizer covers

Over a field of order two every invertible diagonal entry is one, so the
triangular Borel equals the unitriangular Sylow subgroup. The projective
quotient and Sylow conjugacy give self-normalization in the genuine binary
linear models.

For the Tits group, a normalizer of the marked Sylow subgroup fixes its
unique nonidentity central element and normalizes its characteristic second
center. The checked intersection of these two stabilizers is the Sylow
subgroup itself. Sylow conjugacy and the proved Parrott–Atlas equivalence
transfer this calculation to the literal presentation carrier.

The given simplicity and perfectness then make the normalizer of any
nonidentity two-subgroup proper, proving both requested covers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 15.3.41 and
the first paragraph of the final proof of 15.3.35, printed pp.1138–1139;
1.1.5(3)(a), pp.501–502; Theorem C and Remark A.2.4, p.33. The concrete
Tits calculations use Parrott (1972), pp.672,683–684, through the cited
certified model modules.
-/

public section

open Subgroup Matrix
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

private theorem self_normalizing_of_one {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : normalizer (S : Set G) = (S : Subgroup G))
    (P : Sylow 2 G) : normalizer (P : Set G) = (P : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have he : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = (P : Subgroup G) :=
    congrArg (fun T : Sylow 2 G => (T : Subgroup G)) hg
  calc
    normalizer (P : Set G) = (normalizer (S : Set G)).map (MulAut.conj g).toMonoidHom := by
      change normalizer ((P : Subgroup G) : Set G) =
        (normalizer ((S : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom
      rw [map_equiv_normalizer_eq, he]
    _ = (P : Subgroup G) := by rw [hS, he]

private theorem self_normalizing_of_mulEquiv {G H : Type*} [Group G] [Group H]
    [Finite G] (e : G ≃* H)
    (hH : ∀ P : Sylow 2 H, normalizer (P : Set H) = (P : Subgroup H))
    (P : Sylow 2 G) : normalizer (P : Set G) = (P : Subgroup G) := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  change (normalizer ((P : Subgroup G) : Set G)).map e.toMonoidHom = _
  rw [map_equiv_normalizer_eq]
  exact hH (P.mapSurjective (f := e.toMonoidHom) e.surjective)

open Theory.SpecificGroups.LinearSylowNormalizers

private theorem binary_borel_eq_unipotent (n : ℕ) (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : borel n F = unipotent n F := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 2 := by simpa only [Nat.card_eq_fintype_card] using hF
  apply le_antisymm ?_ (unipotent_le_borel n F)
  intro g hg
  rw [mem_unipotent]
  refine ⟨hg, fun i => ?_⟩
  have hb := (mem_borel n F g).mp hg
  have hp : (∏ j, g.val j j) ≠ 0 := by
    rw [← Matrix.det_of_isUpperTriangular hb, g.property]
    exact one_ne_zero
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  simpa [hc] using FiniteField.pow_card_sub_one_eq_one (g.val i i) hi

private theorem binary_self_normalizing (n : ℕ) (hn : 0 < n)
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2)
    (P : Sylow 2 (ProjectiveSpecialLinearGroup (Fin n) F)) :
    normalizer (P : Set (ProjectiveSpecialLinearGroup (Fin n) F)) = (P : Subgroup _) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    simpa only [Nat.card_eq_fintype_card, pow_one] using hF)
  apply Sylow.self_normalizing_of_surjective
    (QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) F)))
    (QuotientGroup.mk'_surjective _) ?_ P
  apply self_normalizing_of_one (standardSylow n F hn)
  rw [normalizer_standardSylow, coe_standardSylow, binary_borel_eq_unipotent n F hF]

open Tits Tits.RelativeParabolicNormalizers

private theorem tits_standard_self_normalizing :
    normalizer (atlas1600SylowTwoSubgroup : Set Atlas1600Group) = atlas1600SylowTwoSubgroup := by
  apply le_antisymm ?_ Subgroup.le_normalizer
  have hfirst : normalizer (atlas1600SylowTwoSubgroup : Set Atlas1600Group) ≤
      ExceptionalParabolics.first := by
    intro g hg
    rw [first_eq_centralizer, mem_centralizer_singleton_iff]
    have h := fixes_r5 (MulAut.conj g) (mem_normalizer_iff_map_conj_eq.mp hg)
    exact mul_inv_eq_iff_eq_mul.mp h
  let : (secondCenter.subgroupOf atlas1600SylowTwoSubgroup).Characteristic :=
    secondCenter_characteristic
  have hsecond := normalizer_le_normalizer_characteristic_image atlas1600SylowTwoSubgroup
    (secondCenter.subgroupOf atlas1600SylowTwoSubgroup)
  rw [map_subgroupOf_eq_of_le secondCenter_le_sylow] at hsecond
  exact (le_inf hfirst hsecond).trans first_inf_normalizer_secondCenter.le

variable {K : Type*} [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]

/-- The genuine binary linear models have simultaneous normalizer coverage. -/
theorem binary_twoSubgroupNormalizerCover (hK : SmallBinaryModel K) :
    TwoSubgroupNormalizerCover K := by
  have hmodel {n : ℕ} (hn : 0 < n) (h : ClassicalGroup.IsPSL K n 2) :
      TwoSubgroupNormalizerCover K := by
    obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := h
    let : Field F := hfield
    let : Finite F := hfinite
    exact twoSubgroupNormalizerCover_of_self_normalizing
      (self_normalizing_of_mulEquiv e (binary_self_normalizing n hn F hcard))
  rcases hK with h | h
  · exact hmodel (by decide : 0 < 4) h
  · exact hmodel (by decide : 0 < 5) h

/-- The literal Parrott Tits model has simultaneous normalizer coverage. -/
theorem tits_twoSubgroupNormalizerCover (hK : Nonempty (K ≃* Tits.ParrottGroup)) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨e⟩ := hK
  apply twoSubgroupNormalizerCover_of_self_normalizing
  apply self_normalizing_of_mulEquiv (e.trans Tits.parrottFiniteImageEquiv)
  apply self_normalizing_of_one atlas1600SylowTwo
  change normalizer ((atlas1600SylowTwo : Subgroup Atlas1600Group) : Set Atlas1600Group) =
    (atlas1600SylowTwo : Subgroup Atlas1600Group)
  rw [atlas1600SylowTwo_coe]
  exact tits_standard_self_normalizing

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
