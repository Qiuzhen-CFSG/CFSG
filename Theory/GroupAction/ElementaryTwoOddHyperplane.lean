module

public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration
public import Theory.GroupAction.SubgroupConjugation
public import Theory.ElementaryAbelian.Basic

/-!
# Hyperplanes detecting an odd subgroup

Let an elementary abelian two-subgroup V normalize a nonidentity odd subgroup R,
with C_R(V) = 1. If U ≤ V centralizes R, then some hyperplane A of V containing U
has C_R(A) ≠ 1.

Coprime fixed-point generation gives a nonidentity element x of R fixed by a
subgroup Y of V with cyclic quotient. Since V has exponent two, |V : Y| divides
two. Take A = C_V(x): it contains U and Y, and it is proper because C_R(V) = 1.
This construction keeps the prescribed subgroup U in the hyperplane without
assuming that an arbitrary generating hyperplane contains the action kernel.

Source: the generation assertion of Aschbacher–Smith A.1.17, applied in E.6.9(2),
combined manuscript (1 March 2004), printed p.248 (PDF p.259).
-/

namespace Subgroup
open scoped IsMulCommutative

/-- A nontrivial odd subgroup with trivial full fixed subgroup is detected by
an index-two subspace containing any prescribed subspace acting trivially. -/
public theorem exists_hyperplane_containing_of_odd_centralizer
    {G : Type*} [Group G] [Finite G]
    (V R U : Subgroup G) [IsElementaryAbelian 2 V]
    (hVR : V ≤ normalizer (R : Set G)) (hodd : Odd (Nat.card R))
    (hR : R ≠ ⊥) (hUV : U ≤ V) (hRU : R ≤ centralizer (U : Set G))
    (hfix : R ⊓ centralizer (V : Set G) = ⊥) :
    ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ A.relIndex V = 2 ∧
      R ⊓ centralizer (A : Set G) ≠ ⊥ := by
  classical
  let _ : Fact (IsPGroup 2 V) := ⟨IsElementaryAbelian.isPGroup 2 V⟩
  let _ : MulDistribMulAction V R := conjMulDistribMulActionOfLeNormalizer V R hVR
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := R) (A := V) 2 hodd.coprime_two_left
  have hex : ∃ Y : Subgroup V, IsCyclic (V ⧸ Y) ∧ fixedPointSubgroup Y R ≠ ⊥ := by
    by_contra! hn
    have ht : (⊤ : Subgroup R) = ⊥ := by
      rw [← hgen]
      exact le_bot_iff.mp (iSup₂_le fun Y hY => (hn Y hY).le)
    apply hR
    apply le_bot_iff.mp
    intro x hx
    exact congrArg Subtype.val (show (⟨x, hx⟩ : R) = 1 from ht.le (mem_top _))
  obtain ⟨Y, hY, hYfix⟩ := hex
  obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp hYfix
  have hxne : ((x : R) : G) ≠ 1 := fun he => hx (Subtype.ext (Subtype.ext he))
  let A := V ⊓ centralizer ({((x : R) : G)} : Set G)
  have hUA : U ≤ A := le_inf hUV (by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr ((hRU (x : R).property) u hu))
  have hYA : Y.map V.subtype ≤ A := by
    rintro y ⟨y, hy, rfl⟩
    refine ⟨y.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have hf := congrArg Subtype.val (x.property (⟨y, hy⟩ : Y))
    change (y : G) * ((x : R) : G) * (y : G)⁻¹ = ((x : R) : G) at hf
    exact (mul_inv_eq_iff_eq_mul.mp hf)
  have hindex : A.relIndex V ∣ 2 := by
    apply (relIndex_dvd_of_le_left V hYA).trans
    have hdiv : Y.index ∣ 2 := by
      rw [index_eq_card, ← hY.exponent_eq_card]
      exact (Group.exponent_quotient_dvd Y).trans
        (IsElementaryAbelian.exponent_dvd_p 2 V)
    simpa only [relIndex, subgroupOf, comap_map_eq, V.ker_subtype, sup_bot_eq] using hdiv
  have hxA : ((x : R) : G) ∈ R ⊓ centralizer (A : Set G) := by
    refine ⟨(x : R).property, ?_⟩
    intro a ha
    exact (mem_centralizer_singleton_iff.mp ha.2)
  have hAne : A.relIndex V ≠ 1 := by
    intro he
    have hVA := relIndex_eq_one.mp he
    exact hxne (hfix.le ⟨hxA.1, (Subgroup.centralizer_le hVA) hxA.2⟩)
  refine ⟨A, hUA, inf_le_left, (Nat.dvd_prime Nat.prime_two).mp hindex |>.resolve_left hAne, ?_⟩
  intro he
  exact hxne (he.le hxA)

end Subgroup
