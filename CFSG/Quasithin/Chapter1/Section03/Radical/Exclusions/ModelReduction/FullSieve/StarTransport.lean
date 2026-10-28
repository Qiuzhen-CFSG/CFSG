module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Normalization
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# A central cover from the actual C.2.7 kernel bound

Write Q = K/O₂(K) and K* for the image of K in KR/C_KR(V).
The C.2.7 bound C_KR(V) ≤ O₂(KR)O₂,Z(K) makes its kernel act
trivially on Q: the first factor is an ambient two-core, and the second
induces inner automorphisms from Z(Q). Thus ker(Q → K*) ≤ Z(Q).
Quasisimplicity now forces K* to be nontrivial, without assuming that
nontriviality as part of a model identification.

In the swapped rank-one case Q is simple, so this particular comparison
map is an isomorphism. The model transport below uses that map.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.2.7(1), printed p.145, and proof of 1.3.8, p.514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
variable {G : Type*} [Group G]

/-- The actual image of O₂,Z(K), the preimage of Z(K/O₂(K)), in KR. -/
def coreCenterImage (K R : Subgroup G) : Subgroup (K ⊔ R : Subgroup G) :=
  ((center (XiQuotient K)).comap (QuotientGroup.mk' (pCore 2 K))).map
    (inclusion (show K ≤ K ⊔ R from le_sup_left))

/-- The upper centralizer bound in C.2.7(1). Its lower bound is already
`core_le_starKernel`. This definition alone is not the full C.2.7 conclusion. -/
def StarKernelBound (K R : Subgroup G) : Prop :=
  starKernel K R ≤ pCore 2 (K ⊔ R : Subgroup G) ⊔ coreCenterImage K R

private theorem conj_eq_one_iff_center {Q : Type*} [Group Q] (x : Q) :
    MulAut.conj x = 1 ↔ x ∈ center Q := by
  constructor
  · intro h
    apply mem_center_iff.mpr
    intro y
    have he := DFunLike.congr_fun h y
    change x * y * x⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h
    ext y
    change x * y * x⁻¹ = y
    rw [← mem_center_iff.mp h y, mul_inv_cancel_right]

/-- Both factors in the source bound act trivially on K/O₂(K). -/
theorem starKernel_le_coreActionKernel {K R : Subgroup G}
    (hRK : R ≤ normalizer K) (hb : StarKernelBound K R) :
    starKernel K R ≤ (pCoreJoinAction 2 hRK).ker := by
  apply hb.trans
  refine sup_le (pCore_le_pCoreJoinAction_kernel 2 hRK) ?_
  rintro x ⟨k, hk, rfl⟩
  change pCoreJoinAction 2 hRK (inclusion le_sup_left k) = 1
  rw [pCoreJoinAction_on_component]
  exact (conj_eq_one_iff_center _).mpr hk

/-- The C.2.7 bound makes the actual comparison kernel central. -/
theorem coreToStar_ker_le_center_of_bound {K R : Subgroup G}
    (hRK : R ≤ normalizer K) (hb : StarKernelBound K R) :
    (coreToStar hRK).ker ≤ center (XiQuotient K) := by
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  have hk : inclusion (show K ≤ K ⊔ R from le_sup_left) k ∈ starKernel K R := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val (show coreToStar hRK
      (QuotientGroup.mk' (pCore 2 K) k) = 1 from hx)
  have ha := starKernel_le_coreActionKernel hRK hb hk
  change pCoreJoinAction 2 hRK (inclusion le_sup_left k) = 1 at ha
  rw [pCoreJoinAction_on_component] at ha
  exact (conj_eq_one_iff_center _).mp ha

/-- A quasisimple core quotient cannot have trivial star image under the bound. -/
theorem starImage_ne_bot_of_bound {K R : Subgroup G}
    (hRK : R ≤ normalizer K) (hq : IsQuasisimple (XiQuotient K))
    (hb : StarKernelBound K R) : starImage K R K ≠ ⊥ := by
  let _ := hq
  let _ := hq.simple
  let _ : Nontrivial (XiQuotient K) :=
    (QuotientGroup.mk'_surjective (center (XiQuotient K))).nontrivial
  intro he
  have hz : center (XiQuotient K) = ⊤ := by
    apply top_unique
    intro x _
    apply coreToStar_ker_le_center_of_bound hRK hb
    apply Subtype.ext
    exact mem_bot.mp (he ▸ (coreToStar hRK x).property)
  exact Group.IsPerfect.not_isMulCommutative (XiQuotient K)
    (center_eq_top_iff.mp hz)

/-- The swapped quotient and the star image agree through their actual map. -/
noncomputable def coreStarEquivOfSwapped {K R : Subgroup G} {p : ℕ}
    (hRK : R ≤ normalizer K) (hq : IsQuasisimple (XiQuotient K))
    (hb : StarKernelBound K R) (hm : XiEmbedding.SwappedModel p (XiQuotient K)) :
    XiQuotient K ≃* starImage K R K := by
  let _ := hq
  let _ := swappedModel_simple hq hm
  have hz : center (XiQuotient K) = ⊥ := by
    rcases (inferInstance : (center (XiQuotient K)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative (XiQuotient K)
        (center_eq_top_iff.mp hz)).elim
  exact coreStarEquivOfCenterEqBot hRK hq (starImage_ne_bot_of_bound hRK hq hb) hz

/-- Every even exponent has 2ⁿ ≡ 1 modulo three. This permits reuse of
model comparisons whose rank-one input is stated with parameter three. -/
theorem swappedModel_three {Q : Type*} [Group Q] {p : ℕ}
    (hm : XiEmbedding.SwappedModel p Q) : XiEmbedding.SwappedModel 3 Q := by
  rcases hm with ⟨n, hn, _, hmodel⟩ | hprime
  · refine Or.inl ⟨n, hn, ?_, hmodel⟩
    obtain ⟨m, rfl⟩ := hn
    rw [← two_mul, pow_mul]
    simpa only [one_pow] using (show Nat.ModEq 3 (2 ^ 2) 1 by decide).pow m
  · exact Or.inr hprime

/-- Transport both rank-one alternatives through an actual equivalence. -/
theorem swappedModel_of_mulEquiv {Q D : Type*} [Group Q] [Group D] {p : ℕ}
    (hm : XiEmbedding.SwappedModel p Q) (e : D ≃* Q) :
    XiEmbedding.SwappedModel p D := by
  rcases hm with ⟨n, hn, hc, hmodel⟩ | ⟨q, hq, ho, hmodel⟩
  · exact Or.inl ⟨n, hn, hc, hmodel.of_mulEquiv e⟩
  · exact Or.inr ⟨q, hq, ho, hmodel.of_mulEquiv e⟩

/-- The actual star image has the same swapped rank-one model. -/
theorem swappedModel_star {K R : Subgroup G} {p : ℕ}
    (hRK : R ≤ normalizer K) (hq : IsQuasisimple (XiQuotient K))
    (hb : StarKernelBound K R) (hm : XiEmbedding.SwappedModel p (XiQuotient K)) :
    XiEmbedding.SwappedModel p (starImage K R K) :=
  swappedModel_of_mulEquiv hm (coreStarEquivOfSwapped hRK hq hb hm).symm

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
