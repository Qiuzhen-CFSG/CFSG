module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement.Core
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# The odd prime in the lambda-core normalizer

The action on the elementary center E has kernel W of order 32, and
Aut(E) has order 168. Hence only 2, 3 and 7 can divide the normalizer order.
A seven-element would fix both 1 and pi*mu in E. Orbit counting on eight
points forces it to fix all of E, putting it in the two-group W. Thus
seven is excluded, and any failure to be a two-group supplies an element
of order three by Cauchy's theorem.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, printed p.226.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem center_action_kernel_card :
    Nat.card (lambdaCenter D e).normalizerMonoidHom.ker = 32 := by
  have hWN : lambdaCore D e ≤ normalizer (lambdaCenter D e : Set G) := by
    rw [← lambdaCenter_centralizer D e]
    exact centralizer_le_normalizer _
  rw [normalizerMonoidHom_ker, lambdaCenter_centralizer,
    Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv, lambdaCore_card]

private theorem center_normalizer_card_dvd :
    Nat.card (normalizer (lambdaCenter D e : Set G)) ∣ 5376 := by
  let E := lambdaCenter D e
  let r := E.normalizerMonoidHom
  have hratio : 32 * Nat.card r.range = Nat.card (normalizer (E : Set G)) := by
    have hh := r.ker.card_mul_index
    rw [index_ker, center_action_kernel_card] at hh
    exact hh
  let := lambdaCenter_elementary D e
  have hd : Nat.card r.range ∣ 168 := by
    rw [← card_mulAut_of_elementary_eight (lambdaCenter D e) (lambdaCenter_card D e)]
    exact r.range.card_subgroup_dvd_card
  rw [← hratio]
  exact Nat.mul_dvd_mul_left 32 hd

private theorem center_normalizer_no_seven :
    ¬ 7 ∣ Nat.card (normalizer (lambdaCenter D e : Set G)) := by
  intro hseven
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let E := lambdaCenter D e
  let N := normalizer (E : Set G)
  let r := E.normalizerMonoidHom
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 hseven
  let R := zpowers x
  have hR : IsPGroup 7 R := IsPGroup.of_card
    ((Nat.card_zpowers x).trans (hx.trans (pow_one 7).symm))
  let c : E := ⟨D.a10ModelEmbedding e (Coordinates.pi * mu),
    mem_map_of_mem _ (lambdaModelCenter.mul_mem lambdaModelCenter_pi lambdaModelCenter_mu)⟩
  have hcne : c ≠ 1 := by
    intro h
    apply (show Coordinates.pi * mu ≠ (1 : H) by decide +kernel)
    apply D.a10ModelEmbedding_injective e
    have hv : D.a10ModelEmbedding e (Coordinates.pi * mu) = (1 : G) :=
      congrArg Subtype.val h
    simpa only [map_one] using hv
  have h1 : (1 : E) ∈ MulAction.fixedPoints R E := by
    intro g
    apply Subtype.ext
    change ((g : N) : G) * 1 * ((g : N) : G)⁻¹ = 1
    simp
  have hc : c ∈ MulAction.fixedPoints R E := by
    intro g
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp
      (lambdaCore_normalizer_le_centralizer D e
        ((lambdaCenter_normalizer_eq D e).le (g : N).property)))
  let F := MulAction.fixedPoints R E
  have hnontriv : Nontrivial F := ⟨⟨⟨c, hc⟩, ⟨1, h1⟩,
    fun he => hcne (congrArg Subtype.val he)⟩⟩
  let := hnontriv
  have hlo : 1 < Nat.card F := Finite.one_lt_card
  have hhi : Nat.card F ≤ 8 := by
    have hh := Nat.card_le_card_of_injective (Subtype.val : F → E) Subtype.val_injective
    exact hh.trans (lambdaCenter_card D e).le
  have hmod := hR.card_modEq_card_fixedPoints E
  change Nat.card E % 7 = Nat.card F % 7 at hmod
  rw [lambdaCenter_card] at hmod
  have hF : Nat.card F = 8 := by omega
  have hsurj : Function.Surjective (Subtype.val : F → E) :=
    (Subtype.val_injective.bijective_of_nat_card_le (by
      rw [hF, lambdaCenter_card])).surjective
  have hfix (t : E) : x • t = t := by
    obtain ⟨y, rfl⟩ := hsurj t
    exact y.property ⟨x, mem_zpowers x⟩
  have hxker : x ∈ r.ker := by
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro t
    exact hfix t
  have hd := r.ker.orderOf_dvd_natCard hxker
  rw [hx, center_action_kernel_card] at hd
  norm_num at hd

/-- If the W-normalizer is not a two-group, it contains an element of order three. -/
public theorem lambdaCore_three_of_not_two
    (h : ¬ IsPGroup 2 (normalizer (lambdaCore D e : Set G))) :
    ∃ x : normalizer (lambdaCore D e : Set G), orderOf x = 3 := by
  rw [← lambdaCenter_normalizer_eq] at h ⊢
  apply exists_prime_orderOf_dvd_card'
  by_contra hthree
  apply h
  rw [isPGroup_iff_primeFactors_card_subset (by decide)]
  intro q hq
  have hq' := Nat.primeFactors_mono (center_normalizer_card_dvd D e) (by decide) hq
  rw [show Nat.primeFactors 5376 = {2, 3, 7} by decide +kernel] at hq'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
  rcases hq' with rfl | rfl | rfl
  · simp only [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, dvd_rfl, by decide⟩
  · exact (hthree (Nat.dvd_of_mem_primeFactors hq)).elim
  · exact (center_normalizer_no_seven D e (Nat.dvd_of_mem_primeFactors hq)).elim

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
