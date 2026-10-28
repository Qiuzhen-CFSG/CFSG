module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.GroupTheory.PResidual.TwoKernelComparison

/-!
# Residuals in local overgroups of the actual binary derived G₂ group

Full-group conjugation identifies Aut(G₂(2)′), so its outer group has order
at most two. Together with the intrinsic elementary nine this gives
three-prime index for a normal C-component in a group of three-rank at
most two. Every proper Sylow two-overgroup has order prime to seven,
by the native seven-overgroup theorem, hence has only primes two and
three. Its two-residual is therefore its prime-to-three residual.

These are the precise intrinsic inputs to the G₂ row of Aschbacher–Smith
3.3.25(2), printed p.599, and the rank argument in A.3.18, pp.51–52.
The octonion carrier retains the licensed ATLAS attribution of its imports;
see LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryLocalResidual
open BinaryParabolicPair LieAutomorphismExtensions
local notation "D" => commutator (Model (ZMod 2))

theorem center_eq_bot : center D = ⊥ := by
  apply bot_unique
  intro z hz
  apply mem_bot.mpr
  apply Subtype.ext
  apply binaryConjugation_injective
  change binaryConjugation z.val = binaryConjugation 1
  rw [binaryConjugation_inner, map_one]
  apply MulEquiv.ext
  intro x
  change z * x * z⁻¹ = x
  rw [← mem_center_iff.mp hz x, mul_inv_cancel_right]

theorem outer_card_dvd_two : Nat.card (MulAut.Outer D) ∣ 2 := by
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup D)).comp binaryConjugation
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp binaryConjugation_surjective
  have hd : D ≤ f.ker := by
    intro x hx
    change QuotientGroup.mk' (MulAut.innerSubgroup D) (binaryConjugation x) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    change binaryConjugation x ∈ (MulAut.conj : D →* MulAut D).range
    exact ⟨⟨x,hx⟩, (binaryConjugation_inner (⟨x,hx⟩ : D)).symm⟩
  have hi : (commutator (Model (ZMod 2))).index = 2 := by
    have hh := (commutator (Model (ZMod 2))).card_mul_index
    rw [card_binaryDerived,card_binaryFull] at hh
    omega
  have hc : f.ker.index = Nat.card (MulAut.Outer D) := by
    rw [index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  exact hc ▸ (index_dvd_of_le hd).trans (dvd_of_eq hi)

theorem index_coprime_three {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* D) (hr : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 L.index := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro z hz
    have he := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center D at he
    rw [center_eq_bot,mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hrL : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e]
    exact EvenThreeRank.two_le_primeRank_derived
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact (show Nat.Coprime 3 2 by decide).coprime_dvd_right outer_card_dvd_two
  exact cComponent_index_coprime_three_of_quotient L hL hz hrL hr ho

private theorem whole_residuals : pResidual 2 D = primeToResidual 3 D := by
  let : IsSimpleGroup D := isSimple_commutator_binary
  have he : primeToResidual 3 D = ⊤ := by
    rcases (inferInstance : (primeToResidual 3 D).Normal).eq_bot_or_eq_top with hz | ht
    · have hc := primeToResidual_index_coprime (G := D) 3
      rw [hz,index_bot,card_binaryDerived] at hc
      norm_num at hc
    · exact ht
  apply le_antisymm ?_ primeToResidual_three_le_twoResidual
  rw [he]
  exact le_top

private theorem standard_residuals (H : Subgroup D)
    (hSH : (derivedSylow : Subgroup D) ≤ H) :
    pResidual 2 H = primeToResidual 3 H := by
  by_cases hH : H = ⊤
  · subst H
    have he := congrArg (fun U : Subgroup D =>
      U.map (topEquiv.symm : D ≃* (⊤ : Subgroup D)).toMonoidHom) whole_residuals
    rwa [map_pResidual, map_primeToResidual] at he
  · have h7 : ¬ 7 ∣ Nat.card H := fun hd =>
      hH (SevenSylowOvergroups.eq_top_of_seven_dvd H hSH hd)
    apply twoResidual_eq_primeToResidual_three
    apply (IsPiGroup_iff twoThreePrimes H).mpr
    intro p hp
    have hd : p.val ∣ 6048 := hp.trans (card_binaryDerived ▸ H.card_subgroup_dvd_card)
    have hpc : p.val = 2 ∨ p.val = 3 ∨ p.val = 7 := by
      have hd' : p.val ∣ 2^5 * 3^3 * 7 := hd
      rcases p.property.dvd_mul.mp hd' with h23 | h7
      · rcases p.property.dvd_mul.mp h23 with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
            (p.property.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_three).mp
            (p.property.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq p.property (by decide)).mp h7))
    rcases hpc with h2 | h3 | hp7
    · exact Or.inl h2
    · exact Or.inr h3
    · exact (h7 (hp7 ▸ hp)).elim

theorem sylow_overgroup_residuals (S : Sylow 2 D) (H : Subgroup D)
    (hSH : (S : Subgroup D) ≤ H) : pResidual 2 H = primeToResidual 3 H := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D S derivedSylow
  let e := MulAut.conj g
  have hs : (S : Subgroup D).map e.toMonoidHom = derivedSylow :=
    congrArg (fun P : Sylow 2 D => (P : Subgroup D)) hg
  have hh := standard_residuals (H.map e.toMonoidHom) (hs ▸ map_mono hSH)
  let b : H ≃* H.map e.toMonoidHom := H.equivMapOfInjective e.toMonoidHom e.injective
  have h := congrArg (fun U : Subgroup (H.map e.toMonoidHom) => U.map b.symm.toMonoidHom) hh
  rwa [map_pResidual, map_primeToResidual] at h
end Atlas.G2.BinaryLocalResidual
