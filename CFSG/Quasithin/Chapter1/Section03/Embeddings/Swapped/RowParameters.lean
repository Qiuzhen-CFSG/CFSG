module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BenderNormalizers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.JankoLocal
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# Parameter restrictions for the Suzuki and Janko exchanged rows

A solvable product of an odd subgroup and a Sylow two-subgroup in two equal
simple factors places the odd subgroup in the Sylow normalizer. A nontrivial
coordinate projection and the Suzuki Borel order give the field congruence.
For Janko's group, the automorphism order of the elementary Sylow two-subgroup
forces either p = 7 or centralization; the latter contradicts the checked
prime-normalizer bounds. The arguments use actual model equivalences.

Source: Aschbacher--Smith, 13.1.12(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem nontrivial_projection (A : Subgroup (Q × Q)) (hne : A ≠ ⊥) :
    ∃ f : (Q × Q) →* Q, Function.Surjective f ∧ A.map f ≠ ⊥ := by
  by_cases hf : A.map (MonoidHom.fst Q Q) = ⊥
  · refine ⟨MonoidHom.snd Q Q, (fun q => ⟨(1,q),rfl⟩), ?_⟩
    intro hs
    apply hne
    apply bot_unique
    intro x hx
    have h1 := hf ▸ mem_map_of_mem (MonoidHom.fst Q Q) hx
    have h2 := hs ▸ mem_map_of_mem (MonoidHom.snd Q Q) hx
    exact Prod.ext (mem_bot.mp h1) (mem_bot.mp h2)
  · exact ⟨MonoidHom.fst Q Q, (fun q => ⟨(q,1),rfl⟩),hf⟩

open BenderSuzuki.MatrixGroups in
private theorem suzuki_model_sylow_normalizer_card {m : ℕ} (hm : 1 ≤ m)
    (e : Q ≃* SuzukiMatrixGroup m) (S : Sylow 2 Q) :
    Nat.card (normalizer (S : Set Q)) =
      (2 ^ (2*m+1)) ^ 2 * (2 ^ (2*m+1) - 1) := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨R,hR⟩ := suzukiRootSubgroup_isSylow m (by omega)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) T R
  let c := e.trans (MulAut.conj g)
  have hST : (S : Subgroup Q).map c.toMonoidHom = SuzukiRootSubgroup m := by
    change (S : Subgroup Q).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map]
    exact (congrArg Sylow.toSubgroup hg).trans hR
  have hN : (normalizer (S : Set Q)).map c.toMonoidHom = SuzukiBorelSubgroup m := by
    change (normalizer ((S : Subgroup Q) : Set Q)).map c.toMonoidHom = _
    rw [map_normalizer_eq_of_bijective _ c.bijective,hST]
    exact CFSG.Quasithin.ChapterF.Source.suzuki_root_normalizer_eq_borel m
  rw [← card_map_of_injective (K := normalizer (S : Set Q)) (f := c.toMonoidHom) c.injective,hN]
  exact suzukiBorelSubgroup_card m (by omega)

theorem suzuki_prod_congruence {m p : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (e : Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (hp : Odd p)
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    (hA : IsPGroup p A) (hne : A ≠ ⊥)
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    Nat.ModEq p (2 ^ (2*m+1)) 1 := by
  have hn := suzuki_model_prod_le_normalizer hm e S A
  obtain ⟨f,hf,hne⟩ := nontrivial_projection A hne
  let T := S.mapSurjective hf
  have hAN : A.map f ≤ normalizer (T : Set Q) :=
    (map_mono hn).trans (le_normalizer_map f)
  have hd : p ∣ (2 ^ (2*m+1)) ^ 2 * (2 ^ (2*m+1)-1) := by
    rw [← suzuki_model_sylow_normalizer_card hm e T]
    exact ((hA.map f).card_eq_or_dvd.resolve_left
      (fun h => hne (card_eq_one.mp h))).trans (card_dvd_of_le hAN)
  have hnot : ¬ p ∣ (2 ^ (2*m+1)) ^ 2 := by
    intro hd
    have ht : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hp.coprime_two_right ht
  exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr
    (((Fact.out : p.Prime).dvd_mul.mp hd).resolve_left hnot)).symm

private theorem janko_normalizer_prime {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (S : Sylow 2 Janko1.Model) (A : Subgroup Janko1.Model)
    (hA : IsPGroup p A) (hne : A ≠ ⊥)
    (hn : A ≤ normalizer (S : Set Janko1.Model)) : p = 7 := by
  by_contra h7
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let f : A →* MulAut S := (S : Subgroup Janko1.Model).normalizerMonoidHom.comp (inclusion hn)
  let := Janko1.SylowTwo.elementary S
  have hf : f.range = ⊥ := by
    rcases (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective).card_eq_or_dvd with h | h
    · exact card_eq_one.mp h
    · have hd : p ∣ 168 := h.trans (card_mulAut_of_elementary_eight S (Janko1.SylowTwo.card S) ▸
        f.range.card_subgroup_dvd_card)
      have hf168 : 168 = 2 * 2 * 2 * 3 * 7 := by decide
      rw [hf168] at hd
      simp only [(Fact.out : p.Prime).dvd_mul,
        Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide : Nat.Prime 2),
        Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide : Nat.Prime 3),
        Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide : Nat.Prime 7)] at hd
      omega
  have hc : A ≤ centralizer (S : Set Janko1.Model) := by
    intro a ha
    have hz : f ⟨a,ha⟩ = 1 := mem_bot.mp (hf ▸ (show f ⟨a,ha⟩ ∈ f.range from ⟨⟨a,ha⟩,rfl⟩))
    have hk : (⟨a,hn ha⟩ : normalizer (S : Set Janko1.Model)) ∈
        (S : Subgroup Janko1.Model).normalizerMonoidHom.ker := hz
    rwa [normalizerMonoidHom_ker] at hk
  have hd : p ∣ Nat.card A := hA.card_eq_or_dvd.resolve_left (fun h => hne (card_eq_one.mp h))
  obtain ⟨B,hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 1) (by simpa using hd)
  let R := B.map A.subtype
  have hR : Nat.card R = p := by rw [card_map_of_injective A.subtype_injective,hB,pow_one]
  have hSN : (S : Subgroup Janko1.Model) ≤ normalizer (R : Set Janko1.Model) :=
    ((le_centralizer_iff.mp hc).trans (centralizer_le (map_subtype_le B))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hbound : Janko1.LocalStructure.PrimeNormalizerBound p :=
    Janko1.LocalStructure.primeNormalizerBound_of_cases
      Janko1.LocalStructure.primeNormalizerBound_three
      Janko1.LocalStructure.primeNormalizerBound_five
      Janko1.LocalStructure.primeNormalizerBound_seven
      Janko1.LocalStructure.primeNormalizerBound_eleven
      Janko1.LocalStructure.primeNormalizerBound_nineteen (Fact.out : p.Prime) ho
  exact hbound R hR (Janko1.SylowTwo.card S ▸ card_dvd_of_le hSN)

theorem janko_prod_prime {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (e : Q ≃* Janko1.Model) (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    (hA : IsPGroup p A) (hne : A ≠ ⊥)
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] : p = 7 := by
  have hn := janko_one_model_prod_le_normalizer e S A
  obtain ⟨f,hf,hne⟩ := nontrivial_projection A hne
  let T := (S.mapSurjective hf).mapSurjective (f := e.toMonoidHom) e.surjective
  apply janko_normalizer_prime hp T ((A.map f).map e.toMonoidHom) ((hA.map _).map _) ?_ ?_
  · intro hb
    exact hne (map_injective e.injective (hb.trans (Subgroup.map_bot _).symm))
  · exact (Subgroup.map_mono (f := e.toMonoidHom) ((map_mono hn).trans (le_normalizer_map f))).trans
      (le_normalizer_map e.toMonoidHom)
end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
