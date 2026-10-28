module
public import Theory.GroupTheory.CentralExtensionSwappedRankThree
public import Theory.GroupTheory.CentralExtensionPartialInversion
/-!
# Local rank three from global partial inverters

The three torus directions lie in a quotient two-local subgroup. Their
partial inverters may lie elsewhere in the quotient. Lift the two-local
first, choose lifts of its torus directions there, and use the global
central extension to prove that these lifts commute. Their abelian span
then forces prime rank three in the lifted two-local.

This is the even orthogonal central-cover obstruction in Aschbacher--Smith
A.2.18, printed p.40. No restriction on the central kernel is required.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CentralExtension.InvertedRankThree
open CentralExtension.SwappedRankThree (basis)
variable {p : ℕ} [Fact p.Prime]
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Global partial inverters suffice even when they do not normalize the local subgroup. -/
theorem exists_twoLocal_rank_three (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hp : Odd p)
    (P : Subgroup H) (hP : IsTwoLocal P)
    (e : (Fin 3 → Multiplicative (ZMod p)) →* P) (he : Function.Injective e)
    (hs : ∀ i j : Fin 3, i ≠ j → ∃ r : H,
      r * (e (basis p i) : H) * r⁻¹ = (e (basis p i) : H)⁻¹ ∧
      Commute r (e (basis p j) : H)) :
    ∃ L : Subgroup G, IsTwoLocal L ∧ 3 ≤ primeRank p L := by
  classical
  obtain ⟨L,hL,_,q,hq,hmark⟩ := hP.exists_surjective_of_surjective f hf
  let a : Fin 3 → L := fun i => Classical.choose (hq (e (basis p i)))
  have ha (i : Fin 3) : q (a i) = e (basis p i) := Classical.choose_spec (hq (e (basis p i)))
  have ha' (i : Fin 3) : f (a i) = (e (basis p i) : H) := by
    rw [← hmark,ha]
  have hcomm (i j : Fin 3) : Commute (a i) (a j) := by
    by_cases hij : i = j
    · subst j; exact Commute.refl _
    obtain ⟨r,hr,hrj⟩ := hs i j hij
    apply Commute.of_map L.subtype_injective
    apply CentralExtension.commute_lifts_of_partial_inversion f hf hk
      _ _ r hp.coprime_two_right _ (((Commute.all _ _).map e).map P.subtype)
      hr hrj _ _ (ha' i) (ha' j)
    have hb : basis p i ^ p = 1 := by
      funext k
      change Multiplicative.ofAdd (p • (basis p i k).toAdd) = Multiplicative.ofAdd 0
      exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero p _)
    rw [← map_pow,← map_pow,hb,map_one,map_one]
  exact ⟨L,hL,SwappedRankThree.three_le_primeRank_of_commuting_lifts q e he a ha hcomm⟩

theorem not_quasithin (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hp : Odd p)
    (P : Subgroup H) (hP : IsTwoLocal P)
    (e : (Fin 3 → Multiplicative (ZMod p)) →* P) (he : Function.Injective e)
    (hs : ∀ i j : Fin 3, i ≠ j → ∃ r : H,
      r * (e (basis p i) : H) * r⁻¹ = (e (basis p i) : H)⁻¹ ∧
      Commute r (e (basis p j) : H)) : ¬ IsQuasithin G := by
  intro hG
  obtain ⟨L,hL,hr⟩ := exists_twoLocal_rank_three f hf hk hp P hP e he hs
  have hh := isQuasithin_iff_twoLocal.mp hG L hL p (Fact.out : p.Prime) hp
  omega
end CentralExtension.InvertedRankThree
