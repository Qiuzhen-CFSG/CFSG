module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Prepared
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.CentralizerPrimeKernel
/-!
# Excluding a single symmetric-three offender actor

A normal S₃ subgroup with a two-group quotient in a two-reduced group is the
whole group. Its centralizer is a two-group because S₃ has trivial center;
thus the centralizer is trivial, and every automorphism of S₃ is inner.
But a group of order six has no Goldschmidt triple: each local S₃ quotient
would force its generator to be the whole group, making the common Sylow
subgroup the whole group as well.

Applied to the actual offender subgroup this excludes B.5.6(2), without
assuming that subgroup equals the ambient quotient. An FF witness separately
excludes the trivial actor. All four other source branches and their complete
module data remain explicit in `RemainingFFAlternative`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.5.6, p.105; F.6.1, p.304; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory.NormalSymmetricThreePairRank
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u v
variable {D : Type u} [Group D] [Finite D]

omit [Finite D] in
private theorem normal_symmetricThree_eq_top (N : Subgroup D) [N.Normal]
    (e : N ≃* Equiv.Perm (Fin 3)) (hD : pCore 2 D = ⊥)
    (hq : IsPGroup 2 (D ⧸ N)) : N = ⊤ := by
  have hz (z : center N) : z = 1 := by
    apply Subtype.ext
    apply e.injective
    change e z.val = e 1
    rw [map_one]
    apply symmetricThree_center_trivial
    intro y
    have he := congrArg e (mem_center_iff.mp z.property (e.symm y))
    simpa only [map_mul, e.apply_symm_apply] using he
  have hpz : IsPGroup 2 (center N) := fun z => ⟨0, by simp [hz z]⟩
  have hpc := isPGroup_centralizer_of_quotient N hq hpz
  have hc : centralizer (N : Set D) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hD]
    exact le_sSup ⟨inferInstance, hpc⟩
  apply top_unique
  intro g _
  let α : MulAut (Equiv.Perm (Fin 3)) := e.symm.trans ((MulAut.conjNormal g).trans e)
  obtain ⟨k, hk⟩ := symmetricThree_aut_inner α
  let n : N := e.symm k
  have he (x : N) : g * x * g⁻¹ = ((n * x * n⁻¹ : N) : D) := by
    change ((MulAut.conjNormal g x : N) : D) = _
    apply congrArg (fun z : N => (z : D))
    apply e.injective
    have hh := DFunLike.congr_fun hk (e x)
    simpa [α, n, MulAut.conj_apply] using hh
  have hn : (n : D)⁻¹ * g ∈ centralizer (N : Set D) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg (fun a : D => (n : D)⁻¹ * a * g) (he ⟨x, hx⟩)
    simpa [mul_assoc] using hh.symm
  rw [hc, mem_bot] at hn
  have hg : g = n := by simpa using (inv_mul_eq_one.mp hn).symm
  exact hg ▸ n.property

private theorem no_goldschmidt_card_six (G₁ G₂ : Subgroup D)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂) (hc : Nat.card D = 6) : False := by
  have step (A : Subgroup D)
      (h : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))) : A = ⊤ := by
    obtain ⟨e⟩ := h
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Nat.card_le_card_of_injective A.subtype A.subtype_injective)
    have hle := Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 A))
      (QuotientGroup.mk'_surjective _)
    rw [Nat.card_congr e.toEquiv] at hle
    simpa [hc, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hle
  have h₁ := step G₁ triple.quotient_left
  have h₂ := step G₂ triple.quotient_right
  obtain ⟨S, hs⟩ := triple.intersection_sylow
  have ht : (S : Subgroup D) = ⊤ := by simpa [h₁, h₂] using hs.symm
  have hp := S.isPGroup'
  rw [ht] at hp
  have hpd := hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D)
  obtain ⟨k, hk⟩ := hpd.exists_card_eq
  have hd : 3 ∣ 2 ^ k := by rw [← hk, hc]; decide
  have := (show Nat.Prime 3 by decide).dvd_of_dvd_pow hd
  norm_num at this

/-- A genuine Goldschmidt triple rules out a normal S₃ offender actor with
2-group quotient: completeness of S₃ and the trivial ambient two-core would
force the entire ambient group to have order six. -/
theorem ClassifiedAction.not_symmetricThree {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂) :
    ¬ Nonempty (offenderSubgroup ρ ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨e⟩
  let := offenderSubgroup_normal ρ
  have ht := normal_symmetricThree_eq_top (offenderSubgroup ρ) e h.twoCore h.quotient_twoGroup
  let a : D ≃* Equiv.Perm (Fin 3) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr ht.symm).trans e)
  apply no_goldschmidt_card_six G₁ G₂ h.triple
  rw [Nat.card_congr a.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The four FF branches still requiring comparison, with all actual source
module data retained; the trivial and S₃ actors have been excluded. -/
def RemainingFFAlternative {A : Type u} [Group A]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) : Prop :=
  (Theory.GroupTheory.IsQuasisimple (Theory.GroupTheory.generalizedFitting A) ∧
    Nonempty (FFAlternatives.QuasisimpleSourceConclusion ρ
      (Theory.GroupTheory.generalizedFitting A))) ∨
  Nonempty (FFAlternatives.SourceTwoFactorCase ρ) ∨
  Nonempty (FFAlternatives.OuterSixThreeCase ρ) ∨
  Nonempty (FFAlternatives.HyperplaneCase ρ)

/-- Exclude the two small degenerate actors from the full FF list. -/
theorem ClassifiedAction.remaining_ff {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂) :
    RemainingFFAlternative (ρ.comp (offenderSubgroup ρ).subtype) := by
  cases h.ffAlternatives with
  | trivial ht =>
    let : Subsingleton (offenderSubgroup ρ) := ht
    let : Nontrivial (offenderSubgroup ρ) := FFAlternatives.nontrivial_of_ff _ h.ffWitness
    obtain ⟨g, hg⟩ := exists_ne (1 : offenderSubgroup ρ)
    exact (hg (Subsingleton.elim _ _)).elim
  | quasisimple hq ha => exact Or.inl ⟨hq, ⟨ha⟩⟩
  | symmetricThree hs => exact (h.not_symmetricThree ⟨hs.equiv⟩).elim
  | twoFactors hs => exact Or.inr (Or.inl ⟨hs⟩)
  | outerSixThree hs => exact Or.inr (Or.inr (Or.inl ⟨hs⟩))
  | hyperplane hs => exact Or.inr (Or.inr (Or.inr ⟨hs⟩))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
