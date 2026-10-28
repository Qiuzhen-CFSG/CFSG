module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.OmegaAction
public import Theory.Representation.BinaryAlternatingSevenControl.NormalFixedKernel
/-!
# Residual movement on the exceptional FF action

The two surviving actual A7 actions have five-free kernels on the fixed
space of the full Sylow actor. The deleted module uses the faithful normal
extension into S7; the four-space uses its intrinsic normal-actor theorem.
All actions and component inclusions retain the original quotient maps.
Source: Aschbacher--Smith 5.1.13, printed p.637.
-/
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExceptionalFixed
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

private theorem no_linearThree {E : Type*} [Group E] (hE : Nat.card E = 2520)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = 2520 := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,← pow_mul,hc] at hd
  have hdeg : F.degree ≤ 1 := by
    by_contra hn
    have hh : 64 ∣ 2520 := (pow_dvd_pow 2 (by omega : 6 ≤ F.degree * 3)).trans hd
    norm_num at hh
  have he : F.degree = 1 := by have := F.degree_pos; omega
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq,he] at hc
  norm_num at hc

private theorem no_binaryLinear {E : Type*} [Group E] (hE : Nat.card E = 2520)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  have hcard (n : ℕ) : Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,Matrix.card_GL_field]
    simp
  rcases hd with rfl | rfl <;> rw [hcard] at hc <;> norm_num [Fin.prod_univ_succ] at hc

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Full movement retains the actual natural coordinates or actual four-space. -/
theorem natural_or_four (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (e : C ≃* alternatingGroup (Fin 7)) (hz : center C = ⊥)
    (hm : moved ρ C = ⊤) :
    IsAlternatingNatural (ρ.comp C.subtype) 7 ∨ Module.finrank (ZMod 2) V = 4 := by
  have hc : Nat.card C = 2520 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have horder : ExceptionalActions.ExceptionalOrder C := Or.inl hc
  have hfixed := (ExceptionalActions.fully_moved_source ρ c horder hz hm).2.2.1
  let a := c.sectionData.fullComponentActionEquiv hm hfixed
  cases c.clause_one with
  | irreducible _ _ _ hs _ =>
    rcases ChapterB.QuasisimpleSource.SourceCompletion.AlternatingSevenActor.natural_or_four _ hs e with hn | hd
    · obtain ⟨b⟩ := hn
      left
      exact ⟨{ groupEquiv := b.groupEquiv
               linearEquiv := a.linearEquiv.trans b.linearEquiv
               intertwines := fun g v => by
                 change b.linearEquiv (a.linearEquiv (ρ g.val v)) = _
                 exact (congrArg b.linearEquiv (a.intertwines g v)).trans
                   (b.intertwines g (a.linearEquiv v)) }⟩
    · exact Or.inr (a.linearEquiv.finrank_eq.trans hd)
  | doubleThree F _ a _ _ => exact (no_linearThree hc F a.groupEquiv).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim

/-- The full original actor's Sylow-fixed kernel is prime to five. -/
theorem sylow_fixedKernel_five_free
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (A N : Subgroup D) [A.Normal] (hAN : A ≤ N)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp N.subtype) (A.subgroupOf N))
    (e : A ≃* alternatingGroup (Fin 7)) (hz : center (A.subgroupOf N) = ⊥)
    (hm : moved (ρ.comp N.subtype) (A.subgroupOf N) = ⊤)
    (P : Sylow 2 D) (B : Subgroup D)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ P, ρ b v = v) : ¬5 ∣ Nat.card B := by
  let E := (subgroupOfEquivOfLe hAN).symm
  rcases natural_or_four (ρ.comp N.subtype) (A.subgroupOf N) c (E.symm.trans e) hz hm with hn | hd
  · obtain ⟨a⟩ := hn
    exact BinaryAlternatingSevenControl.natural_actor_sylow_fixedKernel_five_free
      ρ hf A (E.trans a.groupEquiv) a.linearEquiv (fun x v => a.intertwines (E x) v) P B hB
  · exact BinaryAlternatingSevenControl.normal_actor_sylow_fixedKernel_five_free ρ hf hd A e P B hB
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExceptionalFixed
