module
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentExclusions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.CentralRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.SelfDual
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedLinearThreeDuality

/-!
# Excluding whole marked binary SL₃ central covers

A self-dual irreducible binary SL₃ module has degree at least 8n: the actual
natural and dual actions are not self-dual, nor is the descended half-field
tensor. The original G.9 degree bound is at most 4n+2, using the automorphism
rank of the exact central quotient. Thus no such component can occur.

The result retains the original action and central covering map. The whole
strict-source application is supplied in `StrictWholeModels`. The argument
also underlies the separate Chapter 14 marked-image calculation.
Source: Aschbacher--Smith G.9.3(8),(17), G.11.7 and 14.3.15.
-/

@[expose] public noncomputable section
open Matrix Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section11.WholeLinearThree
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedLinearThree

section Small
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Every nontrivial self-dual binary SL₃ module has degree at least 8n.
The natural and half-field tensor alternatives are excluded on their actual
binary descended actions. -/
theorem selfDual_degree_ge_eight
    (ρ : Representation (ZMod 2) SL(3,K) V) [IsIrreducible ρ]
    (hact : ∃ g, ρ g ≠ 1) (hs : Nonempty (ρ.Equiv ρ.dual))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card K = 2 ^ n) :
    8 * n ≤ Module.finrank (ZMod 2) V := by
  let := ZMod.algebra K 2
  obtain ⟨hpos, hmodel⟩ := AbsoluteExhaustion.absolute_model_trichotomy ρ hact n hn hcard
  rcases hmodel with ⟨hschur, _, hnatural⟩ | ⟨hnt, hdeg, hmodel⟩ | hlarge
  · have hdesc := descend_absolute_natural ρ n hcard hschur hnatural
    change Nonempty (ρ.Equiv (naturalBinary K)) ∨ Nonempty (ρ.Equiv (dualBinary K)) at hdesc
    rcases hdesc with hnat | hdual
    · obtain ⟨e⟩ := hnat
      exfalso
      apply natural_not_selfDual (k := K)
      exact selfDual_of_quasiequivalent ρ (naturalBinary K)
        ⟨MulEquiv.refl _, e.toLinearEquiv,
          fun g v => IntertwiningMap.isIntertwining ρ _ e.toIntertwiningMap g v⟩ hs
    · obtain ⟨e⟩ := hdual
      exfalso
      apply dualNatural_not_selfDual (k := K)
      exact selfDual_of_quasiequivalent ρ (dualBinary K)
        ⟨MulEquiv.refl _, e.toLinearEquiv,
          fun g v => IntertwiningMap.isIntertwining ρ _ e.toIntertwiningMap g v⟩ hs
  · exact (not_selfDual_absolute_twisted ρ (schurDegree ρ) hpos
      (by rw [←hnt]; exact hcard) rfl hmodel hs).elim
  · exact hlarge
end Small

section Component
universe u w
variable {D : Type u} [Group D] [Finite D]
  {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {C : GroupClass.{u}} {ρ : Representation (ZMod 2) D V}
  {A L : Subgroup D} {m : ℕ}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
open Theory.GroupTheory Subgroup ChapterG.Section09

/-- The original G.9 degree window excludes every self-dual binary SL₃
central quotient, retaining the original covering homomorphism. -/
theorem not_single_component_linear_three
    (h : ComponentHypothesis C ρ A L L m)
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (Representation.dual (ρ.comp L.subtype))))
    (π : SL(3,K) →* L) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center SL(3,K))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card K = 2 ^ n) : False := by
  let τ := ρ.comp L.subtype
  let : IsIrreducible τ := h.irreducible
  let : Nontrivial L := L.nontrivial_iff_ne_bot.mpr (by
    intro hL
    exact h.noncentral (by rw [hL, commutator_bot_left]))
  let : IsIrreducible (τ.comp π) :=
    (irreducible_comp_surjective_iff π hπ τ).mpr inferInstance
  have hnon : ∃ g, (τ.comp π) g ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    obtain ⟨g, rfl⟩ := hπ x
    refine ⟨g, fun hg => hx ((h.faithful.comp L.subtype_injective) ?_)⟩
    exact hg.trans τ.map_one.symm
  have hm := h.toSetup.rank_le_automorphisms (L := L) (by
    rw [normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top)
  have hr := central_quotient_automorphism_rank_le π hπ hcentral
  rw [Matrix.PSL3Even.automorphism_two_rank_eq K hn hcard] at hr
  have hdeg := selfDual_degree_ge_eight (τ.comp π) hnon (selfDual_comp τ π hs) n hn hcard
  have hdim := h.degree_le
  omega
end Component

/-- Both literal binary linear-three carriers are excluded by self-duality. -/
theorem not_binary_model
    {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {C : GroupClass} {ρ : Representation (ZMod 2) D V}
    {A L : Subgroup D} {m : ℕ}
    (h : ChapterG.Section09.ComponentHypothesis C ρ A L L m)
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (Representation.dual (ρ.comp L.subtype))))
    {n : ℕ} (hn : 0<n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ Chapter1.Section02.LocalModels.IsSL L 3 (2^n)) :
    False := by
  rcases model with model | model
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact not_single_component_linear_three h hs
      (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,Matrix.PSL3.projection_ker])
      n hn hcard
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact not_single_component_linear_three h hs e.symm.toMonoidHom e.symm.surjective
      (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le) n hn hcard
end CFSG.Quasithin.ChapterG.Section11.WholeLinearThree
