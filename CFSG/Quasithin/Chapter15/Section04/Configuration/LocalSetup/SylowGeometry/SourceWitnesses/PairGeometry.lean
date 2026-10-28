module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors.Permutation.SourceModules
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CentralAssembly
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.FactorIndex

/-!
# Source pairs and the preceding whole-module decompositions

The pair is constructed from the actual source action, retaining its original
quotient, its order-four commutator modules, and the Baumann action. The only
module premises retained are the whole-module conclusions of 15.4.12(4–6):
the Sylow supplement, the omega-center containment and direct decomposition,
and the index of the fixed summand. None refers to the later group I.

The ambient commutator modules centralize each other and the opposite factor.
Restricting the actual pair action to its first stabilizer normalizes both
modules. These facts construct the raw action inputs for Lemma 15.4.19.
Source: Aschbacher–Smith, printed pp.1160–1163.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
open TwoFactors TwoFactors.SourceFactors
open TwoFactors.SourceFactors.Permutation.SourceApplication
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

/-- Exactly the earlier whole-group Sylow and whole-module conclusions used
here; the producer remains the source assembly of 15.4.12(4–6). -/
structure Earlier412 (T : Sylow 2 G) (M X : Subgroup G) : Prop where
  sylow : ∃ P : Sylow 2 (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G),
    (P : Subgroup (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G)).map
      (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G).subtype =
        ChapterB.baumann (T : Subgroup G)
  moved_le_omega : movedModule (T : Subgroup G) M X ≤
    Stellmacher.omegaOneCenterAmbient ((X ⊔ (T : Subgroup G)).pCoreIn 2)
  disjoint : Disjoint (fixedSummand (T : Subgroup G) X) (movedModule (T : Subgroup G) M X)
  decomposition : fixedSummand (T : Subgroup G) X ⊔
    (movedModule (T : Subgroup G) M X ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G)) =
      ChapterB.thompsonAlpha (T : Subgroup G)
  index : (fixedSummand (T : Subgroup G) X).relIndex (ChapterB.thompsonAlpha (T : Subgroup G)) = 4

/-- One source-produced pair, with the actual modules of that same pair. -/
structure Pair (T : Sylow 2 G) (M X : Subgroup G) where
  quotient : QuotientPair T M X
  baumann : ∀ i, ChapterB.baumann (T : Subgroup G) ≤ normalizer (quotient.factor i : Set G)
  module_card : ∀ i, Nat.card (quotient.moduleFactor i) = 4
  module_disjoint : Disjoint (quotient.moduleFactor false) (quotient.moduleFactor true)
  module_join : quotient.moduleFactor false ⊔ quotient.moduleFactor true =
    movedModule (T : Subgroup G) M X

/-- The source action constructs the pair; its permutation and modules are
not extra premises of the later geometry. -/
theorem exists_pair (h : Input K T M X 2) : Nonempty (Pair T M X) := by
  obtain ⟨d, _, hn, hd, hj⟩ :=
    Permutation.SourceModules.source_factor_modules h
  exact ⟨⟨d, fun i => (hn i).1, fun i => (hn i).2.2, hd, hj⟩⟩

private theorem normalizes_pair (p : Pair T M X) (hTM : (T : Subgroup G) ≤ M)
    {U : Subgroup G} (hUT : U ≤ T)
    (hn : U ≤ normalizer (p.quotient.factor false : Set G)) :
    ∀ i, U ≤ normalizer (p.quotient.factor i : Set G) := by
  intro i u hu
  let a := p.quotient.action
  let m : M := ⟨u, hTM (hUT hu)⟩
  have he : a.permutation m false = false := a.distinct
    ((a.conjugation m false).symm.trans (mem_normalizer_iff_map_conj_eq.mp (hn hu)))
  have hei : a.permutation m i = i := by
    cases i
    · exact he
    · cases ht : a.permutation m true
      · exact False.elim (Bool.false_ne_true ((a.permutation m).injective (he.trans ht.symm)))
      · rfl
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (a.conjugation m i).trans (congrArg p.quotient.factor hei)

/-- Each actual source factor together with T generates the original XT. -/
theorem Pair.factor_join_sylow (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    p.quotient.factor i ⊔ (T : Subgroup G) = X ⊔ (T : Subgroup G) := by
  obtain ⟨t, ht, hs, hs', _⟩ := p.quotient.interchange
  cases i
  · exact MixedLocal.pair_join_eq_of_swap (p.quotient.factor_generate h) ht hs
  · have hg : p.quotient.factor true ⊔ p.quotient.factor false = X := by
      rw [sup_comm]
      exact p.quotient.factor_generate h
    exact MixedLocal.pair_join_eq_of_swap (L := fun i => p.quotient.factor (!i)) hg ht hs'

omit [Finite G] in
private theorem whole_module_geometry (earlier : Earlier412 T M X) :
    movedModule (T : Subgroup G) M X ≤ ChapterB.baumann (T : Subgroup G) ∧
    movedModule (T : Subgroup G) M X ⊓ centralizer (X : Set G) = ⊥ ∧
    ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G) =
      fixedSummand (T : Subgroup G) X := by
  let W := movedModule (T : Subgroup G) M X
  let Q := Stellmacher.omegaOneCenterAmbient ((X ⊔ (T : Subgroup G)).pCoreIn 2)
  let C := fixedSummand (T : Subgroup G) X
  let E := ChapterB.thompsonAlpha (T : Subgroup G)
  let S := ChapterB.baumann (T : Subgroup G)
  let := Stellmacher.omegaOneCenterAmbient_elementaryAbelian ((X ⊔ (T : Subgroup G)).pCoreIn 2)
  have hWQ : W ≤ Q := earlier.moved_le_omega
  have hCQ : C ≤ Q := inf_le_left
  have hdecomp : C ⊔ (W ⊓ centralizer (S : Set G)) = E := earlier.decomposition
  have hEQ : E ≤ Q := by
    rw [← hdecomp]
    exact sup_le hCQ (inf_le_left.trans hWQ)
  have hQT : Q ≤ (T : Subgroup G) := by
    have hQcore : Q ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 :=
      fun _ hx => ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx).1
    apply hQcore.trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (X ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWS : W ≤ S := by
    refine le_inf (hWQ.trans hQT) ?_
    intro w hw e he
    exact setLike_mul_comm (hEQ he) (hWQ hw)
  have hfree : W ⊓ centralizer (X : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro w hw
    exact (disjoint_iff.mp earlier.disjoint).le ⟨⟨hWQ hw.1, hw.2⟩, hw.1⟩
  have hCeq : E ⊓ centralizer (X : Set G) = C := by
    apply fixed_summand_eq_centralizer hdecomp
    · intro c hc w hw
      exact setLike_mul_comm (hWQ hw.1) (hCQ hc)
    · exact inf_le_right
    · exact le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hfree.le)
  exact ⟨hWS, hfree, hCeq⟩

/-- Original whole-module source conclusions imply every factor action input
used by the central fixed-space argument, for any subgroup of the stabilizer. -/
theorem Pair.factor_actions (p : Pair T M X) (h : Input K T M X 2)
    (earlier : Earlier412 T M X) {U : Subgroup G} (hUT : U ≤ T)
    (hn : U ≤ normalizer (p.quotient.factor false : Set G)) :
    let L := p.quotient.factor
    let V := p.quotient.moduleFactor
    let E := ChapterB.thompsonAlpha (T : Subgroup G)
    let S := ChapterB.baumann (T : Subgroup G)
    let C := E ⊓ centralizer ((L false ⊔ L true : Subgroup G) : Set G)
    (∀ i, V i ≤ S) ∧ (∀ i, U ≤ normalizer (V i : Set G)) ∧
    (∀ i, V i ≠ ⊥) ∧ V false ≤ centralizer (V true : Set G) ∧
    Disjoint (V false) (V true) ∧ Disjoint C (V false ⊔ V true) ∧
    C ⊔ ((V false ⊔ V true) ⊓ centralizer (S : Set G)) = E ∧
    C.relIndex E = 4 ∧ (∀ i, V (!i) ≤ centralizer (L i : Set G)) ∧
    (V false ⊔ V true) ⊓ centralizer ((L false ⊔ L true : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨hWS, hfree, hCeq⟩ := whole_module_geometry (T := T) (M := M) (X := X) earlier
  let W := movedModule (T : Subgroup G) M X
  let S := ChapterB.baumann (T : Subgroup G)
  have hjoin : p.quotient.moduleFactor false ⊔ p.quotient.moduleFactor true = W := p.module_join
  have hViW (i) : p.quotient.moduleFactor i ≤ W := by
    exact (show p.quotient.moduleFactor i ≤ p.quotient.moduleFactor false ⊔ p.quotient.moduleFactor true from by
      cases i
      · exact le_sup_left
      · exact le_sup_right).trans_eq hjoin
  have hnL := normalizes_pair p h.sylow_le hUT hn
  have hnormV : M ≤ normalizer (localV (T : Subgroup G) M : Set G) :=
    localV_normalized (T : Subgroup G) M
  have hVL : X ≤ normalizer (localV (T : Subgroup G) M : Set G) :=
    le_trans h.member_le hnormV
  dsimp only
  refine ⟨fun i => (hViW i).trans hWS, ?_, ?_, ?_, p.module_disjoint, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact commutator_factors_normalized ((hUT.trans h.sylow_le).trans
      hnormV) (hnL i)
  · intro i hb
    have hc := p.module_card i
    rw [hb, card_bot] at hc
    omega
  · let := h.moved_elementary
    intro a ha b hb
    exact setLike_mul_comm (hViW true hb) (hViW false ha)
  · rw [p.quotient.factor_generate h, hCeq, p.module_join]
    exact earlier.disjoint
  · rw [p.quotient.factor_generate h, hCeq, p.module_join]
    exact earlier.decomposition
  · rw [p.quotient.factor_generate h, hCeq]
    exact earlier.index
  · intro i
    cases i
    · apply factor_centralizes_sibling_module (Y₁ := p.quotient.factor true)
      · rw [sup_comm, p.quotient.factor_generate h]
        exact hVL
      · rw [sup_comm, p.quotient.factor_generate h]
        exact p.quotient.factor_normalized h true
      · exact p.module_disjoint.symm
    · apply factor_centralizes_sibling_module (Y₁ := p.quotient.factor false)
      · rw [p.quotient.factor_generate h]
        exact hVL
      · rw [p.quotient.factor_generate h]
        exact p.quotient.factor_normalized h false
      · exact p.module_disjoint
  · rw [p.quotient.factor_generate h, p.module_join]
    exact hfree

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
