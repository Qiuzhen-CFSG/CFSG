module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNatural
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Markings

/-!
# The two possible modules for the original point constituent

The actual point component has two-core quotient A₈. Applying the genuine
seven-row theorem to a chosen constituent eliminates every row except the
natural four-space and the deleted eight-point central quotient. The latter
identifies I/C_I(K₁), retaining any central attachment in the full I.

This is the local module alternative needed before the second application of
12.6.34 in 12.9.4. No natural-four reduction is assumed or concluded in the
remaining alternating row.
Source: Aschbacher--Smith 12.2.2 and 12.9.4, printed pp.795,859--860.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original seven rows on an A₈ core quotient leave full natural-four
coordinates or the literal deleted-eight central quotient. -/
theorem chosen_eight_natural_or_deleted
    {J I : Subgroup G} (c : ChosenModule T J I)
    (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 8))
    (rows : ModuleAlternatives1222 c) :
    letI := c.actionCentralizer_normal
    NaturalModule c 4 ∨ Nonempty (ActionEquiv c.faithfulCentralAction (alternatingNatural 8)) := by
  let := c.actionCentralizer_normal
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (J ⧸ pCore 2 J) := e.isSimpleGroup
  have hc : Nat.card (J ⧸ pCore 2 J) = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hlin (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
      (a : (J ⧸ pCore 2 J) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : n = 4 := by
    have hd := Nat.card_congr a.toEquiv
    rw [hc] at hd
    rcases hn with rfl | rfl | rfl
    · rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hd
      omega
    · rfl
    · rw [Representation.SL5ExteriorSquare.card_specialLinearFive] at hd
      omega
  have halt (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
      (a : (J ⧸ (centralizer (I : Set G)).subgroupOf J) ≃*
        alternatingGroup (Fin n)) : n = 8 := by
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hd := Nat.card_congr ((c.coreToFaithfulEquiv hs).trans a).toEquiv
    rw [hc, nat_card_alternatingGroup, Nat.card_fin] at hd
    have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl
    · norm_num at hd
    · norm_num at hd
    · norm_num at hd
    · rfl
  cases rows with
  | linear n hn a =>
    obtain rfl := hlin n hn a.groupEquiv
    exact .inl (Section05.NaturalSource.naturalModule_of_actionEquiv c 4 a)
  | linearThreeExtension a _ _ =>
    have he := hlin 3 (.inl rfl) a
    omega
  | linearFiveExterior a _ _ =>
    have he := hlin 5 (.inr (.inr rfl)) a
    omega
  | alternating n hlo hhi a =>
    obtain rfl := halt n hlo hhi a.groupEquiv
    exact .inr ⟨a⟩
  | alternatingSevenFour a _ =>
    have he := halt 7 (by decide) (by decide) a
    omega
  | g2 a =>
    have hd := Nat.card_congr a.groupEquiv.toEquiv
    rw [hc, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tripleSix a _ _ _ =>
    have hd := Nat.card_congr a.toEquiv
    rw [hc, Atlas.Codes.hexEven_card] at hd
    norm_num at hd

/-- The same original point constituent has only these two rows. The actual
point component and its faithful maximality are supplied by the source;
no `NaturalReduction 4` input is used. -/
theorem nonabelian_caseFive_chosen_natural_or_deleted
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I) :
    letI := c.actionCentralizer_normal
    NaturalModule c 4 ∨ Nonempty (ActionEquiv c.faithfulCentralAction (alternatingNatural 8)) := by
  have hm := nonabelian_caseFive_maximal_of_modules modules h preferred earlier F hne g hgP hgH B h5 C
  have hj := nonabelian_caseFive_maximal_hypothesis h earlier F hne B h5 C hm le_rfl
  obtain ⟨e, _⟩ := nonabelian_caseFive_point_core_equiv h earlier F hne B h5 C
  obtain ⟨a⟩ := nonabelian_caseFive_alternating_eight h (Or.inl rfl) earlier F hne B h5
  exact chosen_eight_natural_or_deleted c (e.trans a) (modules C.K1 I hj c)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
