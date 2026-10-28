module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentNatural

/-!
# The original natural constituent with its full source attachments

The actual component and chosen constituent are selected before applying the
new local deleted-module exclusion. The same constituent has order sixteen,
its returning-center fixed subgroup has order four, and the whole point
centralizer normalizes it. No independent NaturalReduction4 premise remains
in this source selection.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Select the actual natural constituent with its original commutator,
center supplement, point-normalizer action, and returning fixed four-group. -/
theorem nonabelian_caseFive_natural_constituent_of_original_rows
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (C : ComponentGeometry F L) (I : Subgroup G) (c : ChosenModule T C.K1 I),
      NaturalModule c 4 ∧ I ≤ nonabelianCenterModule F L C.K1 ∧ I ≤ F.ZU ∧
      (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)) ⊔ I = F.ZU ∧
      I = ⁅F.ZU,C.K1⁆ ∧ F.H ≤ normalizer (I : Set G) ∧
      Nat.card I = 16 ∧ Nat.card (I ⊓ centralizer (conjugate F.ZU g : Set G) : Subgroup G) = 4 := by
  obtain ⟨C⟩ := componentGeometry earlier h (.inl rfl) F
  obtain ⟨I,⟨c⟩,hi,hz,he,hidx⟩ :=
    nonabelian_center_exists_rank_two_chosen h earlier F hne g hgP hgH B h5 C
  have hn := nonabelian_caseFive_chosen_natural_of_original_rows modules h preferred earlier
    F hne g hgP hgH B h5 C c hz
  let := c.elementary
  obtain ⟨m⟩ := hn
  have hc : Nat.card I = 16 := by
    calc
      Nat.card I = Nat.card (Additive I) := rfl
      _ = Nat.card (Fin 4 → ZMod 2) := Nat.card_congr m.coordinates.toEquiv
      _ = 16 := by rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; decide
  refine ⟨C,I,c,⟨m⟩,hi,hz,he,
    nonabelian_caseFive_chosen_eq_center_commutator modules h preferred earlier F hne g hgP hgH B h5 C c hz,
    nonabelian_caseFive_point_normalizes_chosen modules h preferred earlier F hne g hgP hgH B h5 C c hz,hc,?_⟩
  let A := I ⊓ centralizer (conjugate F.ZU g : Set G)
  have hm := (A.subgroupOf I).card_mul_index
  have ha : Nat.card (A.subgroupOf I) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe (show A ≤ I from inf_le_left)).toEquiv
  change Nat.card (A.subgroupOf I) * A.relIndex I = Nat.card I at hm
  rw [ha,hidx,hc] at hm
  change Nat.card A = 4
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
