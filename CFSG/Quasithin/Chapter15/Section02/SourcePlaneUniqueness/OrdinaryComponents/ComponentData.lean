module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.OddCore
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Components
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.GeneralizedFitting.SylowComponentOrbit
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Actual ordinary components for the plane uniqueness argument

Trivial odd core and F*(I) ≠ O₂(I) supply an ordinary component L. The
original 1.1.5 gives its actual model and conjugation action, and excludes
L ≤ Mc. Odd rank at most two makes its S-orbit span normal in I; minimality
then gives I = L₀(Mc∩I). The center of L is a two-group, and the literal
central involution subgroup acts faithfully on L.

The terminal model/action interface records the target of the independent
15.2.24 argument. It is not constructed here. The characteristic-two model
exclusion and the final rank-one/sporadic contradictions remain necessary.

Source: Aschbacher--Smith, paragraph before 15.2.24 and pp.1117--1118,
refs/quasithin.pdf.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 ChapterA.Section05To06
open Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- The actual ordinary component and its Sylow orbit. All normality is inside I. -/
structure ComponentData (I : Subgroup G) (P : Sylow 2 I) (z : G) where
  component : Subgroup I
  isComponent : IsComponent I component
  escapes : ¬ component.map I.subtype ≤ Mc
  center_eq : center component = pCore 2 component
  center_two : IsPGroup 2 (center component)
  oddCore_eq : pPrimeCore 2 component = ⊥
  moved : component.map I.subtype = ⁅component.map I.subtype,zpowers z⁆
  model : HasModelAction115 component z
  faithful : centralInvolutions T ⊓ centralizer (component.map I.subtype : Set G) = ⊥
  orbit_normal : (conjugateSpanBy component (P : Subgroup I)).Normal
  generates : (conjugateSpanBy component (P : Subgroup I)).map I.subtype ⊔ (Mc ⊓ I) = I


include d
/-- The source component selection before 15.2.24, including the normal Sylow orbit and faithful Z-action. -/
theorem exists_component_data {I : Subgroup G} (hI : MinimalPlaneEscape Mc ZS I)
    (hF : generalizedFitting I ≠ pCore 2 I) :
    ∃ (P : Sylow 2 I) (z : G),
      (P : Subgroup I).map I.subtype = planeSylow T ZS ∧
      z ∈ centralInvolutions T ∧ z ≠ 1 ∧ Nonempty (ComponentData (T := T) (Mc := Mc) I P z) := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI.1
  obtain ⟨z,hz,hzne,_⟩ := exists_central_moved_involution d
  have ho := oddCore_eq_bot d hI.1
  obtain ⟨L,hL⟩ := exists_ordinary_component_of_fstar_ne_twoCore ho hF
  have hm := lemma115 d hI.1 P hP hz hzne
  obtain ⟨hmoved,hout,hmodel⟩ := Chapter1.lemma_1_1_5_three_knownSimple
    hsource.ambient I P Mc z hm L hL
  let L0 := conjugateSpanBy L (P : Subgroup I)
  have hn : L0.Normal := by
    change (conjugateSpanBy L (P : Subgroup I)).Normal
    rw [conjugateSpanBy_eq_iSup_conj]
    exact componentOrbit_normal_of_normal_or_index_two L P
      (hL.normal_or_index_two_of_odd_rank_le_two
        (Chapter3.sqtk_of_mem_H hsource.ambient hI.1.1).stronglyQuasithin)
  have hgen : L0.map I.subtype ⊔ (Mc ⊓ I) = I := by
    have hJI : L0.map I.subtype ⊔ (Mc ⊓ I) ≤ I := sup_le (map_subtype_le _) inf_le_right
    rcases d.minimal_intermediate hI le_sup_right hJI with he | he
    · exact (hout ((map_mono (le_conjugateSpanBy L (P : Subgroup I))).trans
        (le_sup_left.trans (he.le.trans inf_le_left)))).elim
    · exact he
  have hfaith : centralInvolutions T ⊓ centralizer (L.map I.subtype : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1
    apply False.elim
    apply hout
    rw [← (marked_centralizer d hI.1 hx.1 hx1).2]
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (hx.2 y hy)
  have hcenter := component_center_eq_twoCore hL ho
  have hcenter2 : IsPGroup 2 (center L) := hcenter ▸ pCore_isPGroup
  exact ⟨P,z,hP,hz,hzne,⟨⟨L,hL,hout,hcenter,hcenter2,
    component_oddCore_eq_bot hL ho,hmoved,hmodel,hfaith,hn,hgen⟩⟩⟩


open Section03.Candidates.ComponentStructure ClassificationModels
/-- The genuine model/action rows left after original 15.2.24. The small
PSL₂ aliases of characteristic-two groups have also been removed. This is a
shared conclusion to be constructed by the even-model argument, not an
assumption of the source theorem. -/
inductive TerminalModelAction115 (L : Type*) [Group L] (α : MulAut L) : Prop
  | seven (σ : Equiv.Perm (Fin 7)) (cycles : σ.cycleType = {2, 2, 2})
      (action : AlternatingAction α 7 σ)
  | linear_three (model : ClassicalGroup.IsPSL L 3 3)
      (inner : α ∈ (MulAut.conj (G := L)).range)
  | linear_two (p : ℕ) (prime : IsFermatOrMersennePrime p) (large : 7 < p)
      (model : ClassicalGroup.IsPSL L 2 p)
      (inner : α ∈ (MulAut.conj (G := L)).range)
  | sporadic (name : SporadicName) (not_j3 : name ≠ .j3)
      (model : Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier))
      (action : TwoCentralInner α)

/-- The remaining alternatives retain the literal conjugation action of z. -/
@[expose] def HasTerminalModelAction115 {I : Subgroup G} (L : Subgroup I) (z : G) : Prop :=
  ∃ α : MulAut L, (∀ x : L, ((α x : I) : G) = z * (x : G) * z⁻¹) ∧
    TerminalModelAction115 L α

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
