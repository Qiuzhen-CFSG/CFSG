module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieve
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSylow
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceKernel
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceActionFrattiniContradiction
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveAssembly

/-!
# Original marked-MS inputs for the outer-action nonblock argument

The original source component carries secondary action data without strict
core enlargement. The source local-image geometry and generation exclude the
nonexceptional rows. The same original S∩K₂ supplies the secondary-image
Sylow, and the original crossing preserves S-star while moving R₂-star.
In the full PSL₃(4) row the actual quotient-action kernel is prime to three.
The final theorem combines the action-only quotient sieve, the cubic root
frame and the marked Frattini contradiction. It proves False from the genuine
whole-core MS alternatives and their simultaneous quotient/Sylow markings,
without strict secondary-core enlargement or a SecondarySourceData witness.

The original nonbinary whole-core alternatives remain an explicit earlier
input, with producer qt-c134-nonbinary-linear-three-source. This conditional
contradiction does not instantiate the refuted universal
EarlierMSClassifications interface or by itself prove unconditional 4.3.2.
Source: Aschbacher–Smith, original 4.3.11–16 and conclusion of 4.3.2,
printed pp.617–619; C.1.34(3), printed pp.136–137.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
set_option maxHeartbeats 800000
open EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- All source geometry and the literal crossing from the original marked inputs.
The model and full Frattini recognitions are not additional input fields. -/
theorem MSData.secondary_outer_action_source
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    ∃ s : SecondaryActionData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      SecondaryActionData.ActionGeneration s ∧ SecondaryActionData.LocalImageData s ∧
      ¬ NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      Chapter1.IsSylowIn 2 (SecondaryActionData.image s (S c ⊓ secondary c))
        (SecondaryActionData.secondaryImage s) ∧
      (∀ _e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL,
        Nat.Coprime 3 (Nat.card s.action.ker)) ∧
      let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
      (SecondaryActionData.image s (S c)).map (MulAut.conj (s.action t)).toMonoidHom =
          SecondaryActionData.image s (S c) ∧
        s.action t ^ 2 ∈ SecondaryActionData.image s (S c) ∧
        (SecondaryActionData.image s (S c) ⊓ SecondaryActionData.componentImage s).map
          (MulAut.conj (s.action t)).toMonoidHom =
            SecondaryActionData.image s (S c) ⊓ SecondaryActionData.componentImage s ∧
        (SecondaryActionData.radicalImage s).map (MulAut.conj (s.action t)).toMonoidHom ≠
          SecondaryActionData.radicalImage s := by
  obtain ⟨s,hs,hY,hfix,hgen⟩ := d.exists_secondaryActionData hn D h hL hSL
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact ⟨s,hs,hY,hfix,hgen,SecondaryActionData.localImageData s D,
    SecondaryActionData.not_nonexceptional_of_generation s hn hgen,
    SecondaryActionData.original_sylow_image s D,
    fun e => s.action_kernel_coprime_three D h e,
    SecondaryActionData.crossing_image_geometry s m hn D⟩

/-- The nonexceptional rows are excluded for the actual selected component. -/
theorem MSData.sourceComponent_not_nonexceptional
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    ¬ NonexceptionalModel (d.sourceComponent hn D h hL hSL ⧸
      pCore 2 (d.sourceComponent hn D h hL hSL)) n := by
  obtain ⟨s,hs,_,_,hgen⟩ := d.exists_secondaryActionData hn D h hL hSL
  have hnexc := SecondaryActionData.not_nonexceptional_of_generation s hn hgen
  cases s
  cases hs
  exact hnexc

open scoped MatrixGroups
/-- Apply the source construction to the MS witness and simultaneous markings
supplied by the whole-core alternatives, retaining the literal action. -/
theorem source_outer_action_of_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) :
    ∃ s : SecondaryActionData c n,
      s.torus ≤ K c ∧ Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      SecondaryActionData.ActionGeneration s ∧ SecondaryActionData.LocalImageData s ∧
      ¬ NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
      (SecondaryActionData.radicalImage s).map (MulAut.conj (s.action t)).toMonoidHom ≠
        SecondaryActionData.radicalImage s := by
  obtain ⟨d,_,hL,hSL⟩ := DoubledMarking.source_msData_of_alternatives D hf hb n hn
    F hdegree e P hP hm
  obtain ⟨s,_,hY,hfix,hgen,hlocal,hnexc,_,_,_,_,_,hcross⟩ :=
    d.secondary_outer_action_source hn D h hL hSL
  exact ⟨s,hY,hfix,hgen,hlocal,hnexc,hcross⟩

open SourceActionEndgame
open scoped MatrixGroups

/-- The marked original MS witness already forces the action-only Frattini
contradiction. The secondary component and its action are constructed without
the strict core-enlargement premise of the older source-component API. -/
theorem MSData.false_of_source_markings
    (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) =
      unipotentSL d.field.Carrier) : False := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨s,_,_,_,hgen,_,_,_,_,_⟩ := d.secondary_outer_action_source hn D h hL hSL
  obtain ⟨⟨hn2,hmodel⟩,_⟩ :=
    EndgameSieve.SecondaryActionData.linearFour_of_coordinates s d m hn D h
  cases hn2
  let d₂ : MSData c 2 := d
  let s₂ : SecondaryActionData c 2 := s
  let m₂ : RootCoordinates d₂ := m
  let hgen₂ : EndgameSieve.SecondaryActionData.ActionGeneration s₂ := hgen
  let hmodel₂ : ClassicalGroup.IsPSL (s₂.component ⧸ pCore 2 s₂.component) 3 4 := hmodel
  obtain ⟨F',_,_,hF',⟨e'⟩⟩ := hmodel₂
  let : Fintype F' := Fintype.ofFinite F'
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let i : F' ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hF', Matrix.PSL3Four.card_F])
  let mark : (s₂.component ⧸ pCore 2 s₂.component) ≃* Matrix.PSL3Four.PSL :=
    e'.trans (Atlas.fieldEquivPSL 3 i)
  obtain ⟨mark',b,X,hXr,hX3,hXK,hfix,hcomm,φ,hφ,_,hsquare,hframe⟩ :=
    SourceActionEndgame.exists_source_cubic_root_frame (G := G) (F := Matrix.PSL3Four.F)
      (c := c) d₂ s₂ D h hgen₂
      (by exact Matrix.PSL3Four.card_F) mark
  obtain ⟨x,horder⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX3])
  have hx : x ≠ 1 := by
    intro hx1
    subst x
    simp at horder
  exact source_action_marked_frattini_false_of_generation m₂ s₂ D h hgen₂ mark' X hX3 hXK hXr
    hfix hcomm φ hφ hsquare x hx b ((hframe x).2.2 hx) (hframe x).2.1

/-- The genuine marked-MS alternatives force the source-action Frattini
contradiction in the surviving PSL₃(4) row. -/
theorem false_of_source_action_of_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) : False := by
  obtain ⟨d,_,hL,hSL⟩ := DoubledMarking.source_msData_of_alternatives D hf hb n hn
    F hdegree e P hP hm
  exact d.false_of_source_markings hn D h hL hSL

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
