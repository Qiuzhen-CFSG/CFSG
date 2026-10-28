module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedNatural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.Reselection
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ModelSeparation
public import Theory.SpecificGroups.Janko4.Model.Center
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponents
public import Theory.GroupTheory.PGroup.OmegaCenterIn
-- Internal reuse of the existing Sylow-center movement proof in this triangle family.
import all CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.FaithfulJoinSp4
set_option Elab.async false

/-!
# The containing projective component centralizes the Sylow omega-center

If the original normalized local PSL₃(4) component moved Ω₁(Z(T)), its
intrinsic signalizer module would be nontrivial. A faithful maximal envelope
therefore inherits Hypothesis 12.2.3 and an actual chosen module. The proved
embedding catalogue leaves PSL₃(4), M₂₃, J₂ and J₄. The latter two surplus
rows can be excluded by the same completed B.5.1 comparison, without a
stronger embedding theorem. Orders exclude all natural rows except the
binary four-space possibility; the actual Sylow centers distinguish
PSL₃(4) from the equal-order PSL₄(2).

The preceding 7.0.1 alternatives force FF on the original chosen orbit.
The genuine 3.2.5 constituent list excludes its doubled alternative, so
that orbit equals its seed. B.5.1 on the unchanged full-normalizer
supplement then supplies the contradiction. All two-core quotient maps
and the original seed action are retained. Relative normality places the
original K in the local family, giving the literal point-normalizer
application without any common-normal witness.

OmegaCentralizationSp4 feeds this conclusion to the common-Q consumer.
The earlier source 7.0.1 and 3.2.5 implications remain explicit, with
producers qt-d-1222-normalized-nonff and qt-baumann-fsu and final discharge
by qt-d-1222-natural-local-geometry. Common-normal existence, the SL₃(4)
exclusion, both triangle orientations and original 11.1.1--3 assembly
remain with qt-d-1222-natural-relative-components.
Source: Aschbacher--Smith, 11.1.2, printed p.764, using A.3.12, B.4.2,
B.5.1, 1.2.9, 3.2.5 and 7.0.1.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open ChapterA.Section03.SourceEmbeddings
public noncomputable section

/-- The proved containing catalogue, including its still-unexcluded J₄ row. -/
@[expose] def OmegaEnvelopeModel (A : Type*) [Group A] : Prop :=
  Exceptional.IsModel A ∨ Nonempty (A ≃* Janko4.Model)

private def EnvelopeOrder (n : ℕ) : Prop :=
  n = 604800 ∨ n = 10200960 ∨ n = 20160 ∨ n = 86775571046077562880

private theorem envelope_order {A : Type*} [Group A] (hm : OmegaEnvelopeModel A) :
    EnvelopeOrder (Nat.card A) := by
  rcases hm with hm | hm
  · rcases hm.card with hc | hc | hc
    · exact .inl hc
    · exact .inr (.inl hc)
    · exact .inr (.inr (.inl hc))
  · obtain ⟨e⟩ := hm
    exact .inr (.inr (.inr ((Nat.card_congr e.toEquiv).trans Janko4.Cardinality.model_card)))

private theorem envelope_bound {n : ℕ} (h : EnvelopeOrder n) : n ≤ 86775571046077562880 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

private theorem envelope_not_small {n : ℕ} (h : EnvelopeOrder n) (hn : n < 20160) : False := by
  rcases h with h | h | h | h <;> omega

private theorem envelope_of_equiv {A B : Type*} [Group A] [Group B]
    (hm : OmegaEnvelopeModel B) (e : A ≃* B) : OmegaEnvelopeModel A := by
  rcases hm with h | h
  · exact .inl (h.of_equiv e)
  · obtain ⟨a⟩ := h
    exact .inr ⟨e.trans a⟩

private theorem envelope_not_binaryFour {A : Type*} [Group A]
    (hm : OmegaEnvelopeModel A) : ¬ ClassicalGroup.IsPSL A 4 2 := by
  rcases hm with h | h
  · exact h.not_binaryFour
  · obtain ⟨e⟩ := h
    rintro ⟨F,_,_,hF,⟨a⟩⟩
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF,←Nat.card_congr a.toEquiv,Nat.card_congr e.toEquiv,
      Janko4.Cardinality.model_card] at hc
    norm_num [Fin.prod_univ_succ] at hc

private theorem no_linearTwo_envelope_order (F : BinaryField)
    (h : EnvelopeOrder (Nat.card (SL(2,F.Carrier)))) : False := by
  have hc := envelope_bound h
  rw [Atlas.card_sl_two,F.card_eq] at hc
  have hb : F.degree ≤ 22 := by
    by_contra hn
    have hp : 8388608 ≤ 2^F.degree :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 23 ≤ F.degree by omega)
    have hh : 8388608 * (8388608^2-1) ≤ (2^F.degree) * ((2^F.degree)^2-1) := by gcongr
    omega
  rw [EnvelopeOrder,Atlas.card_sl_two,F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h

private theorem no_linearThree_envelope_order (F : BinaryField)
    (h : EnvelopeOrder (Nat.card (SL(3,F.Carrier)))) : False := by
  have hc := envelope_bound h
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq] at hc
  have hb : F.degree ≤ 8 := by
    by_contra hn
    have hp : 512 ≤ 2^F.degree :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 9 ≤ F.degree by omega)
    have hh : 512^3 * (512^3-1) * (512^2-1) ≤ (2^F.degree)^3 * ((2^F.degree)^3-1) * ((2^F.degree)^2-1) := by gcongr
    omega
  rw [EnvelopeOrder,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h

private theorem no_symplectic_envelope_order (F : BinaryField)
    (h : EnvelopeOrder (Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier))) : False := by
  have hc := envelope_bound h
  rw [Theory.SpecificGroups.SymplecticFour.card_sp,F.card_eq] at hc
  have hb : F.degree ≤ 6 := by
    by_contra hn
    have hp : 128 ≤ 2^F.degree :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ F.degree by omega)
    have hh : 128^4 * (128^2-1) * (128^4-1) ≤ (2^F.degree)^4 * ((2^F.degree)^2-1) * ((2^F.degree)^4-1) := by gcongr
    omega
  rw [EnvelopeOrder,Theory.SpecificGroups.SymplecticFour.card_sp,F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h

private theorem no_g2_envelope_order (F : BinaryField)
    (h : EnvelopeOrder (Nat.card (Atlas.G2.Model F.Carrier))) : False := by
  have hc := envelope_bound h
  rw [Atlas.G2.card_Model,F.card_eq] at hc
  have hb : F.degree ≤ 4 := by
    by_contra hn
    have hp : 32 ≤ 2^F.degree :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ F.degree by omega)
    have hh : 32^6 * (32^6-1) * (32^2-1) ≤ (2^F.degree)^6 * ((2^F.degree)^6-1) * ((2^F.degree)^2-1) := by gcongr
    omega
  rw [EnvelopeOrder,Atlas.G2.card_Model,F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h

private theorem no_binary_envelope {A : Type*} [Group A]
    (hm : OmegaEnvelopeModel A) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : A ≃* SL(n,ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact envelope_not_binaryFour hm
      ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e.trans Atlas.Order20160A8.sl4TwoEquivPSL⟩⟩
  · have hc := envelope_order hm
    have he : Nat.card SL(5,ZMod 2) = ∏ i : Fin 5, (2^5 - 2^i.val) := by
      rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 5).toEquiv,
        ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
      simp
    rw [EnvelopeOrder,Nat.card_congr e.toEquiv,he] at hc
    norm_num [Fin.prod_univ_succ] at hc

private theorem no_alternating_envelope {A : Type*} [Group A]
    (hm : OmegaEnvelopeModel A) {n : ℕ} (hn : 2 ≤ n) (hb : n ≤ 8)
    (e : A ≃* alternatingGroup (Fin n)) : False := by
  by_cases he : n = 8
  · subst n
    exact envelope_not_binaryFour hm
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
  · have hb' : n ≤ 7 := by omega
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    have hc := envelope_order hm
    rw [EnvelopeOrder,Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hc
    interval_cases n <;> norm_num [Nat.factorial] at hc

private theorem no_envelope_irreducible_case
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) P W) {L H : Subgroup P}
    (hm : OmegaEnvelopeModel L)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) : False := by
  have hc := envelope_order hm
  cases h with
  | linearTwo F _ e _ _ =>
    exact no_linearTwo_envelope_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
  | linearThree F _ e _ =>
    exact no_linearThree_envelope_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
  | symplectic F _ _ e _ =>
    exact no_symplectic_envelope_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
  | g2 F _ _ e _ _ =>
    exact no_g2_envelope_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
  | symplecticTwo e _ =>
    have hb := Nat.card_le_card_of_injective
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
    rw [←Nat.card_congr e.subgroupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hb
    exact envelope_not_small hc (by omega)
  | g2Two e _ _ =>
    have he := Nat.card_congr e.subgroupEquiv.toEquiv
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H] at he
    exact envelope_not_small hc (by omega)
  | symmetric n hn e _ _ =>
    exact no_alternating_envelope hm (by rcases hn with rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl <;> decide) e.subgroupEquiv
  | alternatingSix _ e _ _ =>
    exact no_alternating_envelope hm (by decide) (by decide) e.groupEquiv
  | alternatingSeven _ _ e _ _ _ =>
    exact no_alternating_envelope hm (by decide) (by decide) e
  | tripleSix _ a _ =>
    have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [Nat.card_congr a.quotientEquiv.toEquiv,Nat.card_congr a.centerEquiv.toEquiv,
      nat_card_alternatingGroup] at he
    norm_num [Nat.factorial,Nat.card_congr Multiplicative.toAdd] at he
    exact envelope_not_small hc (by omega)
  | binaryLinear n hn _ e _ => exact no_binary_envelope hm hn e.groupEquiv
  | orthogonalSix _ _ e _ _ =>
    exact no_alternating_envelope hm (by decide) (by decide) e.groupEquiv
  | symmetricEight _ e _ =>
    exact no_alternating_envelope hm (by decide) (by decide) e.subgroupEquiv
  | exteriorFive _ _ e _ _ _ => exact no_binary_envelope hm (.inr rfl) e

/-- The complete B.5.1 list has no row for any possible maximal envelope. -/
private theorem no_omega_envelope_source_case
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) P W) {L : Subgroup P} {s : MovedSection ρ L}
    (hm : OmegaEnvelopeModel L)
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) : False := by
  cases h with
  | irreducible _ _ _ h _ => exact no_envelope_irreducible_case _ hm h
  | doubleThree F _ e _ _ =>
    exact no_linearThree_envelope_order F
      ((Nat.card_congr e.groupEquiv.toEquiv) ▸ envelope_order hm)
  | naturalDual n hn _ hnat => exact no_binary_envelope hm hn hnat.some.groupEquiv
  | repeatedNatural n _ hn _ _ _ hnat => exact no_binary_envelope hm hn hnat.some.groupEquiv

open Chapter12.Section02
open ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification

private theorem envelope_simple {A : Type*} [Group A] [IsQuasisimple A]
    (hm : OmegaEnvelopeModel A) : IsSimpleGroup A := by
  rcases hm with hm | hm
  · exact hm.isSimple
  · obtain ⟨e⟩ := hm
    have hc : center A = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro x hx
      apply mem_bot.mpr
      apply e.injective
      have hz : e x ∈ center Janko4.Model := by
        apply mem_center_iff.mpr
        intro y
        obtain ⟨z,rfl⟩ := e.surjective y
        simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
      exact (mem_bot.mp (Janko4.model_center_eq_bot ▸ hz)).trans e.map_one.symm
    let := IsQuasisimple.simple (G := A)
    exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem no_envelope_constituent
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) P W) (hm : OmegaEnvelopeModel P)
    (h : Chapter3.Section02.ChosenSource325.ConstituentModel ρ) : False := by
  have hc := envelope_order hm
  rcases h with ⟨F,⟨e⟩⟩ | ⟨F,_,⟨e⟩⟩ | ⟨e⟩ | ⟨n,hn,⟨e⟩⟩ | ⟨σ,_,⟨e⟩⟩
  · exact no_linearThree_envelope_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
  · exact no_symplectic_envelope_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
  · exact no_alternating_envelope hm (by decide) (by decide) e.some.groupEquiv
  · exact no_binary_envelope hm hn e.groupEquiv
  · exact no_alternating_envelope hm (by decide) (by decide) e.groupEquiv

private theorem no_envelope_comparison
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : ChosenModule T I U)
    {H : Type*} [Group H] {ρ : Representation (ZMod 2) H D.space}
    {K : Subgroup H} (d : D.LiteralComparison ρ K)
    (hs : IsSimpleGroup (I ⧸ pCore 2 I))
    (hm : OmegaEnvelopeModel (I ⧸ pCore 2 I))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K) : False := by
  have hp : Function.Injective d.projection := by
    intro x y he
    apply D.quotientAction_injective hs
    exact (d.action x).symm.trans ((congrArg (fun k : K => ρ k) he).trans (d.action y))
  let e := MulEquiv.ofBijective d.projection ⟨hp,d.surjective⟩
  exact no_omega_envelope_source_case ρ (envelope_of_equiv hm e.symm) c.clause_one

/-- On the literal chosen orbit, the preceding source alternatives rule out
all four proved envelope models, including the surplus J₂ and J₄ rows. -/
theorem no_omega_envelope_of_source701325
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {J U : Subgroup G}
    (D : ChosenModule T J U) (h : Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (hm : OmegaEnvelopeModel (J ⧸ pCore 2 J))
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) : False := by
  let := h.quasisimple
  have hs := envelope_simple hm
  have hff : IsFFModule D.sourceOrbitNormalizerRepresentation := by
    rcases h701 with hff | ⟨n,hn,⟨m⟩⟩ | hj
    · exact hff
    · let : NeZero n := ⟨by omega⟩
      let F : BinaryField := {
        Carrier := OrthogonalFourMinus.FiniteModel.Field n
        degree := 2*n
        degree_pos := by omega
        card_eq := GaloisField.card 2 (2*n) (by omega) }
      have e := (orbitComponentEquiv D h.toHypothesis1221 hs).trans m.groupEquiv
      exact (no_linearTwo_envelope_order F ((Nat.card_congr e.toEquiv) ▸ envelope_order hm)).elim
    · exact (h.no_J4 hj).elim
  have hd : ¬ D.MarkedDoubled := by
    intro hd
    exact no_envelope_constituent D.seedComponentAction
      (envelope_of_equiv hm (quotientComponentEquiv D hs).symm) hd.2.1
  have hf := seed_ff_of_orbit_eq D (orbit_eq_seed_of_source325 D h325 hd) hff
  obtain ⟨A,_,hle,⟨c⟩⟩ := source_conclusion D h.toHypothesis1221 hf
  exact no_envelope_comparison D (D.normalizerOffenderComparison A hle) hs hm c

/-- Identify the field-independent PSL₃(4) quotient with the actual
exceptional carrier used by the containing-component catalogue. -/
theorem projective_four_exceptional_model {A : Type*} [Group A]
    (hm : ClassicalGroup.IsPSL A 3 4) : Exceptional.IsModel A := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let a : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  exact .inr (.inr ⟨e.trans (Atlas.fieldEquivPSL 3 a)⟩)

/-- A normalized local PSL₃(4) component centralizes the actual Sylow
omega-center. Only the original earlier source alternatives remain explicit. -/
theorem projective_four_local_centralizes_omega_of_source701325
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hK : K ∈ Chapter1.L G T) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives) :
    K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G) := by
  by_contra hc
  have hmove : ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (K : Set G) := by
    intro hz
    apply hc
    apply le_centralizer_iff.mpr
    rwa [←omegaCenterIn_eq_omegaOneAmbient]
  have hf := local_faithful_of_sylow_center_movement T
    (h.simpleQTKE.evenCharacteristic T) hK hTK hmove
  have hex := projective_four_exceptional_model hm
  have hr : 2 ≤ primeRank 3 K := hex.threeRank.trans
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup)
  obtain ⟨J,hKJ,_,hsource,W,⟨D_J⟩⟩ := exists_maximal_faithful_envelope h hK hf hTK hr
  have hmJ : OmegaEnvelopeModel (J ⧸ pCore 2 J) := by
    rcases Chapter1.Section02.exceptional_local_overcomponent_models_or_jankoFour
      h.simpleQTKE T hK hTK hsource.maximal_faithful.1.1 hKJ hex with he | hJ | hM | hJ4
    · exact .inl (he ▸ hex)
    · exact .inl (.inl hJ)
    · exact .inl (.inr (.inl hM))
    · exact .inr hJ4
  obtain ⟨h701,h325⟩ := hpre J W D_J hsource
  exact no_omega_envelope_of_source701325 D_J hsource hmJ h701 h325

/-- Apply the faithful-envelope contradiction to the original relatively
normal containing component in the point normalizer. No common Q is needed. -/
theorem first_projective_component_centralizes_omega_of_source701325
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V K : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives) :
    K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G) := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hjoin : K ⊔ (T : Subgroup G) ≤ normalizer (f.Vi 0 : Set G) :=
    sup_le hK.1.1 (f.invariant 0)
  have hlocal : K ∈ Chapter1.L G T := by
    refine ⟨hK.1.2.subgroupOf_of_le le_sup_left hjoin,
      ⟨T.subtype le_sup_right,?_⟩,?_⟩
    · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    · intro he
      apply f.V_ne_bot 0
      apply bot_unique
      have hUT : f.Vi 0 ≤ (T : Subgroup G) :=
        (D.centralQuotientPreimage_le _).trans D.le_sylow
      have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT)
        (hUT.trans (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)) hjoin
      exact he ▸ hcore
  exact projective_four_local_centralizes_omega_of_source701325 S.source hlocal hTK hm hpre

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
