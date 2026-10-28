module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesWholeExclusions
public import CFSG.Quasithin.ChapterG.Section11.WholeComponentCandidates
public import CFSG.Quasithin.ChapterG.Section11.WholeG2
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.SmallSymplecticNormalThree
public import Theory.Representation.Mathieu.M22James.MinimumDegree
public import Theory.Mathieu.M22.TripleCover.Recognition

/-!
# The remaining whole-component carriers for the original larger actor

Apply the genuine G.9 carrier catalogue to the literal component orbit. For
one component, the original invariant alternating form excludes every central
three-cover: binary linear and unitary covers fail their degree bounds, odd
signed-three and triple-A₆ covers have degree six and hence solvable symplectic
image, and triple-M₂₂ has minimum degree twelve but actor rank at most five.
The binary A₆ catalogue excludes that simple carrier. The A₇ automorphism
bound forces degree six and actor rank three, so the original terminal kernel
and empty-family sieve exclude its actual lifted quotient without recognizing
the module. The common low-displacement theorem excludes nonbinary G₂.

The single-component remainder is A₈, nonbinary Sp₄, G₂(2)′ or M₂₂, each
specified by an actual model isomorphism. A two-component orbit retains its
literal join, action comparison and genuine simple-central-quotient catalogue.
The numerical reduction and original component consumer retain both this
remainder and the exceptional marked S₈ action. Thus this is a source reduction,
not yet a proof of the degree alternatives. In the successful degree-six branch,
the equivalence still concerns the full dotted G₂(2).

Source: Aschbacher–Smith G.5.1, G.7.3, G.9.3 and G.11.7, printed
pp.342–343,348,353–356,366–368; 14.3.6 and 14.3.13–14, pp.991,993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11 ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic
open Chapter1.Section02.LocalModels
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

private theorem degree_le_twice_actor :
    finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have hm := s.half_degree_le_actor
  obtain ⟨n,hn⟩ := s.even_degree
  omega

variable {L : Subgroup F.TerminalHdot}
  (h9 : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
    (F.terminalDot (F.X g)) L L
    (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
include h9

/-- A normal cubic center cannot occur in a whole component of degree at most six. -/
theorem not_single_cubic_center_small
    (hc : Nat.card (center L) = 3) (hd : finrank (ZMod 2) (Additive F.Uhat) ≤ 6) : False := by
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  exact h9.component.isCComponent.not_isSolvable
    (SmallSymplecticNormalThree.isSolvable_of_normal_cubic
      (F.terminalRepresentation.comp L.subtype) (h9.faithful.comp L.subtype_injective)
      B s.hypothesis.alternating s.hypothesis.nondegenerate
      (fun a u w => s.hypothesis.preserves a u w) hd (center L) hc)

omit s [IsElementaryAbelian 2 (rankTwoSeed T M)] in
/-- The actual A₆ binary catalogue has no whole component above degree four
in the G.9 window. -/
theorem not_single_alternating_six (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (e : L ≃* alternatingGroup (Fin 6)) : False := by
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hr := AlternatingSixCover.alternating_six_automorphism_two_rank
  have hu := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  rcases BinaryAlternatingSix.alternating_degrees σ with h | h | h <;> omega

/-- The original actor has rank three on a whole A₇ component, so degree
six makes the lifted terminal kernel the two-core. The original empty-family
sieve then excludes the actual A₇ quotient, without module recognition. -/
theorem not_single_alternating_seven (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (e : L ≃* alternatingGroup (Fin 7)) : False := by
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  have hr := h9.toSetup.rank_le_automorphisms (L := L) (by
    rw [normalizer_eq_top_iff.mpr h9.normal_H]
    exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hb := ChapterG.Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
  have hu := s.degree_le_twice_actor
  have hd6 : finrank (ZMod 2) (Additive F.Uhat) = 6 := by omega
  have hm3 : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 := by omega
  obtain ⟨K,hKH,hlocal,hcomp,himage,_,hspan⟩ :=
    Recognition.terminal_component_lift s.simple F (by decide) L h9.component
  change F.terminalDot K = L at himage
  have hK : ComponentLift F g K :=
    ⟨hKH,hlocal,hcomp,himage.symm ▸ h9.component,himage.symm ▸ h9.noncentral,hspan⟩
  have hk := rankTwo_terminal_kernel_of_six_three
    (source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups
      s.seed_card (Classical.choice s.centralizer_quotient))
    F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis hd6 hm3
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) :=
    (hK.twoCoreQuotientEquivDot hk).trans ((MulEquiv.subgroupCongr himage).trans e)
  exact source_excluded_quotient_row_false s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient) s.not_model F g K hK
    (hK.eq_conjugateSpanBy_of_image_normal (himage.symm ▸ h9.normal_H))
    (Or.inr (Or.inl ⟨eK⟩))

/-- The genuine triple-A₆ cover has degree six; its cubic center contradicts
the invariant nondegenerate alternating form. -/
theorem not_single_triple_alternating_six (model : IsAlternatingCover L 6) : False := by
  let : IsQuasisimple L := h9.component.2
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  have hc : Nat.card (center L) = 3 :=
    (Nat.card_congr model.2.1.some.toEquiv).trans (by simp)
  have hd := AlternatingSixCover.small_degree_eq_six model.2.2.some hc
    (F.terminalRepresentation.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    h9.single_component_degree_bound
  exact s.not_single_cubic_center_small h9 hc hd.le

/-- The triple-M₂₂ minimum degree twelve exceeds twice the actual actor
rank, which is at most five by faithful conjugation on the central quotient. -/
theorem not_single_triple_mathieu (model : IsM22Cover L) : False := by
  let : IsQuasisimple L := h9.component.2
  have hr := TwistedExclusions.actor_rank_le_of_central_quotient h9 model.2.2.some
    Sporadic.Mathieu.m22_automorphism_twoRank_le_five
  have hc : Nat.card (center L) = 3 :=
    (Nat.card_congr model.2.1.some.toEquiv).trans (by simp)
  obtain ⟨e⟩ := Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv hc model.2.2
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hl := Sporadic.Mathieu.M22TripleCover.faithful_irreducible_finrank_ge_twelve σ
    (h9.faithful.comp (L.subtype_injective.comp e.symm.injective))
  have hu := s.degree_le_twice_actor
  omega

/-- Odd signed-three carriers have degree six, so a central cubic excludes
the whole cover in the original symplectic action. -/
private theorem not_single_odd_three_cover (hc : Nat.card (center L) = 3)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree L p) : False := by
  let : IsQuasisimple L := h9.component.2
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  obtain ⟨_,hd⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (F.terminalRepresentation.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho model h9.single_component_degree_bound
  exact s.not_single_cubic_center_small h9 hc hd.le

/-- Both signs and all source parameters of the classical central covers
are excluded on the actual whole component. -/
theorem not_single_classical_cover (hc : Nat.card (center L) = 3)
    (unitary : Bool) (q : ℕ) (hq : CoverParameter unitary q)
    (model : IsSLSign L unitary 3 q) : False := by
  cases unitary
  · change IsSL L 3 q at model
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
      let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
      exact MarkedLinearThree.not_single_component_linear_three h9
        (s.whole_restriction_selfDual L) e.symm.toMonoidHom e.symm.surjective
        (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le)
        n hn hcard
    · exact s.not_single_odd_three_cover h9 hc hp ho (.inr (.inl model))
  · change IsSU L 3 q at model
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · obtain ⟨k,_,_,J,hcard,hconj,e⟩ := model
      exact TwistedExclusions.not_unitary_three_positive_exponent h9 J hn hcard hconj (.inl e)
    · exact s.not_single_odd_three_cover h9 hc hp ho (.inr (.inr (.inr model)))

/-- All central-cover rows of the whole-component carrier sieve are impossible
for the original larger actor. -/
theorem not_single_cover (hc : Nat.card (center L) = 3)
    (model : WholeComponentCandidates.Cover L) : False := by
  rcases model with ⟨u,q,hq,hm⟩ | ha | hm
  · exact s.not_single_classical_cover h9 hc u q hq hm
  · exact s.not_single_triple_alternating_six h9 ha
  · exact s.not_single_triple_mathieu h9 hm

/-- The remaining simple whole-component carriers, with literal isomorphisms. -/
inductive RemainingWholeComponentModel (D : Type*) [Group D] : Prop
  | alternating_eight (e : Nonempty (D ≃* alternatingGroup (Fin 8)))
  | symplectic (n : ℕ) (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp D 2 (2^n))
  | binary_g2 (e : Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | mathieu (e : Nonempty (D ≃* Sporadic.Mathieu.M22))

/-- Recognition of the literal whole orbit retains a possible pair of distinct
components and the original quasiequivalence; no orbit equality is assumed. -/
@[expose] def RemainingWholeOrbit {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop :=
  (componentOrbit L ⊤ = L ∧ IsSimpleGroup L ∧ RemainingWholeComponentModel L) ∨
    ∃ L₂ : Subgroup D, IsComponent D L₂ ∧ L₂ ≠ L ∧ componentOrbit L ⊤ = L ⊔ L₂ ∧
      TwoComponents.FactorReduction.ModelRestrictions.QuotientModel (L ⧸ center L) ∧
      (Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
        Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))

private theorem not_single_alternating_five (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (e : L ≃* alternatingGroup (Fin 5)) : False := by
  let k := GaloisField 2 2
  have hc : Nat.card k = 4 := by
    change Nat.card (GaloisField 2 2) = 4
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact WholeRankOne.not_projective_binary_rank_one s.hypothesis h9 s.low_rank_witness hd
    (n := 2) (by decide) ⟨k,inferInstance,inferInstance,hc,⟨e.trans f.symm⟩⟩

private theorem whole_alternating_cases (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8) (e : L ≃* alternatingGroup (Fin n)) :
    RemainingWholeComponentModel L := by
  by_cases h5 : n = 5
  · exact (s.not_single_alternating_five h9 hd (h5 ▸ e)).elim
  by_cases h6 : n = 6
  · exact (not_single_alternating_six h9 hd (h6 ▸ e)).elim
  by_cases h7 : n = 7
  · exact (s.not_single_alternating_seven h9 hd (h7 ▸ e)).elim
  have h8 : n = 8 := by omega
  exact .alternating_eight ⟨h8 ▸ e⟩

private theorem not_single_odd_two (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    {p a : ℕ} (hp : p.Prime) (ho : Odd p) (ha : 0 < a)
    (model : ClassicalGroup.IsPSL L 2 (p^a)) : False := by
  let : IsQuasisimple L := h9.component.2
  rcases ChapterG.Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (F.terminalRepresentation.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho ha model h9.single_component_degree_bound with hb | ht | he
  · exact WholeRankOne.not_projective_binary_rank_one s.hypothesis h9 s.low_rank_witness hd
      (n := 2) (by decide) hb
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := ht
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (f := 1) (by simpa using hcard)
    exact MarkedLinearThree.not_single_component_linear_three h9
      (s.whole_restriction_selfDual L) (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,Matrix.PSL3.projection_ker])
      1 (by decide) (by simpa using hcard)
  · exact not_single_alternating_six h9 hd (he.some.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))

omit s [IsElementaryAbelian 2 (rankTwoSeed T M)] in
private theorem whole_odd_three_cases {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree L p) :
    RemainingWholeComponentModel L := by
  let : IsQuasisimple L := h9.component.2
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  obtain ⟨e,_⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (F.terminalRepresentation.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho model h9.single_component_degree_bound
  exact .binary_g2 e

private theorem whole_rank_two_cases (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (model : WholeComponentCandidates.RankTwo L) : RemainingWholeComponentModel L := by
  rcases model with ⟨n,hn,hm⟩ | ⟨n,hn,hm⟩ | ⟨n,hn,hm⟩ | he | he
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := hm
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact (MarkedLinearThree.not_single_component_linear_three h9
      (s.whole_restriction_selfDual L) (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,Matrix.PSL3.projection_ker])
      n hn hcard).elim
  · exact .symplectic n hn hm
  · exact (WholeG2.not_nonbinary_model s.hypothesis h9 s.low_rank_witness hn hm).elim
  · exact (not_single_alternating_six h9 hd (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
  · exact .binary_g2 he

omit s h9 [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))] in
private theorem whole_binary_four_cases (model : ClassicalGroup.IsPSL L 4 2) :
    RemainingWholeComponentModel L := by
  obtain ⟨k,_,_,hc,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc)
  exact .alternating_eight
    ⟨(e.trans (Atlas.fieldEquivPSL 4 a)).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm⟩

omit h9 in
/-- The original larger actor leaves only A₈, nonbinary Sp₄, binary
G₂′, and M₂₂ on a single whole component. In particular every cover is gone. -/
theorem whole_single_models
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
      (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L)
    (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat)) :
    IsSimpleGroup L ∧ RemainingWholeComponentModel L := by
  have h : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
      (F.terminalDot (F.X g)) L L
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by simpa only [hHL] using h9
  rcases WholeComponentCandidates.single_component_candidates s.hypothesis h s.low_rank_witness
      hd s.degree_le_twice_actor with ⟨hi,hm⟩ | ⟨hc,hm⟩
  · refine ⟨hi,?_⟩
    rcases hm with ⟨n,hn,e⟩ | ⟨p,a,hp,ho,ha,_,hm⟩ | ⟨p,hp,ho,u,hm⟩ | hm | hm | hm | hm
    · exact s.whole_alternating_cases h hd hn e.some
    · exact (s.not_single_odd_two h hd hp ho (by rcases ha with rfl | rfl <;> decide) hm).elim
    · apply whole_odd_three_cases h hp ho
      cases u with
      | false => exact .inl hm
      | true => exact .inr (.inr (.inl hm))
    · exact s.whole_rank_two_cases h hd hm
    · exact whole_binary_four_cases hm
    · exact .mathieu hm
    · exact (s.not_whole_janko_two h9 hHL hm.some).elim
  · exact (s.not_single_cover h ((Nat.card_congr hc.some.toEquiv).trans (by simp)) hm).elim

omit h9 in
/-- Keep the original orbit equality separate from the carrier classification.
The second branch is the actual two-component orbit with its action comparison. -/
theorem whole_orbit_models
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
      (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat)) :
    RemainingWholeOrbit F.terminalRepresentation L := by
  by_cases hHL : componentOrbit L ⊤ = L
  · exact .inl ⟨hHL,s.whole_single_models h9 hHL hd⟩
  · rcases h9.components with he | ⟨L₂,hL₂,he,hcomp⟩
    · exact (hHL he).elim
    · have hne : L₂ ≠ L := fun hh => hHL (by simpa only [hh,sup_idem] using he)
      obtain ⟨e⟩ : Nonempty (L ≃* L₂) := by
        rcases hcomp with ⟨e,_,_⟩ | ⟨e,_,_⟩ <;> exact ⟨e⟩
      have hmodel := TwoComponents.FactorReduction.ModelRestrictions.source_quotient_models_knownSimple
        h9 hL₂ he (Ne.symm hne) e
      exact .inr ⟨L₂,hL₂,hne,he,hmodel,hcomp⟩

omit h9 in
/-- The source numerical reduction with all single-component covers removed
and the simple carriers reduced. The marked S₈ action and the paired whole
orbit remain explicit source obligations. -/
theorem degree_cases_or_full_four_or_whole_models :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          RemainingWholeOrbit F.terminalRepresentation L) := by
  rcases s.degree_cases_or_full_four_or_whole with hd | hf | ⟨hd,L,hL,hm,ho,h9⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr ⟨hd,L,hL,hm,ho,h9,
      s.whole_orbit_models h9 hd⟩)

omit h9 in
/-- Apply the refined numerical alternatives to the actual component consumer.
The successful degree-six branch still identifies the full dotted G₂(2). -/
theorem component_or_full_four_or_whole_models
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          RemainingWholeOrbit F.terminalRepresentation L) := by
  rcases s.degree_cases_or_full_four_or_whole_models with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
