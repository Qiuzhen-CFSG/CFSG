module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedNonfaithfulComplete

/-!
# Complete recognition for proper faithful marked constituents

A proper constituent is totally isotropic in the original nondegenerate
form. The source actor-dimension equality therefore gives dim I ≤ m+1.
The sharp component theorem identifies its normal orbit with one component.
Self-duality and the completed single-component carrier catalogue exclude
the binary linear and nonbinary classical rows at this stricter degree;
the permitted native small and exceptional rows give the original images.

All supporting model arguments and literal quotient transports are kept
with this consumer. The nonfaithful branch is already complete, so final
assembly now retains only the faithful whole-module case I = top. That
remaining source argument is an explicit premise, not asserted here.
Source: Aschbacher–Smith G.11.7 and 14.3.15, printed pp.366–368,994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
namespace MarkedProperModels
open ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic
open Chapter1.Section02.LocalModels
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {A L : Subgroup D} {m : ℕ}
  (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L L m)
  (hd : finrank (ZMod 2) V ≤ m+1)
  (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))))
include h hd
omit hd in
private theorem actor_rank : m ≤ primeRank 2 (MulAut L) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  exact h.toSetup.rank_le_automorphisms (by
    rw [normalizer_eq_top_iff.mpr h.normal_H]; exact le_top)

include hs in
private theorem not_linear_three_cover {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : SL(3,k) →* L) (hπ : Function.Surjective π) (hz : π.ker ≤ center SL(3,k))
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card k = 2^n) : False :=
  MarkedLinearThree.not_two_copy_linear_three h hs (by omega) π hπ hz n hn hcard

include hs in
private theorem not_linear_three {n : ℕ} (hn : 0 < n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ IsSL L 3 (2^n)) : False := by
  rcases model with model | model
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact not_linear_three_cover h hd hs (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, Matrix.PSL3.projection_ker]) hn hcard
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact not_linear_three_cover h hd hs e.symm.toMonoidHom e.symm.surjective
      (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le) hn hcard

private theorem not_rank_one {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSL L 2 (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  have hm := rank_one_module_alternatives h
    (e.trans (Theory.PSL2.sl2QuotientEquiv k).symm) n hn hcard
  have hactor := hm.1
  rcases hm.2 with ⟨hdeg,_,_⟩ | ⟨a,ha,hna,hdeg,_⟩ | ⟨hna,hdeg,_⟩ <;> omega

private theorem not_symplectic {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSp L 2 (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  let E := (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).trans
    (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hcard hn).symm
  let := ZMod.algebra k 2
  let σ := (ρ.comp L.subtype).comp E.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective _).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp E.symm.injective)
  have hm := actor_rank h
  rw [primeRank_equiv 2 (MulAut.congr E)] at hm
  have hr := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_automorphism_rank_le hcard hn
  have hdeg := SymplecticFourRecognition.Nonbinary.small_finrank hn hcard hf (by omega)
  change finrank (ZMod 2) V = 4*n at hdeg
  omega

private theorem not_g2 {n : ℕ} (hn : 2 ≤ n)
    (model : ClassificationModels.IsG2At L (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact G2Recognition.not_nonbinary_of_sharp_degree h (by omega)
    (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard).symm) hn hcard

include hs in
private theorem not_binary_linear {n : ℕ} (hn : n=4 ∨ n=5)
    (model : ClassicalGroup.IsPSL L n 2) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  rcases hn with rfl | rfl
  · let E := e.trans (Atlas.fieldEquivPSL 4 a)
    have hm := actor_rank h
    rw [primeRank_equiv 2 (MulAut.congr E)] at hm
    have hr := _root_.BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
    rcases BinaryLinearRecognition.four_alternatives h E with hnat | horth
    · exact (Representation.BinaryLinearRecognition.not_natural_degree_of_selfDual
        (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hs (by decide) E hnat.2.1).elim
    · omega
  · exact BinaryLinearRecognition.not_five_of_selfDual_sharp_degree h (by omega)
      hs (e.trans (Atlas.fieldEquivPSL 5 a))

omit h hd [Finite D] in
private theorem native_g2 (e : L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ComponentOrbitImageCases L L := Or.inl ⟨rfl,Or.inl ⟨e⟩⟩

omit h hd [Finite D] in
private theorem binary_symplectic (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    ComponentOrbitImageCases L L :=
  Or.inr (Or.inl (Or.inr ⟨e.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))⟩))

include hs in
private theorem odd_two {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (model : ClassicalGroup.IsPSL L 2 (p^e)) : ComponentOrbitImageCases L L := by
  let : IsQuasisimple L := h.component.2
  rcases ChapterG.Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hp ho he model
    h.single_component_degree_bound with hb | ht | he
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := hb
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
    exact Or.inr (Or.inl (Or.inl ⟨e.trans a⟩))
  · exact (not_linear_three h hd hs (n := 1) (by decide) (Or.inl (by simpa using ht))).elim
  · exact binary_symplectic he.some

omit hd in
private theorem odd_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree L p) :
    ComponentOrbitImageCases L L := by
  let : IsQuasisimple L := h.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨e,_⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hp ho model h.single_component_degree_bound
  exact native_g2 e.some

include hs in
private theorem alternating {n : ℕ} (hn : 5≤n ∧ n≤8)
    (e : L ≃* alternatingGroup (Fin n)) : ComponentOrbitImageCases L L := by
  obtain ⟨hnl,hnu⟩ := hn
  interval_cases n
  · exact Or.inr (Or.inl (Or.inl ⟨e⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨e⟩))
  · exact Or.inl ⟨rfl,Or.inr (Or.inl ⟨e⟩)⟩
  · apply (not_binary_linear h hd hs (n := 4) (Or.inl rfl) ?_).elim
    exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
      ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

private theorem rank_one (model : ClassificationModels.IsBenderModel L) : ComponentOrbitImageCases L L := by
  cases model with
  | linear n hn hm => exact (not_rank_one h hd hn hm).elim
  | unitary n hn hm =>
    obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
    exact (TwistedExclusions.not_unitary_three_positive_exponent h J (by omega) hcard hconj (Or.inr e)).elim
  | suzuki k hk e => exact (h.not_suzuki hk e.some).elim

include hs in
private theorem rank_two (model : RankTwoTheoremC L) : ComponentOrbitImageCases L L := by
  cases model with
  | linear n hn hm => exact (not_linear_three h hd hs hn (Or.inl hm)).elim
  | symplectic n hn hm => exact (not_symplectic h hd hn hm).elim
  | g2 n hn hm => exact (not_g2 h hd hn hm).elim
  | triality n hn hm => exact (TwistedExclusions.not_triality_positive_exponent h hn hm).elim
  | ree k hk hm =>
    obtain ⟨d,e⟩ := hm
    exact (TwistedExclusions.not_ree_of_local_block h hk d e.some).elim
  | symplectic_derived e =>
    exact Or.inr (Or.inl (Or.inr ⟨e.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩))
  | g2_derived e => exact native_g2 e.some
  | tits e => exact (TwistedExclusions.not_tits_of_source_component h e.some).elim

omit h hd in
private theorem simple_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S] :
    center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp ht)).elim

include hs in
private theorem simple_models (hsimple : IsSimpleGroup L) (model : TheoremCModel L) :
    ComponentOrbitImageCases L L := by
  let : IsSimpleGroup L := hsimple
  let : IsQuasisimple L := h.component.2
  let q : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq simple_center_eq_bot).trans QuotientGroup.quotientBot
  have hsharp : finrank (ZMod 2) V ≤ m+2 := by omega
  cases model with
  | alternating n hn e => exact alternating h hd hs hn e.some
  | linear_odd p e hp ho he _ hm => exact odd_two h hd hs hp ho (by rcases he with rfl | rfl <;> decide) hm
  | three_odd p hp ho unitary hm =>
    apply odd_three h hp ho
    cases unitary with
    | false => exact Or.inl hm
    | true => exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm => exact rank_one h hd hm
  | rank_two hm => exact rank_two h hd hs hm
  | binary_linear n hn hm => exact (not_binary_linear h hd hs hn hm).elim
  | sporadic name hne e =>
    cases name with
    | m11 => exact (h.not_m11_central_quotient (q.trans e.some)).elim
    | m12 => exact (h.not_m12_of_sharp_degree hsharp e.some).elim
    | m22 => exact (h.not_m22_of_sharp_degree hsharp e.some).elim
    | m23 => exact (h.not_m23_of_sharp_degree hsharp e.some).elim
    | m24 => exact (h.not_m24_of_sharp_degree hsharp e.some).elim
    | j2 => exact (h.not_janko_two_of_sharp_degree hsharp e.some).elim
    | j3 => exact (hne rfl).elim
    | j4 => exact (h.not_janko_four e.some).elim
    | hs => exact (h.not_higman_sims e.some).elim
    | he => exact (h.not_held e.some).elim
    | ru => exact (h.not_rudvalis e.some).elim
  | janko_one e => exact (h.not_j1_central_quotient (q.trans e.some)).elim

include hs in
private theorem cover_models (model : ThreeCoverModel L) : ComponentOrbitImageCases L L := by
  have hsharp : finrank (ZMod 2) V ≤ m+2 := by omega
  cases model with
  | classical unitary q hq hm =>
    cases unitary with
    | false =>
      change IsSL L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · exact (not_linear_three h hd hs hn (Or.inr hm)).elim
      · exact odd_three h hp ho (Or.inr (Or.inl hm))
    | true =>
      change IsSU L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
        exact (TwistedExclusions.not_unitary_three_positive_exponent h J hn hcard hconj (Or.inl e)).elim
      · exact odd_three h hp ho (Or.inr (Or.inr (Or.inr hm)))
  | alternating_six hm => exact (h.not_triple_alternating_six_of_sharp_degree hsharp hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | alternating_seven hm => exact (h.not_triple_alternating_seven hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | mathieu hm => exact (h.not_m22_central_quotient_of_sharp_degree hsharp hm.2.2.some).elim

include hs in
/-- A self-dual single component at the proper-constituent degree bound has
only permitted native image carriers. -/
private theorem imageCases_of_selfDual_strict_sharp_degree : ComponentOrbitImageCases L L := by
  rcases h.single_component_models with ⟨hi,hm⟩ | ⟨_,hm⟩
  · exact simple_models h hd hs hi hm
  · exact cover_models h hd hs hm
end MarkedProperModels

namespace MarkedSource
open Representation.BinaryOffender
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- Every proper faithful constituent gives the original full image cases. -/
theorem imageCases_of_actorFaithful_of_ne_top
    (hf : ActorFaithful (F := F) (g := g) (I := I)) (hi : I ≠ ⊤) : s.ImageCases := by
  have hsource := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem).2.2
  have hiso := hsource.2.resolve_right (fun h => hi h.1)
  have hisodim := B.twice_finrank_le_of_isotropic s.hypothesis.nondegenerate I hiso
  have hdim := s.actor_dimension
  have hHL := s.orbit_eq_component_of_actorFaithful_of_ne_top hf hi
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_actorFaithful hf
  have hs := MarkedAction.selfDual_image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes hsource.1
  dsimp only at hc hs
  rw [he] at hc hs
  change ComponentOrbitImageCases
    (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)
    (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes (componentOrbit L ⊤))
  rw [he]
  exact MarkedProperModels.imageCases_of_selfDual_strict_sharp_degree hc (by omega) hs

/-- The proper faithful branch supplies the actual intrinsic local lift. -/
theorem local_lift_of_actorFaithful_of_ne_top
    (hf : ActorFaithful (F := F) (g := g) (I := I)) (hi : I ≠ ⊤) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_actorFaithful_of_ne_top hf hi)

/-- The only remaining marked source recognition is faithful on the whole module. -/
theorem imageCases_of_whole_faithful_recognition
    (hwhole : ActorFaithful (F := F) (g := g) (I := I) → I = ⊤ →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases) : s.ImageCases := by
  by_cases hf : ActorFaithful (F := F) (g := g) (I := I)
  · by_cases hi : I = ⊤
    · exact hwhole hf hi s.fixedPointAlternative
    · exact s.imageCases_of_actorFaithful_of_ne_top hf hi
  · exact s.imageCases_of_not_actorFaithful hf

/-- Whole-module faithful recognition completes the original intrinsic local lift. -/
theorem local_lift_of_whole_faithful_recognition
    (hwhole : ActorFaithful (F := F) (g := g) (I := I) → I = ⊤ →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_faithful_recognition hwhole)
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
