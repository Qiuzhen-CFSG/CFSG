module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalRecognition
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalSeven
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorMoved
public import Theory.Representation.PSL3Two.SmallSemisimple
public import Theory.Representation.SimpleHeadQuotient.Independent
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Binary containing actions without an original module marking

A fully moved binary SL₃(2)-module with zero invariants and dimension less
than six is irreducible: a nonzero kernel and a nontrivial simple head each
require at least three dimensions. The irreducible catalogue then identifies
it with the natural module or its graph twist. Applied to the original moved
subgroup, either marking contradicts the existing natural-three exclusion.

An exceptional A₇ section reconstructs an actual block. The block comparison
places the original moved subgroup inside VI, whose dimension is four. The
preceding small-module argument therefore excludes this action without first
assuming a marking of the original moved subgroup. The deleted A₇ action was
already excluded. Thus every prepared original action has an SL₄(2) or SL₅(2)
actor and the same two-core quotient of I.

Since [VI,I] = VI, the B.5.1 moved-module alternatives apply to the entire
literal VI, retaining the six/seven-dimensional central cover and all allowed
multiplicities. In particular VI has dimension at most twenty. These facts
reduce the remaining binary-three original-row recognition in Source; they
do not identify the full original moved subgroup with VI or the local seed.
Original binary-three and Suzuki row exhaustion remain with this owner.

Source: Aschbacher--Smith H.6.1 and B.5.1; the application is10.2.9,
printed pp.751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource

private theorem small_binary_irreducible
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (hf : ρ.invariants = ⊥) (hm : Coinvariants.ker ρ = ⊤)
    (hd : Module.finrank (ZMod 2) V < 6) : IsIrreducible ρ := by
  let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
  obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  have hn : ∃ g v, N.quotientRepresentation g v ≠ v := by
    by_contra! h
    have hc : Coinvariants.ker ρ ≤ N.toSubmodule := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      apply (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp
      change N.toSubmodule.mkQ (ρ g v - v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (h g (N.toSubmodule.mkQ v))
    exact hN.1 (Subrepresentation.toSubmodule_injective (top_unique (hm ▸ hc)))
  have hq : 3 ≤ Module.finrank (ZMod 2) (V ⧸ N.toSubmodule) := by
    rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial
      N.quotientRepresentation hn with h | h | h
    all_goals obtain ⟨e⟩ := h
    · rw [e.toLinearEquiv.finrank_eq]
      simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    · rw [e.toLinearEquiv.finrank_eq,Subspace.dual_finrank_eq]
      simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    · rw [e.toLinearEquiv.finrank_eq,BinaryLinearThree.finrank_steinberg]; decide
  have hz : N = ⊥ := by
    by_contra hz
    have hk := BinaryLinearThree.submodule_finrank_ge_three_of_invariants_eq_bot ρ hf N hz
    have he := N.toSubmodule.finrank_quotient_add_finrank
    omega
  exact isSimpleOrder_iff_isCoatom_bot.mpr (hz ▸ hN)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The original binary-three moved subgroup cannot have dimension less than six. Its zero fixed layer and full movement recover actual natural coordinates. -/
theorem Context.no_small_original_binary (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (hd : letI := source_original_full_moved_elementary D
      Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 6) : False := by
  let W := ⁅D.fullModule,L⁆
  let := source_original_full_moved_elementary D
  let : Nontrivial W := (nontrivial_iff_ne_bot _).mpr (source_full_moved_ne_bot D)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  obtain ⟨ρ,s,hs⟩ := BinaryConjugationSection.exists_of_central_kernel L W
    (source_full_moved_le_component D) (normalizer_commutator_ge_right _ _) q hq (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  have hm : Coinvariants.ker ρ = ⊤ := s.coinvariants_eq_top_of_group_generation L le_rfl
    ρ q (fun _ _ => rfl) (by rw [sup_bot_eq,commutator_comm]; exact source_full_moved_eq_commutator D)
  have hf : ρ.invariants = ⊥ := by
    apply bot_unique
    intro w hw
    apply Additive.toMul.injective
    apply Subtype.ext
    apply c.moved_fixed_eq_bot.le
    refine ⟨w.toMul.property,?_⟩
    intro l hl
    have hh := s.equivariant ⟨l,hl⟩ w.toMul
    rw [hs,hs] at hh
    change Additive.ofMul _ = ρ (q ⟨l,hl⟩) w at hh
    rw [hw] at hh
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : Additive W => (z.toMul : G)) hh))
  let : IsIrreducible ρ := small_binary_irreducible ρ hf hm hd
  have hmove : ∃ g w, ρ g w ≠ w := by
    by_contra! h
    obtain ⟨w,hw⟩ := exists_ne (0 : Additive W)
    exact hw (hf.le (fun g => h g w))
  have hnat : Selection.BinaryThreeNatural D := by
    rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial ρ hmove with
      h | h | h
    all_goals obtain ⟨f⟩ := h
    · refine ⟨e,⟨?_⟩⟩
      change BinaryConjugationSection L W (sourceMovedFixed D) _
      rw [c.moved_fixed_eq_bot]
      exact s.relabel q f
    · let E := f.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm
      refine ⟨e.trans BinaryLinearThree.AutomorphismAction.graph,⟨?_⟩⟩
      change BinaryConjugationSection L W (sourceMovedFixed D) _
      rw [c.moved_fixed_eq_bot]
      exact s.relabel q E
    · have hh := f.toLinearEquiv.finrank_eq
      rw [BinaryLinearThree.finrank_steinberg] at hh
      change Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) = 8 at hh
      omega
  exact c.no_binaryThreeNatural hnat

/-- The exceptional A₇ section is impossible on the original action, with full moved-span containment proved from the reconstructed block. -/
theorem Context.no_original_seven_four_section (c : Context D t v I)
    (a : ActionFacts c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_E : (A.subgroupOf N) ≃* alternatingGroup (Fin 7)),
      IsIrreducible (s.action.comp (A.subgroupOf N).subtype) →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 → False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  let K := I.subgroupOf (pointJoin T v I)
  let : IsElementaryAbelian 2 (⁅U,K⁆ : Subgroup (pointJoin T v I)) :=
    IsElementaryAbelian.of_le (commutator_le_left U K)
  dsimp only
  intro N hAN s E hi hd
  have hm := (c.moved_four_dimensional_of_seven_section a N hAN s E hi hd).2
  obtain ⟨hb,⟨eI⟩⟩ := c.block_and_quotient_of_four_moved_action a
    ((subgroupOfEquivOfLe hAN).symm.trans E) hm
  obtain ⟨e⟩ := c.original_binary_three_quotient a
  have hne : ⁅U,K⁆ ≠ ⊥ := by
    intro hz
    have hc : Nat.card (⁅U,K⁆ : Subgroup (pointJoin T v I)) = 16 := by
      change Nat.card (Additive (⁅U,K⁆ : Subgroup (pointJoin T v I))) = 16
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hm]
      norm_num
    rw [hz,card_bot] at hc
    omega
  have hspan := c.moved_le_of_seven_block e eI hb hne
  have hu := (c.four_dimensional_of_seven_section hspan N hAN s E hi hd).2
  change Module.finrank (ZMod 2) (Additive U) = 4 at hu
  apply c.no_small_original_binary e
  let := source_original_full_moved_elementary D
  let j : (⁅D.fullModule,L⁆ : Subgroup G) →* U :=
    (subgroupOfEquivOfLe c.orbit_le_join).symm.toMonoidHom.comp (inclusion hspan)
  let f := j.toAdditive.toZModLinearMap 2
  have hfi : Function.Injective f :=
    (subgroupOfEquivOfLe c.orbit_le_join).symm.injective.comp (inclusion_injective hspan)
  have hle := LinearMap.finrank_le_finrank_of_injective hfi
  change Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
    Module.finrank (ZMod 2) (Additive U) at hle
  omega

/-- Every prepared original containing action has a binary-linear actor of degree four or five, retaining its complete B.5.1 conclusion. -/
theorem Context.original_binary_source_action (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
      BinaryOrSevenAction h.sectionData ∧
        ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let N := offenderSubgroup (action (internalModule D v I))
  have hAN : A ≤ N := a.classification.2.1
  let f : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe hAN).symm
  obtain ⟨h,hs⟩ := c.original_binary_or_seven_action a
  refine ⟨h,hs,?_⟩
  cases hs with
  | sevenFour _ hi E hd =>
    exact (c.no_original_seven_four_section a N hAN h.sectionData E hi hd).elim
  | sevenDeleted _ _ E =>
    exact (c.no_deletedSeven_source_section a h.sectionData ⟨E⟩).elim
  | linear d hd _ _ E => exact ⟨d,hd,⟨f.trans E.groupEquiv⟩⟩
  | orthogonalSix _ _ E => exact ⟨4,Or.inl rfl,
      ⟨((f.trans E.groupEquiv).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
        (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩⟩
  | symmetricEight _ _ E => exact ⟨4,Or.inl rfl,
      ⟨((f.trans E.subgroupEquiv).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
        (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩⟩
  | exteriorFive _ _ E _ => exact ⟨5,Or.inr rfl,⟨f.trans E⟩⟩
  | naturalDual d hd E => exact ⟨d,hd,⟨f.trans E.some.groupEquiv⟩⟩
  | repeatedNatural d _ hd _ _ E => exact ⟨d,hd,⟨f.trans E.some.groupEquiv⟩⟩

/-- No prepared original action has an A₇ actor, without any original moved-module marking. -/
theorem Context.no_original_seven_actor (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    ∀ _E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      alternatingGroup (Fin 7), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  intro E
  obtain ⟨_,_,d,hd,⟨f⟩⟩ := c.original_binary_source_action a
  have hc := Nat.card_congr (f.symm.trans E).toEquiv
  rw [_root_.BinaryLinear.card_SL,nat_card_alternatingGroup] at hc
  rcases hd with rfl | rfl <;>
    norm_num [_root_.BinaryLinear.order,Fin.prod_univ_succ,Nat.factorial] at hc

/-- The original containing component has actual two-core quotient SL₄(2) or SL₅(2). -/
theorem Context.original_containing_binary_quotient (c : Context D t v I) (a : ActionFacts c) :
    ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty ((I ⧸ pCore 2 I) ≃* SL(d,ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨_,_,d,hd,⟨E⟩⟩ := c.original_binary_source_action a
  exact ⟨d,hd,⟨c.binaryActorQuotient hd E⟩⟩

/-- The B.5.1 binary moved-module alternatives hold on all of the literal VI, with the original quotient action and fixed attachments retained. -/
theorem Context.original_binary_moved_rows (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ d, (d = 4 ∨ d = 5) ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
        h.sectionData.space.toSubmodule = ⊤ ∧
          SourceCompletion.BinaryActor.MovedCase h.sectionData d := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let N := offenderSubgroup (action (internalModule D v I))
  have hAN : A ≤ N := a.classification.2.1
  obtain ⟨h,_,d,hd,⟨E⟩⟩ := c.original_binary_source_action a
  refine ⟨d,hd,h,?_,SourceCompletion.BinaryActor.movedCase hd
    (SourceCompletion.BinaryActor.actionCase _ hd
      ((subgroupOfEquivOfLe hAN).trans E) h.clause_one)⟩
  rw [h.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
  exact c.fully_moved

/-- The original reduced orbit has at most twenty binary dimensions, including its central attachment. -/
theorem Context.original_orbit_finrank_le_twenty (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.elementary
    Module.finrank (ZMod 2) (Additive (internalModule D v I)) ≤ 20 := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  obtain ⟨d,hd,h,hs,hm⟩ := c.original_binary_moved_rows a
  let j : Additive U ≃ₗ[ZMod 2] h.sectionData.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict h.sectionData.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ he => congrArg Subtype.val he,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  rw [j.finrank_eq]
  cases hm with
  | natural E =>
    rw [E.linearEquiv.finrank_eq]
    change Module.finrank (ZMod 2) (Fin d → ZMod 2) ≤ 20
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
    omega
  | orthogonal _ _ _ dim => omega
  | exterior _ _ _ dim => omega
  | naturalDual hn =>
    obtain ⟨E⟩ := hn
    rw [E.linearEquiv.finrank_eq]
    change Module.finrank (ZMod 2)
      ((Fin d → ZMod 2) × Module.Dual (ZMod 2) (Fin d → ZMod 2)) ≤ 20
    rw [Module.finrank_prod,Subspace.dual_finrank_eq]
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
    omega
  | repeatedNatural r _ hr hn =>
    obtain ⟨E⟩ := hn
    rw [E.linearEquiv.finrank_eq]
    change Module.finrank (ZMod 2) (Fin r → Fin d → ZMod 2) ≤ 20
    simp only [Module.finrank_pi_fintype,Module.finrank_self,
      Fintype.card_fin,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
    rcases hd with rfl | rfl <;> omega

/-- An actual original binary-three quotient prepares the literal FF action,
without supplying any moved-module coordinates. -/
theorem Context.actionFacts_of_binary_three_quotient (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) : ActionFacts c := by
  apply c.actionFacts_of_three
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
  decide

end CFSG.Quasithin.Chapter10.PointControl.Constrained
