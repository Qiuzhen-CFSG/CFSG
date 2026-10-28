module
public import Theory.Representation.G2LargeActors
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeJankoTwo

/-!
# The complete whole marked G₂ row

Natural-module recognition in the original G.9 degree window gives degree
6n. The marked actor identity forces rank 3n-1, so genuine conjugation makes
the actor linear over the natural coefficient field. The original marked
coefficient bound excludes every n≥2. At n=1 the actual derived carrier is
the permitted binary G₂ component. The last adapters apply these results to
the literal original constituent image and local component lift.

Source: Aschbacher–Smith G.9.3(10), G.11.7 and 14.3.15, pp.354,367–368,994.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s
open ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic.G2Recognition
attribute [local instance] ZMod.algebra

/-- A whole nonbinary natural G₂ component contradicts the original marked
coefficient bound; the actor's conjugation is proved inner from its size. -/
theorem not_whole_g2_natural
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card k = 2^n)
    (hnat : Quasiequivalent (F.terminalRepresentation.comp L.subtype) (naturalBinary k)) : False := by
  let : L.Normal := hHL ▸ componentOrbit_top_normal L
  have hI := s.selected.isIrrPlus
  have hfix := s.fixedSpace_eq_bot
  rw [hi,hHL] at hI
  rw [hHL] at hfix
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) :=
    component_irreducible_of_top_isIrrPlus F.terminalRepresentation L hI hfix
  have hdim := degree_of_natural hcard hnat
  have hd := s.actor_dimension
  obtain ⟨e,c,hc⟩ := hnat
  let : Module k (Additive F.Uhat) := Representation.SymplecticFixedLine.coordinateModule c
  have hsmul (a : k) (w : Additive F.Uhat) : c (a • w) = a • c w := c.apply_symm_apply _
  let : SMulCommClass k (ZMod 2) (Additive F.Uhat) := ⟨fun a b w => by
    apply c.injective
    simp only [hsmul,c.map_smul,smul_comm a b]⟩
  let : IsScalarTower (ZMod 2) k (Additive F.Uhat) :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      apply c.injective
      rw [hsmul,c.map_smul]
      exact IsScalarTower.algebraMap_smul k a (c w))
  have hH : ∀ (l : L) (a : k) (w : Additive F.Uhat),
      F.terminalRepresentation l (a • w) = a • F.terminalRepresentation l w := by
    intro l a w
    apply c.injective
    change c ((F.terminalRepresentation.comp L.subtype) l (a • w)) =
      c (a • (F.terminalRepresentation.comp L.subtype) l w)
    rw [hc,hsmul,hsmul,hc]
    exact (Atlas.G2.Natural.action k (e l)).map_smul a (c w)
  have hA : 2^(3*n-1) ≤ Nat.card (F.terminalDot (F.X g)) := by
    have heq : Nat.card (F.terminalDot (F.X g)) =
        2 ^ Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
      rw [← Nat.card_congr (Additive.toMul (α := F.terminalDot (F.X g)))]
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (F.terminalDot (F.X g))))
    rw [heq]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hlin := Representation.G2LargeActors.coefficient_linear F.terminalRepresentation L
    (F.terminalDot (F.X g)) s.hypothesis.faithful e hn hcard hA hH
  have hb := s.coefficient_card_le_two_of_actor_linear (k := k) (by omega) hlin
  rw [hcard] at hb
  have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  omega

/-- The actual whole G₂ carrier is recognized on its natural module in the
original degree window, so every nonbinary parameter is impossible. -/
theorem not_whole_nonbinary_g2
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* Atlas.G2.Model k) {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) : False := by
  subst I
  have hf : ActorFaithful (F := F) (g := g) (I := ⊤) := by
    by_contra hnf
    exact s.constituent_ne_top_of_not_actorFaithful hnf rfl
  have hc := s.componentHypothesis_of_actorFaithful hf
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) ⊤ s.selected.invariant s.actor_stabilizes) hHL
  dsimp only at hc
  rw [he] at hc
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) ⊤ s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) ⊤ s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  let E := eL.symm.trans e
  let ρ := kerRepresentation (MarkedAction.action F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) ⊤ s.selected.invariant s.actor_stabilizes)
  let σ := (ρ.comp (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) ⊤ s.selected.invariant s.actor_stabilizes L).subtype).comp E.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective _).mpr hc.irreducible
  have hσ : Function.Injective σ := hc.faithful.comp (Subtype.val_injective.comp E.symm.injective)
  have hw := actor_bound_of_model_rank hc E
    (Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le k hn hcard)
  obtain ⟨_,t,l,ht,_,hnt,hdim,hne,hbasic,hnatural⟩ :=
    Nonbinary.exists_basic_parameters_and_natural σ hn hcard hσ
  have hp := small_orbit_parameters (by omega : 0<n) ht
    ((basic_product_alternatives l hbasic).resolve_left hne) hnt hdim hw.2
  obtain ⟨e',c,hc'⟩ := hnatural hp.2.1 hp.2.2.1
  let d := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) (Additive F.Uhat)) ≃ₗ[ZMod 2] _).symm.trans c
  apply s.not_whole_g2_natural rfl hHL hn hcard
  refine ⟨eL.trans (E.trans e'),d,?_⟩
  intro l w
  have hh := hc' (E (eL l)) ⟨w,Submodule.mem_top⟩
  have hact : ρ (eL l) ⟨w,Submodule.mem_top⟩ =
      ⟨F.terminalRepresentation l w,Submodule.mem_top⟩ := by rfl
  change c ⟨F.terminalRepresentation l w,Submodule.mem_top⟩ =
    naturalBinary k (e' (E (eL l))) (c ⟨w,Submodule.mem_top⟩)
  simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,E.symm_apply_apply,Subgroup.coe_subtype,hact] using hh

/-- The genuine derived G₂ carrier gives the permitted original image only
at the binary endpoint. -/
theorem imageCases_of_whole_g2
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* commutator (Atlas.G2.Model k))
    (n : ℕ) (hn : 0<n) (hcard : Nat.card k = 2^n) : s.ImageCases := by
  by_cases hn1 : n=1
  · have hk2 : Nat.card k = 2 := by simpa [hn1] using hcard
    let a := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv hk2)
    let f : commutator (Atlas.G2.Model k) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
      (a.subgroupMap _).trans (MulEquiv.subgroupCongr (by
        rw [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective,commutator_def]))
    let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
      (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
    exact Or.inl ⟨congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL,
      Or.inl ⟨eL.symm.trans (e.trans f)⟩⟩
  · exact (s.not_whole_nonbinary_g2 hi hHL
      (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard)) (by omega) hcard).elim

/-- The whole G₂ family feeds the literal original local lift. -/
theorem local_lift_of_whole_g2
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* commutator (Atlas.G2.Model k))
    (n : ℕ) (hn : 0<n) (hcard : Nat.card k = 2^n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_g2 hi hHL e n hn hcard)
/-- The full nonbinary model predicate is excluded with its actual field witness. -/
theorem not_whole_full_g2
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 2 ≤ n) (model : ClassificationModels.IsG2At L (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact s.not_whole_nonbinary_g2 hi hHL e hn hcard

/-- The excluded full G₂ row closes the literal local-lift consumer. -/
theorem local_lift_of_whole_full_g2
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 2 ≤ n) (model : ClassificationModels.IsG2At L (2^n)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_full_g2 hi hHL hn model).elim

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
