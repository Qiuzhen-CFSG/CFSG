module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.Single
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.NaturalModels

/-!
# The whole faithful solvable factor action

The natural moved space is faithful when the two-core vanishes and the
residual lies in the offender subgroup. The offender centralizer fixes this
space, so it is trivial. On two factors, transitivity gives the full symmetric
two-group as permutation image; the order is therefore 72. The two actual
natural supports then identify the full action with O₄⁺(2), retaining every
original vector and actor. This is the solvable E.2.3/13.2.8(3) action step.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)
include d

omit [FiniteDimensional (ZMod 2) V] in
/-- The original offender centralizer is trivial, by faithfulness on moved vectors. -/
theorem centralizer_eq_bot_of_residual (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ) :
    centralizer (offenderSubgroup ρ : Set G) = ⊥ := by
  apply bot_unique
  intro c hc
  apply mem_bot.mpr
  apply d.naturalMovedAction_injective hf hcore hr
  rw [map_one]
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := d.naturalMovedCoordinates.surjective w
  rw [d.naturalMovedAction_coordinates,Module.End.one_apply]
  apply congrArg d.naturalMovedCoordinates
  apply Subtype.ext
  exact d.centralizer_fixes_moved c hc v.property

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Transitivity on two actual factors gives the full factor-permutation image. -/
theorem factorConjugation_surjective_of_two_transitive (hn : d.count = 2)
    (ht : ∀ i j, ∃ g : G, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    Function.Surjective d.factorConjugation := by
  intro p
  let i : Fin d.count := ⟨0,by omega⟩
  let j : Fin d.count := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; change 0 = 1 at this; omega
  have hall (k : Fin d.count) : k = i ∨ k = j := by
    have : k.val = 0 ∨ k.val = 1 := by omega
    exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  obtain ⟨g,hg⟩ := ht i (p i)
  have hi : d.factorConjugation g i = p i :=
    d.factor_injective ((d.factor_map_conj g i).symm.trans hg)
  refine ⟨g,Equiv.ext fun k => ?_⟩
  rcases hall k with rfl | rfl
  · exact hi
  · have hx : d.factorConjugation g j ≠ p i := by
      rw [← hi]
      exact fun h => hij ((d.factorConjugation g).injective h).symm
    have hy : p j ≠ p i := fun h => hij (p.injective h).symm
    rcases hall (d.factorConjugation g j) with h | h <;>
      rcases hall (p j) with h' | h'
    · exact h.trans h'.symm
    · rcases hall (p i) with hp | hp
      · exact (hx (h.trans hp.symm)).elim
      · exact (hy (h'.trans hp.symm)).elim
    · rcases hall (p i) with hp | hp
      · exact (hy (h'.trans hp.symm)).elim
      · exact (hx (h.trans hp.symm)).elim
    · exact h.trans h'.symm

omit [FiniteDimensional (ZMod 2) V] in
/-- The full paired actor has order72, rather than only containing two S₃ factors. -/
theorem actor_card_of_two_transitive (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hn : d.count = 2)
    (ht : ∀ i j, ∃ g : G, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    Nat.card G = 72 := by
  have h := d.card_of_full_factorConjugation (d.centralizer_eq_bot_of_residual hf hcore hr)
    (d.factorConjugation_surjective_of_two_transitive hn ht)
  simpa [hn] using h


omit [FiniteDimensional (ZMod 2) V] in
/-- The one-factor action is the full natural SL₂(2) action on the literal moved space. -/
theorem one_factor_moved_natural_coordinates (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hn : d.count = 1) :
    ∃ (c : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ g v, c ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v) =
        (e g).val.mulVec (c v) := by
  let c := d.naturalMovedCoordinates.trans (d.singleSpaceCoordinates hn)
  let e := MulEquiv.ofBijective (d.singleAmbientHom hn)
    ⟨d.singleAmbientHom_injective hf hcore hr hn,d.singleAmbientHom_surjective hn⟩
  refine ⟨c,e,fun g v => ?_⟩
  change c ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v) =
    (d.singleAmbientHom hn g).val.mulVec (c v)
  rw [d.singleAmbientHom_action]
  change d.singleSpaceCoordinates hn (d.naturalMovedCoordinates
      ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v)) =
    d.singleSpaceCoordinates hn (d.naturalMovedAction g
      ((d.singleSpaceCoordinates hn).symm (d.singleSpaceCoordinates hn (d.naturalMovedCoordinates v))))
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (d.singleSpaceCoordinates hn) (d.naturalMovedAction_coordinates g v).symm

/-- The literal paired moved space has the full natural O₄⁺(2) action. -/
theorem two_factor_moved_orthogonal_coordinates (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hn : d.count = 2)
    (ht : ∀ i j, ∃ g : G, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    ∃ (c : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (e : G ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      ∀ g v, c ((naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v) =
        (e g).val (c v) := by
  let W := subspaceCommutator ρ ⊤ (offenderSubgroup ρ)
  let σ := (naturalMovedSubrepresentation (ρ := ρ)).toRepresentation
  have hf' : Function.Injective σ := by
    intro g h he
    apply d.naturalMovedAction_injective hf hcore hr
    change d.naturalMovedCoordinates.conjRingEquiv (σ g) =
      d.naturalMovedCoordinates.conjRingEquiv (σ h)
    rw [he]
  let i : Fin d.count := ⟨0,by omega⟩
  let j : Fin d.count := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; change 0 = 1 at this; omega
  have hall (k : Fin d.count) : k = i ∨ k = j := by
    have : k.val = 0 ∨ k.val = 1 := by omega
    exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  let A := subspaceCommutator ρ ⊤ (d.factor i)
  let B := subspaceCommutator ρ ⊤ (d.factor j)
  have hAW : A ≤ W := (le_iSup (fun k => subspaceCommutator ρ ⊤ (d.factor k)) i).trans_eq d.iSup_support
  have hBW : B ≤ W := (le_iSup (fun k => subspaceCommutator ρ ⊤ (d.factor k)) j).trans_eq d.iSup_support
  have hsup : A ⊔ B = W := by
    apply le_antisymm (sup_le hAW hBW)
    change subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ≤ A ⊔ B
    rw [← d.iSup_support]
    exact iSup_le fun k => (hall k).elim (fun h => h ▸ le_sup_left) (fun h => h ▸ le_sup_right)
  let A' := A.comap W.subtype
  let B' := B.comap W.subtype
  have hAB : IsCompl A' B' := by
    constructor
    · rw [disjoint_iff]
      apply bot_unique
      intro v hv
      change v = 0
      apply Subtype.ext
      exact Submodule.disjoint_def.mp (d.supports_independent.pairwiseDisjoint hij) (v : V) hv.1 hv.2
    · apply codisjoint_iff.mpr
      apply top_unique
      intro v _
      obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp (hsup.ge v.property)
      exact Submodule.mem_sup.mpr ⟨⟨a,hAW ha⟩,ha,⟨b,hBW hb⟩,hb,Subtype.ext hab⟩
  have hAd : Module.finrank (ZMod 2) A' = 2 :=
    (Submodule.comapSubtypeEquivOfLe hAW).finrank_eq.trans (d.support_finrank i)
  have hBd : Module.finrank (ZMod 2) B' = 2 :=
    (Submodule.comapSubtypeEquivOfLe hBW).finrank_eq.trans (d.support_finrank j)
  have hforward (g : G) {v : W} (hv : v ∈ A' ∨ v ∈ B') :
      σ g v ∈ A' ∨ σ g v ∈ B' := by
    rcases hv with hv | hv
    · have h := d.action_mem_factor_support g i hv
      rcases hall (d.factorConjugation g i) with he | he
      · rw [he] at h
        exact Or.inl h
      · rw [he] at h
        exact Or.inr h
    · have h := d.action_mem_factor_support g j hv
      rcases hall (d.factorConjugation g j) with he | he
      · rw [he] at h
        exact Or.inl h
      · rw [he] at h
        exact Or.inr h
  apply Representation.BinaryTwoPlaneRecognition.exists_isometry_coordinates σ hf'
    (d.actor_card_of_two_transitive hf hcore hr hn ht) A' B' hAB hAd hBd
  intro g v
  constructor
  · intro hv
    have h := hforward g⁻¹ hv
    simp only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at h
    exact h
  · exact hforward g

end CFSG.Quasithin.ChapterB.SolvableFFFactors

namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual coordinates for the whole actor on its original offender moved space. -/
def SmallNaturalMovedAction (ρ : Representation (ZMod 2) G V) : Prop :=
  (∃ (c : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ g v, c ((SolvableFFFactors.naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v) =
        (e g).val.mulVec (c v)) ∨
  (∃ (c : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (e : G ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      ∀ g v, c ((SolvableFFFactors.naturalMovedSubrepresentation (ρ := ρ)).toRepresentation g v) =
        (e g).val (c v))

/-- One or two transitive original factors exhaust the whole natural actor. -/
theorem SolvableFFFactors.small_natural_moved_action [Finite G] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hr : pResidual 2 G ≤ offenderSubgroup ρ) (hc : d.count = 1 ∨ d.count = 2)
    (ht : ∀ i j, ∃ g : G, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    SmallNaturalMovedAction ρ := by
  rcases hc with hc | hc
  · exact Or.inl (d.one_factor_moved_natural_coordinates hf hcore hr hc)
  · exact Or.inr (d.two_factor_moved_orthogonal_coordinates hf hcore hr hc ht)
end CFSG.Quasithin.ChapterB

