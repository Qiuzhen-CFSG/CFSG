module

public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Offenders under equivariant identifications

Changing the acting group by an injection preserves subgroup ranks. An
intertwining linear equivalence identifies the fixed spaces and their literal
quotients, so it preserves the offender inequality. Restricting a best offender
to an overgroup preserves all of its subgroup weight comparisons.

For surjective maps of actors, conjugation by the linear equivalence identifies
the actual action images and transports the FF property. This supplies the
transport in Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.11, printed pp. 72–73, without assuming faithfulness of the original actors.
-/

public section

namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)

theorem fixedSpace_comp_map (f : G →* D) (A : Subgroup G) :
    fixedSpace (σ.comp f) A = fixedSpace σ (A.map f) := by
  ext v
  constructor
  · intro h
    rintro ⟨_, a, ha, rfl⟩
    exact h ⟨a, ha⟩
  · intro h a
    exact h ⟨f a, Subgroup.mem_map_of_mem f a.property⟩

theorem rank_map_injective (f : G →* D) (hf : Function.Injective f) (A : Subgroup G) :
    rank (A.map f) = rank A :=
  congrArg (Nat.log 2) (Nat.card_congr (A.equivMapOfInjective f hf).toEquiv).symm

theorem weight_comp_map (f : G →* D) (hf : Function.Injective f) (A : Subgroup G) :
    weight (σ.comp f) A = weight σ (A.map f) := by
  rw [weight, weight, fixedSpace_comp_map, rank_map_injective f hf]

theorem IsBestOffender.subgroupOf {A H : Subgroup G} (hA : IsBestOffender ρ A)
    (hAH : A ≤ H) : IsBestOffender (ρ.comp H.subtype) (A.subgroupOf H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  have hmap : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
  refine ⟨⟨?_, IsElementaryAbelian.subgroupOf hAH⟩, ?_⟩
  · intro hbot
    apply hA.1.1
    rw [← hmap, hbot, Subgroup.map_bot]
  · intro B hB
    rw [weight_comp_map ρ H.subtype H.subtype_injective,
      weight_comp_map ρ H.subtype H.subtype_injective, hmap]
    exact hA.2 _ (hmap ▸ Subgroup.map_mono hB)

theorem fixedSpace_map_equivariant (f : G →* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) (A : Subgroup G) :
    (fixedSpace ρ A).map E.toLinearMap = fixedSpace σ (A.map f) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩ ⟨_, a, ha, rfl⟩
    exact (hE a v).symm.trans (congrArg E (hv ⟨a, ha⟩))
  · intro hw
    refine ⟨E.symm w, ?_, E.apply_symm_apply w⟩
    intro a
    apply E.injective
    change E (ρ a (E.symm w)) = E (E.symm w)
    rw [hE, E.apply_symm_apply]
    exact hw ⟨f a, Subgroup.mem_map_of_mem f a.property⟩

theorem fixedCodim_map_equivariant (f : G →* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) (A : Subgroup G) :
    fixedCodim ρ A = fixedCodim σ (A.map f) :=
  (Submodule.Quotient.equiv _ _ E (fixedSpace_map_equivariant ρ σ f E hE A)).finrank_eq

theorem IsOffender.map_equivariant (f : G →* D) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup G} (hA : IsOffender ρ A) : IsOffender σ (A.map f) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.map f⟩, ?_⟩
  · intro hb
    apply hA.1.1
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hb
  · rw [← fixedCodim_map_equivariant ρ σ f E hE, rank_map_injective f hf]
    exact hA.2

theorem IsFFModule.map_equivariant (f : G →* D) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (h : IsFFModule ρ) : IsFFModule σ := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.map f, hA.map_equivariant ρ σ f hf E hE⟩

theorem image_isFFModule_of_equivariant (f : G →* D) (hf : Function.Surjective f)
    (E : W ≃ₗ[ZMod 2] V) (hE : ∀ g w, ρ g (E w) = E (σ (f g) w))
    (h : IsFFModule (imageRepresentation σ)) : IsFFModule (imageRepresentation ρ) := by
  let ψ := equivariantActionImageEquiv ρ σ f E hf hE
  apply h.map_equivariant (imageRepresentation σ) (imageRepresentation ρ)
    ψ.toMonoidHom ψ.injective E
  intro d w
  change E (d.val.val w) = E (d.val.val (E.symm (E w)))
  rw [E.symm_apply_apply]

end Representation.BinaryOffender
