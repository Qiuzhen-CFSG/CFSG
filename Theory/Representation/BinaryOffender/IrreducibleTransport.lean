module

public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Transport of irreducible sections along equivariant embeddings

For an injective equivariant linear map and a homomorphism of acting groups,
we identify the commutator subspaces and fixed subspaces. The resulting linear
equivalence is between the literal quotients by fixed vectors and intertwines
the induced actions. Surjectivity onto the image of the actor then transports
irreducibility, hence the concrete family `IsIrrPlus`.

Applied to the inclusion of a normal subgroup's fixed space and its action
image, this justifies the module replacement in Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.1.11, printed pp. 72–73.
-/

@[expose] public section

open Representation
namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
  (f : G →* D) (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
  (hact : ∀ g w, ρ g (e w) = e (σ (f g) w))

include hact
include he in
/-- Fixed vectors correspond under an injective equivariant embedding. -/
theorem embedding_mem_fixedSpace_iff (L : Subgroup G) (w : W) :
    e w ∈ fixedSpace ρ L ↔ w ∈ fixedSpace σ (L.map f) := by
  constructor
  · intro hw
    rintro ⟨d, l, hl, rfl⟩
    apply he
    change e (σ (f l) w) = e w
    rw [← hact]
    exact hw ⟨l, hl⟩
  · intro hw l
    change ρ l (e w) = e w
    rw [hact]
    exact congrArg e (hw ⟨f l, Subgroup.mem_map_of_mem f l.property⟩)

theorem map_subspace_invariant (L : Subgroup G) (I : Submodule (ZMod 2) W)
    (hI : L.map f ≤ subspaceStabilizer σ I) :
    L ≤ subspaceStabilizer ρ (I.map e) := by
  apply le_subspaceStabilizer
  rintro g hg _ ⟨w, hw, rfl⟩
  exact ⟨σ (f g) w, (hI (Subgroup.mem_map_of_mem f hg) w).2 hw, (hact g w).symm⟩

theorem fixedSubspace_map_equiv (L : Subgroup G) (I : Submodule (ZMod 2) W) :
    ((fixedSpace σ (L.map f)).comap I.subtype).map
      (Submodule.equivMapOfInjective e he I).toLinearMap =
    (fixedSpace ρ L).comap (I.map e).subtype := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro l
    change ρ l (e w) = e w
    rw [hact]
    exact congrArg e (hw ⟨f l, Subgroup.mem_map_of_mem f l.property⟩)
  · intro hv
    obtain ⟨w, rfl⟩ := (Submodule.equivMapOfInjective e he I).surjective v
    refine ⟨w, ?_, rfl⟩
    rintro ⟨d, l, hl, rfl⟩
    apply he
    change e (σ (f l) w) = e w
    rw [← hact]
    exact hv ⟨l, hl⟩

noncomputable def embeddedCentralQuotientEquiv (L : Subgroup G)
    (I : Submodule (ZMod 2) W) :
    centralQuotient σ (L.map f) I ≃ₗ[ZMod 2] centralQuotient ρ L (I.map e) :=
  Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective e he I)
    (fixedSubspace_map_equiv ρ σ f e he hact L I)

theorem subspaceCommutator_map_embedding (L : Subgroup G) (I : Submodule (ZMod 2) W) :
    subspaceCommutator ρ (I.map e) L = (subspaceCommutator σ I (L.map f)).map e := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨l, hl, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨σ (f l) w - w, Submodule.subset_span ⟨f l,
      Subgroup.mem_map_of_mem f hl, w, hw, rfl⟩, ?_⟩
    rw [map_sub, hact]
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro v ⟨_, ⟨l, hl, rfl⟩, w, hw, rfl⟩
    change e (σ (f l) w - w) ∈ subspaceCommutator ρ (I.map e) L
    rw [map_sub, ← hact]
    exact Submodule.subset_span ⟨l, hl, e w, ⟨w, hw, rfl⟩, rfl⟩

theorem embeddedCentralQuotientEquiv_intertwines (L : Subgroup G)
    (I : Submodule (ZMod 2) W) (hI : L.map f ≤ subspaceStabilizer σ I)
    (l : L) (v : centralQuotient σ (L.map f) I) :
    embeddedCentralQuotientEquiv ρ σ f e he hact L I
      (centralQuotientRepresentation σ (L.map f) I hI (f.subgroupMap L l) v) =
    centralQuotientRepresentation ρ L (I.map e)
      (map_subspace_invariant ρ σ f e hact L I hI) l
      (embeddedCentralQuotientEquiv ρ σ f e he hact L I v) := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact (hact l v).symm

omit hact in
private theorem irreducible_transport (E : W ≃ₗ[ZMod 2] V)
    (hf : Function.Surjective f)
    (hE : ∀ g w, ρ g (E w) = E (σ (f g) w))
    (hirr : IsIrreducible σ) : IsIrreducible ρ := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let : Nontrivial V := Function.Injective.nontrivial E.injective
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro S
  let T : Subrepresentation σ := ⟨S.toSubmodule.comap E.toLinearMap, by
    intro d w hw
    obtain ⟨g, rfl⟩ := hf d
    change E (σ (f g) w) ∈ S
    rw [← hE]
    exact S.apply_mem_toSubmodule g hw⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective E.surjective
    change T.toSubmodule = Submodule.comap E.toLinearMap ⊥
    rw [hb]
    ext w
    change w = 0 ↔ E w = 0
    exact E.map_eq_zero_iff.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective E.surjective
    change T.toSubmodule = Submodule.comap E.toLinearMap ⊤
    rw [ht]
    rfl

include he in
theorem IsIrrPlus.map_embedding (L : Subgroup G) (I : Submodule (ZMod 2) W)
    (hI : IsIrrPlus σ (L.map f) I) : IsIrrPlus ρ L (I.map e) := by
  obtain ⟨hst, hcomm, hirr⟩ := hI
  refine ⟨map_subspace_invariant ρ σ f e hact L I hst, ?_, ?_⟩
  · rw [subspaceCommutator_map_embedding ρ σ f e hact, hcomm]
  · apply irreducible_transport _ _ (f.subgroupMap L)
      (embeddedCentralQuotientEquiv ρ σ f e he hact L I)
      (f.subgroupMap_surjective L)
    · intro l v
      exact (embeddedCentralQuotientEquiv_intertwines ρ σ f e he hact L I hst l v).symm
    · exact hirr
end Representation.BinaryOffender


namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
  (f : G →* D) (E : W ≃ₗ[ZMod 2] V) (hf : Function.Surjective f)
  (hE : ∀ g w, ρ g (E w) = E (σ (f g) w))
include hE in
theorem conjugate_image_action (g : G) :
    Units.mapEquiv E.conjRingEquiv.toMulEquiv (σ.asGroupHom (f g)) = ρ.asGroupHom g := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  change E (σ (f g) (E.symm v)) = ρ g v
  rw [← hE, E.apply_symm_apply]

include hf hE in
theorem conjugate_action_image :
    σ.asGroupHom.range.map (Units.mapEquiv E.conjRingEquiv.toMulEquiv).toMonoidHom =
      ρ.asGroupHom.range := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    obtain ⟨g, rfl⟩ := hf d
    exact ⟨g, (conjugate_image_action ρ σ f E hE g).symm⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨σ.asGroupHom (f g), ⟨f g, rfl⟩, conjugate_image_action ρ σ f E hE g⟩

noncomputable def equivariantActionImageEquiv : σ.asGroupHom.range ≃* ρ.asGroupHom.range :=
  ((Units.mapEquiv E.conjRingEquiv.toMulEquiv).subgroupMap σ.asGroupHom.range).trans
    (MulEquiv.subgroupCongr (conjugate_action_image ρ σ f E hf hE))
end Representation.BinaryOffender
