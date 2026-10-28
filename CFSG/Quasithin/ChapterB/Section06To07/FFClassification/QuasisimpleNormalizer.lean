module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FactorNormalizer
public import Theory.Representation.BinaryOffender.InvariantAction
/-!
# The original quasisimple moved section retains its normalizer action

The normalizer of the actual component preserves [V,L] and its L-fixed
subspace. Hence it acts on the same central quotient stored by B.5.1.
The comparison uses identity linear maps on these literal spaces and the
original component inclusion. In particular natural and repeated-natural
coordinates extend without forcing the component centralizer to act trivially.

Source: Aschbacher–Smith, B.5.1 and B.6.9, pp.99–103 and 116.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (Y : Subgroup G) (A : Subgroup Y)
  (s : MovedSection (ρ.comp Y.subtype) A)

/-- The whole normalizer preserves the original moved submodule. -/
noncomputable def sourceMovedNormalizerSpace :
    Subrepresentation (ρ.comp (normalizer (A.map Y.subtype : Set G)).subtype) where
  toSubmodule := s.space.toSubmodule
  apply_mem_toSubmodule g v hv := by
    have hm : s.space.toSubmodule = moved ρ (A.map Y.subtype) := by
      rw [s.space_eq]
      have hh := subspaceCommutator_map_embedding (ρ.comp Y.subtype) ρ Y.subtype
        (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl) A ⊤
      simpa only [Submodule.map_id] using hh
    rw [hm] at hv ⊢
    exact (subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer _ ⊤ (by intros; trivial)) le_rfl g.property v).2 hv

/-- The restriction to the original factor has exactly the original moved action. -/
noncomputable def sourceMovedNormalizerSpaceEquiv :
    ActionEquiv ((sourceMovedNormalizerSpace ρ Y A s).toRepresentation.comp
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype)
      (s.space.toRepresentation.comp A.subtype) where
  groupEquiv := sourceFactorNormalizerEquiv Y A
  linearEquiv := LinearEquiv.refl _ _
  intertwines a v := by
    apply Subtype.ext
    have ha : (((sourceFactorNormalizerEquiv Y A a : A) : Y) : G) =
        (a : normalizer (A.map Y.subtype : Set G)) := by
      exact congrArg Subtype.val ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply
        ((subgroupOfEquivOfLe (A.map Y.subtype).le_normalizer) a))
    change ρ (a : G) v = ρ (((sourceFactorNormalizerEquiv Y A a : A) : Y) : G) v
    rw [ha]

/-- The two literal fixed subspaces are equal under their original actor marks. -/
theorem sourceMovedNormalizer_fixed_eq :
    s.central.toSubmodule = fixedSpace (sourceMovedNormalizerSpace ρ Y A s).toRepresentation
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))) := by
  rw [s.central_eq]
  let e := sourceMovedNormalizerSpaceEquiv ρ Y A s
  ext v
  constructor
  · intro hv a
    exact (e.intertwines a v).trans (hv (sourceFactorNormalizerEquiv Y A a))
  · intro hv a
    obtain ⟨b,hb⟩ := (sourceFactorNormalizerEquiv Y A).surjective a
    have hh := (e.intertwines b v).symm.trans (hv b)
    change s.space.toRepresentation (sourceFactorNormalizerEquiv Y A b) v = v at hh
    rwa [hb] at hh

/-- The original fixed subspace is invariant under the full normalizer. -/
noncomputable def sourceMovedNormalizerCentral :
    Subrepresentation (sourceMovedNormalizerSpace ρ Y A s).toRepresentation where
  toSubmodule := s.central.toSubmodule
  apply_mem_toSubmodule g v hv := by
    rw [sourceMovedNormalizer_fixed_eq ρ Y A s] at hv ⊢
    exact (fixedSpace_stable_of_normal
      (sourceMovedNormalizerSpace ρ Y A s).toRepresentation
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))) (mem_top g) v).2 hv

/-- The normalizer acts on the literal B.5.1 central quotient. -/
noncomputable def sourceMovedNormalizerRepresentation :=
  (sourceMovedNormalizerCentral ρ Y A s).quotientRepresentation

/-- The same group mark and identity quotient coordinates retain the B.5.1 action. -/
noncomputable def sourceMovedNormalizerActionEquiv :
    ActionEquiv ((sourceMovedNormalizerRepresentation ρ Y A s).comp
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype)
      (s.action.comp A.subtype) where
  groupEquiv := sourceFactorNormalizerEquiv Y A
  linearEquiv := LinearEquiv.refl _ _
  intertwines a v := by
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      exact congrArg s.central.toSubmodule.mkQ
        ((sourceMovedNormalizerSpaceEquiv ρ Y A s).intertwines a v)


/-- Original B.5.1 natural coordinates extend to the literal normalizer quotient action. -/
theorem source_moved_normalizer_natural
    (F : BinaryField) (n : ℕ) (h : IsLinearNatural (s.action.comp A.subtype) F n) :
    IsLinearNatural ((sourceMovedNormalizerRepresentation ρ Y A s).comp
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype) F n := by
  obtain ⟨c⟩ := h
  let e := sourceMovedNormalizerActionEquiv ρ Y A s
  exact ⟨⟨e.groupEquiv.trans c.groupEquiv,e.linearEquiv.trans c.linearEquiv,
    fun a v => (congrArg c.linearEquiv (e.intertwines a v)).trans (c.intertwines _ _)⟩⟩

/-- Original doubled-natural coordinates extend on the identical moved space. -/
theorem source_moved_normalizer_repeated_natural
    (F : BinaryField) (n r : ℕ)
    (h : IsRepeatedLinearNatural (s.space.toRepresentation.comp A.subtype) F n r) :
    IsRepeatedLinearNatural ((sourceMovedNormalizerSpace ρ Y A s).toRepresentation.comp
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype) F n r := by
  obtain ⟨c⟩ := h
  let e := sourceMovedNormalizerSpaceEquiv ρ Y A s
  exact ⟨⟨e.groupEquiv.trans c.groupEquiv,e.linearEquiv.trans c.linearEquiv,
    fun a v => (congrArg c.linearEquiv (e.intertwines a v)).trans (c.intertwines _ _)⟩⟩
end CFSG.Quasithin.ChapterB
