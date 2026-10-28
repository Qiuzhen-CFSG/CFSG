module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.AmbientGroups
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels

/-!
# Transporting the actual six-point normalizer

The full ambient group acts on the original component moved space. Transport
that action through the marked local intertwiner. The embedded component
becomes the literal alternating image; its concrete normalizer is the literal
symmetric image. Thus the local LA action covers the ambient action image.
Its kernel is exactly C_G(L): faithfulness on LA proves one containment and
the scalar commutant proves the other. The same marking gives the index two
of the embedded component inside LA.

Both the natural module and the nonsplit augmentation core are supported.
No global fixed-space splitting or ambient group decomposition is assumed.
Source: Aschbacher–Smith, B.5.7, printed p.106, final paragraph.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v w
variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

private def ambientModelSpace {L A : Subgroup G} [L.Normal]
    (m : SymmetricMovedModel ρ L A) : Subrepresentation ρ where
  toSubmodule := m.sectionData.space.toSubmodule
  apply_mem_toSubmodule g v hv := by
    rw [model_space_eq ρ m] at hv ⊢
    exact (normalMoved ρ L).apply_mem_toSubmodule g hv

/-- A marked six-point action and its concrete normalizer provide the actual
local symmetric supplement, including its literal alternating index. -/
theorem marked_symmetric_supplement {L A : Subgroup G} [L.Normal]
    (m : SymmetricMovedModel ρ L A)
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) W)
    (hf : Function.Injective σ)
    (hn : normalizer (((Representation.asGroupHom (σ.comp (alternatingGroup (Fin 6)).subtype)).range) :
      Set (Module.End (ZMod 2) W)ˣ) = σ.asGroupHom.range)
    (e : MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A)) σ (alternatingGroup (Fin 6))) :
    (L ⊔ A) ⊔ centralizer (L : Set G) = ⊤ ∧
      Disjoint (L ⊔ A) (centralizer (L : Set G)) ∧
      L.relIndex (L ⊔ A) = 2 := by
  let H := L ⊔ A
  let C := centralizer (L : Set G)
  let U := ambientModelSpace ρ m
  let b := e.action.linearEquiv
  let f : H ≃* Equiv.Perm (Fin 6) := Subgroup.topEquiv.symm.trans e.action.groupEquiv
  let β : Representation (ZMod 2) G W := b.conjRingEquiv.toMonoidHom.comp U.toRepresentation
  let φ := β.asGroupHom
  have hφ (h : H) : φ h = σ.asGroupHom (f h) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := b.surjective w
    change b (U.toRepresentation h (b.symm (b v))) = σ (f h) (b v)
    rw [b.symm_apply_apply]
    exact e.action.intertwines ⟨h, mem_top _⟩ v
  have hfaith : Function.Injective (φ.comp H.subtype) := by
    intro a b hab
    apply f.injective
    apply hf
    have hh : σ.asGroupHom (f a) = σ.asGroupHom (f b) :=
      (hφ a).symm.trans (hab.trans (hφ b))
    exact congrArg Units.val hh
  have himH : H.map φ = σ.asGroupHom.range := by
    ext t
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨f ⟨h, hh⟩, (hφ ⟨h, hh⟩).symm⟩
    · rintro ⟨s, rfl⟩
      obtain ⟨h, rfl⟩ := f.surjective s
      exact ⟨h, h.property, hφ h⟩
  have hfl (l : L.subgroupOf H) : f l = (e.subgroupEquiv l : Equiv.Perm (Fin 6)) :=
    e.compatible l
  have himL : L.map φ = (Representation.asGroupHom (σ.comp (alternatingGroup (Fin 6)).subtype)).range := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      let ll : L.subgroupOf H := ⟨⟨l, (le_sup_left : L ≤ H) hl⟩, hl⟩
      refine ⟨e.subgroupEquiv ll, ?_⟩
      change σ.asGroupHom (e.subgroupEquiv ll) = φ l
      rw [← hfl ll, ← hφ ll]
    · rintro ⟨s, rfl⟩
      obtain ⟨l, rfl⟩ := e.subgroupEquiv.surjective s
      refine ⟨l.val.val, l.property, ?_⟩
      change φ l.val.val = σ.asGroupHom (e.subgroupEquiv l)
      rw [← hfl l, ← hφ l]
  have hker : φ.ker = C := by
    apply le_antisymm
    · intro g hg l hl
      have hconj : g * l * g⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem l hl g
      have he : (⟨g * l * g⁻¹, (le_sup_left : L ≤ H) hconj⟩ : H) = ⟨l, (le_sup_left : L ≤ H) hl⟩ := by
        apply hfaith
        change φ (g * l * g⁻¹) = φ l
        rw [map_mul, map_mul, map_inv, show φ g = 1 from hg]
        simp
      have he' := congrArg Subtype.val he
      have he'' := congrArg (fun x => x * g) he'
      simpa [mul_assoc] using he''.symm
    · intro g hg
      apply Units.ext
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := b.surjective w
      change b (U.toRepresentation g (b.symm (b v))) = b v
      rw [b.symm_apply_apply]
      apply congrArg b
      apply Subtype.ext
      exact centralizer_fixes_model ρ ConcreteModels.modelCommutants m
        ((model_space_eq ρ m) ▸ v.property) ⟨g, hg⟩
  have hcover : H ⊔ C = ⊤ := by
    have hr : φ.range ≤ H.map φ := by
      rw [himH, ← hn, ← himL]
      have hh := le_normalizer_map (H := L) φ
      rwa [normalizer_eq_top, ← MonoidHom.range_eq_map] at hh
    have he : H.map φ = φ.range := le_antisymm (map_le_range _ _) hr
    have hc := congrArg (fun T : Subgroup (Module.End (ZMod 2) W)ˣ => T.comap φ) he
    rw [comap_map_eq, hker, MonoidHom.comap_range_self] at hc
    exact hc
  have hd : Disjoint H C := by
    apply disjoint_def.mpr
    intro g hg hgc
    have he : (⟨g, hg⟩ : H) = 1 := by
      apply hfaith
      change φ g = φ 1
      rw [map_one]
      exact (show g ∈ φ.ker from hker.symm ▸ hgc)
    exact congrArg Subtype.val he
  have hmap : (L.subgroupOf H).map (f : H →* Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) := by
    ext s
    constructor
    · rintro ⟨l, hl, rfl⟩
      change f l ∈ alternatingGroup (Fin 6)
      rw [hfl ⟨l, hl⟩]
      exact (e.subgroupEquiv ⟨l, hl⟩).property
    · intro hs
      obtain ⟨l, hl⟩ := e.subgroupEquiv.surjective ⟨s, hs⟩
      exact ⟨l, l.property, (hfl l).trans (congrArg Subtype.val hl)⟩
  refine ⟨hcover, hd, ?_⟩
  change (L.subgroupOf H).index = 2
  rw [← index_map_equiv (L.subgroupOf H) f, hmap]
  exact alternatingGroup.index_eq_two

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
