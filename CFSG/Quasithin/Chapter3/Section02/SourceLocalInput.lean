module

public import CFSG.Quasithin.ChapterD.Section03.InternalRestriction
public import CFSG.Quasithin.Chapter3.Section02.InternalFromReducedSeed

/-!
# The original reduced seed inside X T

Restrict either original actor alternative from M to X T, preserving its
literal Sylow subgroup, two-core quotient and conjugation action. The SQTK
property and the two-residual hypothesis descend through the canonical
subgroup copies. Reducedness gives the normal actor's trivial action
two-core, while the whole two-core fixes the original seed. Thus the
internal hypotheses of D.3.2 hold on the original reduced module of X T.

This supplies the local input for Lemma 3.2.2(8) under both source actor
alternatives, without assuming an action-image or invariance conclusion.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 3.2.2, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]

include hXM

/-- The original reduced seed satisfies D.3.2 already in X T, with either actor alternative. -/
theorem source_reduced_seed_local_internal
    (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
    (hX : pResidual 2 (X.subgroupOf M) = ⊤)
    (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
      (by rw [normalizer_eq_top]; exact le_top))
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
    (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
      (X.subgroupOf (X ⊔ (T : Subgroup G))) I) :
    InternalModuleHypotheses K (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
      (T.subtype le_sup_right) (X.subgroupOf (X ⊔ (T : Subgroup G))) I := by
  let A := X ⊔ (T : Subgroup G)
  have hAM : A ≤ M := sup_le hXM hTM
  have hXA : X ≤ A := le_sup_left
  have hTA : (T : Subgroup G) ≤ A := le_sup_right
  have hNM : M ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXM).mp inferInstance
  let : (X.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer (hAM.trans hNM)
  have hSQ := (hG.twoLocal_sqtk hM.1).subgroup (A.subgroupOf M)
  have hSA : IsSQTK K A := (IsSQTK.equiv (subgroupOfEquivOfLe hAM)).mp hSQ
  let eX := (subgroupOfEquivOfLe hXM).trans (subgroupOfEquivOfLe hXA).symm
  have hpX : pResidual 2 (X.subgroupOf A) = ⊤ := (pResidual_eq_top_iff _ _).mpr
    (((pResidual_eq_top_iff _ _).mp hX).of_surjective eX.toMonoidHom eX.surjective)
  have hS : ((T.subtype hTM : Sylow 2 M) : Subgroup M) ≤ A.subgroupOf M :=
    fun _ ht => hTA ht
  have hY : X.subgroupOf M ≤ A.subgroupOf M := fun _ hx => hXA hx
  have hi := hc.subgroupOf (A.subgroupOf M) hS hY
    (by rw [normalizer_eq_top]; exact le_top)
  let e := subgroupOfEquivOfLe hAM
  have heX : ((X.subgroupOf M).subgroupOf (A.subgroupOf M)).map e.toMonoidHom =
      X.subgroupOf A := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨⟨⟨a, hAM a.property⟩, a.property⟩, ha, rfl⟩
  have heT : ((T.subtype hTM).subtype hS).mapSurjective (f := e.toMonoidHom) e.surjective =
      T.subtype hTA := by
    apply Sylow.ext
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨⟨⟨a, hAM a.property⟩, a.property⟩, ha, rfl⟩
  have hcases : InternalActorCases (T.subtype hTA) (X.subgroupOf A)
      (by rw [normalizer_eq_top]; exact le_top) := by
    have hm := hi.map_equiv e (by rw [heX, normalizer_eq_top]; exact le_top)
    simpa only [heX, heT] using hm
  refine ⟨hSA, inferInstance, inferInstance, hpX, hcases,
    ReducedNormal.normal_actor_representation_twoCore_eq_bot A (X.subgroupOf A), hI, ?_⟩
  have hj : X.subgroupOf A ⊔ ((T.subtype hTA : Sylow 2 A) : Subgroup A) = ⊤ := by
    change X.subgroupOf A ⊔ (T : Subgroup G).subgroupOf A = ⊤
    rw [← subgroupOf_sup hXA hTA, subgroupOf_self]
  rw [hj]
  have he : (⊤ : Subgroup A).pCoreIn 2 = pCore 2 A := pCore_map_iso 2 topEquiv
  rw [he]
  exact ReducedNormal.representation_twoCore_stabilizes A I
end CFSG.Quasithin.Chapter3.Section02
