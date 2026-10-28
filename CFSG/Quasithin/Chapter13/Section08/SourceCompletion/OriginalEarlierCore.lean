module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Ordinary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore

/-!
# Original ordinary plane-core identities on every Sylow flag

The Sylow action on the original natural A₆ module has a unique invariant
line and plane. Thus every flag quantified by the earlier 13.5.4 interface
has the same first two subgroups as the original flag. The original plane
noncentrality and its actual cubic residual action then give the normal
closure and two-core identities. The supplied set product identifies the
same subgroup, using the original relative normalizer in LT.

No module marking, flag identity, normal closure or centralizer identity is
assumed beyond the original natural setup and preceding plane noncentrality.
Source: Aschbacher--Smith B.3.4, 13.3.14--15 and 13.5.4,
printed pp.84--85,891--894,916.
-/

public section

open Subgroup BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open Section07.NaturalAction
open Section05.PlaneGeometry.TwoBlocks
open Section05.AmbientSource
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
open TransvectionParabolic.EarlierCore

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

private theorem stable_small_subgroup_eq
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    {A B : Subgroup G} (hA : A ≤ V) (hB : B ≤ V)
    (n : ℕ) (hn : n = 1 ∨ n = 2)
    (hcA : Nat.card A = 2 ^ n) (hcB : Nat.card B = 2 ^ n)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) : A = B := by
  let f := Section07.NaturalAction.permutation d
  let Q := (T.subtype (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right)).mapSurjective
    f.rangeRestrict_surjective
  have hQ : (Q : Subgroup f.range).map f.range.subtype =
      ((T : Subgroup G).subgroupOf (L ⊔ T)).map f := by
    rw [Sylow.coe_mapSurjective, map_map, Sylow.coe_subtype]
    rfl
  obtain ⟨g, hg⟩ := NaturalGeometry.exists_conjugate_T0_le
    f.range (alternating_le_range d) Q
  have stable (X : Subgroup G)
      (hX : (T : Subgroup G) ≤ normalizer (X : Set G)) :
      ∀ x ∈ T0.map (MulAut.conj g.val).toMonoidHom,
        move x (image d X) = image d X := by
    intro x hx
    have hmem := hg hx
    rw [hQ] at hmem
    exact (mem_stabilizer_iff_map _ _).mp (image_stable d X hX hmem)
  have ha := invariant_unique_conjugate T0 le_rfl g.val (image d A) (stable A hTA)
  have hb := invariant_unique_conjugate T0 le_rfl g.val (image d B) (stable B hTB)
  apply Section05.QuadraticSource.image_injective_on_subgroups d hA hB
  rcases hn with rfl | rfl
  · exact (ha.1 (image_dim d A hA 1 hcA)).trans
      (hb.1 (image_dim d B hB 1 hcB)).symm
  · exact (ha.2 (image_dim d A hA 2 hcA)).trans
      (hb.2 (image_dim d B hB 2 hcB)).symm

/-- The exact earlier 13.5.4 contract on the original natural module.
Every quantified flag uses the same Sylow-fixed line and plane, so the
proved plane-normalizer argument applies to its actual supplied product. -/
theorem original_earlier1354_of_ordinary_plane_noncentral
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2, V₂⁆ ≠ ⊥) : Earlier1354 T L V := by
  intro _ _ _ _ _ _ _ W₁ W₂ W₃ h12 h23 h3V hc1 hc2 _ ht1 ht2 _ I hI
  have hw1 : W₁ = V₁ := stable_small_subgroup_eq d
    (h12.trans (h23.trans h3V))
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
    1 (Or.inl rfl) hc1 d.line_card ht1 d.line_stable
  have hw2 : W₂ = V₂ := stable_small_subgroup_eq d
    (h23.trans h3V) (d.plane_le_seed.trans d.seed_le)
    2 (Or.inr rfl) hc2 d.plane_card ht2 d.plane_stable
  subst W₁
  subst W₂
  have hres := residual_relative_normalizer_eq L T V₂ T.isPGroup'
    d.normalizes_L d.plane_stable
  rw [hres] at hI
  have hQT : (normalizer (V₁ : Set G)).pCoreIn 2 ≤ T := by
    have hh := pCoreIn_le_sylow (normalizer (V₁ : Set G)) (T.subtype d.line_stable)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le d.line_stable] at hh
  have hn : (normalizer (V₁ : Set G)).pCoreIn 2 ≤
      normalizer (localResidual L V₂ : Set G) :=
    hQT.trans (normalizes_localResidual L T V₂ d.normalizes_L d.plane_stable)
  have hIj : I = localI L V₁ V₂ := SetLike.coe_injective
    (hI.trans (localI_coe_eq_product L V₁ V₂ hn).symm)
  subst I
  let := source_plane_isKleinFour d
  obtain ⟨hx, hk⟩ := Ordinary.planeActor_action_source d eL
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2, V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hc := plane_normalClosure T V₁ V₂ (planeActor (L := L) (V₂ := V₂))
    d.line_card d.line_le_plane d.line_stable d.plane_stable
    (planeActor_le.trans inf_le_right) (planeActor_normalized d)
    planeActor_twoPerfect hx hk hm'
  constructor
  · change (normalizer (V₁ : Set G)).pCoreIn 2 ⊔
        planeActor (L := L) (V₂ := V₂) = _
    exact (sup_comm _ _).trans hc.1.symm
  · change ((normalizer (V₁ : Set G)).pCoreIn 2 ⊔
        planeActor (L := L) (V₂ := V₂)) ⊓ centralizer (V₂ : Set G) =
      ((normalizer (V₁ : Set G)).pCoreIn 2 ⊔ planeActor (L := L) (V₂ := V₂)).pCoreIn 2
    rw [sup_comm]
    exact hc.2.2.1.symm

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
