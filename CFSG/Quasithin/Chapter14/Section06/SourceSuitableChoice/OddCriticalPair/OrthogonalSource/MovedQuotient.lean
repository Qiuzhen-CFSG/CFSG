module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Support
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalAction
public import Theory.Representation.BinaryGroupAction

/-!
# The literal moved quotient and its action

The quotient image of [U,H] is precisely the linear moved space in U/Z.
Restricting the original quotient map therefore gives a surjection onto that
space, with kernel Z intersect [U,H]. Its conjugation equation allows marked
wreath coordinates to lift to the original source orthogonal action.

Source: Aschbacher--Smith 14.6.13(1), printed pp.1031--1032.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.OrthogonalSource
open OddNormalizer Chapter15.Section03 Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

abbrev movedSpace (a : LocalQuotientAction H U Z) :=
  subspaceCommutator a.representation ⊤ ⊤

theorem movedSpace_invariant (a : LocalQuotientAction H U Z) :
    (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ subspaceStabilizer a.representation (movedSpace a) :=
  subspaceCommutator_invariant_normalizer a.representation
    (le_subspaceStabilizer a.representation ⊤ (by intros; trivial)) le_normalizer_of_normal

def movedRepresentation (a : LocalQuotientAction H U Z) :
    Representation (ZMod 2) (H ⧸ pCore 2 H) (movedSpace a) where
  toFun g := (a.representation g).restrict (fun {v} hv =>
    (movedSpace_invariant a (mem_top g) v).2 hv)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[instance_reducible] def movedAction (a : LocalQuotientAction H U Z) :
    MulDistribMulAction (H ⧸ pCore 2 H) (Multiplicative (movedSpace a)) :=
  Representation.BinaryGroupAction.action (movedRepresentation a)

theorem moved_image (a : LocalQuotientAction H U Z) :
    (⁅U,H⁆.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
      binarySubgroup (movedSpace a) := by
  have h := commutator_image_eq a.representation U U H a.normalizes le_rfl
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk' (Z.subgroupOf U))
    a.conjugation ⊤ (by
      rw [subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rfl)
  rwa [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h

theorem moved_le (a : LocalQuotientAction H U Z) : ⁅U,H⁆ ≤ U :=
  le_normalizer_iff_commutator_le_left.mp a.normalizes

/-- The original quotient map, restricted to the actual commutator group. -/
def movedMap (a : LocalQuotientAction H U Z) :
    (⁅U,H⁆ : Subgroup G) →* Multiplicative (movedSpace a) where
  toFun v := Multiplicative.ofAdd ⟨Additive.ofMul
    (QuotientGroup.mk' (Z.subgroupOf U) ⟨v,moved_le a v.property⟩), by
      change QuotientGroup.mk' (Z.subgroupOf U) ⟨v,moved_le a v.property⟩ ∈
        binarySubgroup (movedSpace a)
      rw [← moved_image a]
      exact mem_map_of_mem _ v.property⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg Additive.ofMul (map_one (QuotientGroup.mk' (Z.subgroupOf U)))
  map_mul' v w := by
    apply Subtype.ext
    exact congrArg Additive.ofMul (map_mul (QuotientGroup.mk' (Z.subgroupOf U))
      (⟨v,moved_le a v.property⟩ : U) (⟨w,moved_le a w.property⟩ : U))

theorem movedMap_surjective (a : LocalQuotientAction H U Z) :
    Function.Surjective (movedMap a) := by
  intro v
  have hv : v.toAdd.val.toMul ∈ binarySubgroup (movedSpace a) := v.toAdd.property
  rw [← moved_image a] at hv
  obtain ⟨u,hu,he⟩ := hv
  exact ⟨⟨u,hu⟩,Subtype.ext (congrArg Additive.ofMul he)⟩

theorem movedMap_kernel (a : LocalQuotientAction H U Z) :
    (movedMap a).ker = Z.subgroupOf ⁅U,H⁆ := by
  ext v
  change (movedMap a v = 1) ↔ (v : G) ∈ Z
  rw [show movedMap a v = 1 ↔
      QuotientGroup.mk' (Z.subgroupOf U) ⟨v,moved_le a v.property⟩ = 1 from
    ⟨fun h => congrArg (fun x => x.toAdd.val.toMul) h,
      fun h => Subtype.ext (congrArg Additive.ofMul h)⟩]
  exact QuotientGroup.eq_one_iff _

theorem movedMap_conjugation (a : LocalQuotientAction H U Z) (h : H)
    (v : (⁅U,H⁆ : Subgroup G)) :
    letI := movedAction a
    movedMap a (⁅U,H⁆.normalizerMonoidHom
      ⟨h,normalizer_commutator_ge_right U H h.property⟩ v) =
      (QuotientGroup.mk' (pCore 2 H) h) • movedMap a v := by
  apply Subtype.ext
  exact (a.conjugation h ⟨v,moved_le a v.property⟩).symm

/-- Lift compatible coordinates on the moved quotient, preserving both kernels. -/
def liftAction (a : LocalQuotientAction H U Z) (hZ : Z ≤ ⁅U,H⁆)
    (eG : (H ⧸ pCore 2 H) ≃* OrthogonalActor)
    (eV : Multiplicative (movedSpace a) ≃* OrthogonalVector)
    (he : letI := movedAction a; letI := orthogonalAction
      ∀ g v, eV (g • v) = eG g • eV v) :
    SourceOrthogonalFourAction H U Z (H.pCoreIn 2) where
  normalized := a.normalizes
  point_le := hZ
  actor := eG.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  onto := eG.surjective.comp (QuotientGroup.mk'_surjective _)
  actor_kernel := by
    ext h
    change eG (QuotientGroup.mk' (pCore 2 H) h) = 1 ↔ _
    rw [eG.map_eq_one_iff]
    change h ∈ (QuotientGroup.mk' (pCore 2 H)).ker ↔ _
    rw [QuotientGroup.ker_mk']
    change h ∈ pCore 2 H ↔ h ∈ ((pCore 2 H).map H.subtype).subgroupOf H
    rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  coordinates := eV.toMonoidHom.comp (movedMap a)
  surjective := eV.surjective.comp (movedMap_surjective a)
  vector_kernel := by
    ext v
    change eV (movedMap a v) = 1 ↔ _
    rw [eV.map_eq_one_iff]
    exact SetLike.ext_iff.mp (movedMap_kernel a) v
  compatible := by
    let := movedAction a
    let := orthogonalAction
    intro h v
    change eV (movedMap a _) = eG (QuotientGroup.mk' (pCore 2 H) h) • eV (movedMap a v)
    rw [movedMap_conjugation, he]

theorem liftAction_plane (a : LocalQuotientAction H U Z) (hZ : Z ≤ ⁅U,H⁆)
    (eG : (H ⧸ pCore 2 H) ≃* OrthogonalActor)
    (eV : Multiplicative (movedSpace a) ≃* OrthogonalVector)
    (he : letI := movedAction a; letI := orthogonalAction
      ∀ g v, eV (g • v) = eG g • eV v)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)))
    (hA : A ≤ movedSpace a) (i : OrthogonalPlaneIndex)
    (hmark : ∀ v, eV v ∈ orthogonalCoordinatePlane i ↔ v.toAdd.val ∈ A) :
    (liftAction a hZ eG eV he).plane i = supportPreimage a A := by
  have hs : supportPreimage a (movedSpace a) = ⁅U,H⁆ := by
    unfold supportPreimage
    rw [← moved_image a, comap_map_eq, sup_eq_left.mpr]
    · exact map_subgroupOf_eq_of_le (moved_le a)
    · rw [QuotientGroup.ker_mk']
      exact fun _ hz => hZ hz
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    apply (mem_supportPreimage a A ⟨v,moved_le a v.property⟩).mpr
    exact (hmark (movedMap a v)).mp hv
  · intro v hv
    have hvU := supportPreimage_le a A hv
    have hva := (mem_supportPreimage a A ⟨v,hvU⟩).mp hv
    have hvW : v ∈ ⁅U,H⁆ := by
      rw [← hs]
      exact (mem_supportPreimage a _ ⟨v,hvU⟩).mpr (hA hva)
    exact mem_map.mpr ⟨⟨v,hvW⟩,(hmark _).mpr hva,rfl⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.OrthogonalSource
