module
public import Theory.Representation.BinaryOffender.ProjectedSeed
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Residual images of normal actor subgroups

An invariant subspace gives a literal inclusion of the restricted normal
subgroup's faithful image into the ambient faithful image. Its range is the
image of that normal actor subgroup, hence normal. Restriction of the ambient
prime core and transport along this inclusion exclude the restricted two-core.

Applied to a normal odd subgroup's fixed space, the original ambient
Sylow-fixed generating seed supplies the ambient residual bound by coprime
projection. The seed need not span under the smaller normal actor subgroup.
This is the transport needed for the actual Jhat action in original 15.1.2,
printed pp.1084–1085.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem normal_subgroup_subspaceImage_twoCore
    (H : Subgroup G) [H.Normal] (U : Submodule (ZMod 2) V)
    (hU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U)
    (hcore : pCore 2 (subspaceActionImage ρ U)=⊥) :
    pCore 2 (subspaceActionImage (ρ.comp H.subtype) U)=⊥ := by
  let σ := ρ.comp H.subtype
  have hincl : subspaceActionImage σ U ≤ subspaceActionImage ρ U := by
    rintro a ⟨h,rfl⟩
    refine ⟨⟨h.val.val,hU (mem_top _)⟩,?_⟩
    apply Units.ext
    ext v
    rfl
  let j := Subgroup.inclusion hincl
  have hj : Function.Injective j := Subgroup.inclusion_injective hincl
  have hr : j.range = H.map (invariantActionHom ρ U hU) := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      obtain ⟨h,hh⟩ := b.property
      refine ⟨h.val,h.val.property,?_⟩
      apply Subtype.ext
      exact hh
    · rintro ⟨h,hh,rfl⟩
      have hu : (⟨h,hh⟩ : H) ∈ subspaceStabilizer σ U := by
        intro v
        exact hU (mem_top h) v
      refine ⟨subspaceActionHom σ U ⟨⟨h,hh⟩,hu⟩,?_⟩
      rfl
  let : j.range.Normal := hr ▸ Normal.map inferInstance _ (invariantActionHom_surjective ρ U hU)
  have hc : pCore 2 j.range=⊥ := by
    rw [pCore_eq_comap_of_normal,hcore]
    change j.range.subtype.ker=⊥
    exact j.range.ker_subtype
  let e := MonoidHom.ofInjective hj
  have he := pCore_map_iso 2 e
  rw [hc] at he
  exact (map_eq_bot_iff_of_injective _ e.injective).mp he

/-- The projected ambient seed also excludes the two-core of the action of a
normal subgroup on that same residual space. -/
theorem normalOddFixed_subgroupImage_twoCore [Finite G]
    (H Y : Subgroup G) [H.Normal] [Y.Normal] (hodd : Odd (Nat.card Y))
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v=w}=⊤) :
    pCore 2 (subspaceActionImage (ρ.comp H.subtype) (fixedSpace ρ Y))=⊥ :=
  normal_subgroup_subspaceImage_twoCore ρ H _ (fixedSpace_stable_of_normal ρ Y)
    (normalOddFixedImage_twoCore ρ Y hodd S Z hfix hspan)
end Representation.BinaryOffender
