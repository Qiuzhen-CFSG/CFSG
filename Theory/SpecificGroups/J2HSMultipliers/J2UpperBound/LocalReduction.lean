module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddPrimary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.PerfectCentralCoverLocalBound

/-!
# Reduction of the J₂ upper bound to its marked involution centralizer

The fixed centralizer `Seed.l₁` has odd index 315. Its universal perfect
cover lifts to the full preimage in any central cover of J₂. Central transfer
places the entire global kernel in that lift, since `OddPrimary` proves the
kernel is a two-group. The local universal kernel therefore surjects onto
the global kernel. This retains the exact subgroup and all covering maps.

Perfectness of the literal centralizer is already proved in `CoverSquareOrbit`.
The local universal-kernel upper bound remains an explicit premise. Once
supplied, it completes the upper bound without further fusion inputs.
Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 §6.1.
-/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2
open Sporadic.LeechRelated.J2 PerfectCentralCovering Subgroup

/-- The local centralizer kernel bounds every perfect central kernel over J₂.
The literal order-1920 subgroup is perfect by the checked commutator words. -/
theorem kernel_card_le_local_universal_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    Nat.card f.ker ≤
      Nat.card (universalProjection ExceptionalParabolics.Seed.l₁).ker := by
  let : Group.IsPerfect ExceptionalParabolics.Seed.l₁ :=
    ExceptionalParabolics.FirstParabolic.CoverSquareOrbit.l₁_isPerfect
  let L := ExceptionalParabolics.Seed.l₁
  let P := L.comap f
  let g : P →* L :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : E) (y : E)) }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, by change f x ∈ L; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  have hkg : g.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hk (congrArg Subtype.val hx)) y
  obtain ⟨a₀, ha₀, _⟩ := universalProjection_existsUnique_lift g hg hkg
  let a : UniversalGroup L →* E := P.subtype.comp a₀
  have ha (x : UniversalGroup L) : f (a x) = (universalProjection L x : L) :=
    congrArg Subtype.val (DFunLike.congr_fun ha₀ x)
  have hmap : a.range.map f = L := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      rw [ha]
      exact (universalProjection L x).property
    · intro y hy
      obtain ⟨x, hx⟩ := universalProjection_surjective L ⟨y, hy⟩
      exact ⟨a x, ⟨x, rfl⟩, (ha x).trans (congrArg Subtype.val hx)⟩
  have hi : ¬ 2 ∣ L.index := by
    change ¬ 2 ∣ ExceptionalParabolics.Seed.l₁.index
    have hindex : ExceptionalParabolics.Seed.l₁.index = 315 :=
      GeneratorPair.FirstFusion.centralizer_index
    rw [hindex]
    decide
  let c : Cover E Carrier := ⟨f, hf, inferInstance, hk⟩
  have hkH : f.ker ≤ a.range := c.central_pSubgroup_le_local_lift
    a.range L hmap hi f.ker le_rfl (kernel_isPGroup f hf hk)
  let φ : (universalProjection L).ker → f.ker := fun x =>
    ⟨a x, by
      change f (a x) = 1
      rw [ha, x.property, Subgroup.coe_one]⟩
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨x, hx⟩ := hkH z.property
    have hcx : universalProjection L x = 1 := by
      apply Subtype.ext
      rw [← ha, hx]
      exact z.property
    exact ⟨⟨x, hcx⟩, Subtype.ext hx⟩
  exact Nat.card_le_card_of_surjective φ hφ

/-- Final numerical assembly once the independent local calculation is supplied. -/
theorem kernel_card_le_two_of_local_bound
    (hlocal : Nat.card (universalProjection ExceptionalParabolics.Seed.l₁).ker ≤ 2)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    Nat.card f.ker ≤ 2 :=
  (kernel_card_le_local_universal_kernel f hf hk).trans hlocal

end Theory.SpecificGroups.J2HSMultipliers.J2
