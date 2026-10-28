module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.AtlasPort.LinearGroups.G2.LieSpecialRadical
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Theory.GroupTheory.PCoreSurjective

/-!
# Commutator-layer obstructions in the G₂ local groups

A short group has elementary abelian U(B) = [O₂(B), B], before passing
to its module U(B)/C_U(B). Three explicit root calculations violate this
necessary condition: the short-Weyl and long-Weyl commutators, and a cubic
commutator in the quaternion core of the first parabolic of G₂(2)′.

The homomorphism forms retain the image of the actual two-core. They do
not assume injectivity, and hence can be used for central covers. A separate
surjection lemma lifts the two-core through an arbitrary two-group kernel.
The binary derived-group calculation uses the proved intersection core,
not the core of the parabolic in full G₂(2).

These are local calculations for Aschbacher–Smith 2.3.9(7), printed p.526,
using C.1.7 and F.1.12(I)(3),(8). They do not identify a parabolic with a
subnormal block or assert the source exclusion. The owner must still find
the displayed witnesses in every possible escaping relative block.

Root coordinates and binary quaternion models are reused from the ATLAS
port, licensed under LICENSES/ATLAS.txt; see LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup ChapterC Atlas.G2
open Atlas.G2.LieParabolicSetup
open scoped commutatorElement

variable {F : Type*} [Field F] [CharP F 2]

/-- A short-Weyl commutator has nonidentity square in the highest root group. -/
theorem short_root_commutator_square :
    ⁅rootB (1 : F), (weylS : Model F)⁆ ^ 2 = rootA 1 := by
  have hinv : (rootB (1 : F))⁻¹ = rootB 1 := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootB_add, CharTwo.add_self_eq_zero, rootB_zero]
  have hc : ⁅rootB (1 : F), (weylS : Model F)⁆ = unipotentProduct ![0,1,0,0,1,0] := by
    rw [commutatorElement_def, hinv]
    simp only [mul_assoc]
    rw [← mul_assoc weylS, weylS_rootB]
    simp [unipotentProduct]
  rw [hc, fiveRoot_square _ rfl]
  simp [CharTwo.neg_eq]

/-- A long-Weyl commutator has square A(1)B(1). -/
theorem long_root_commutator_square :
    ⁅rootD (1 : F), (weylR : Model F)⁆ ^ 2 = rootA 1 * rootB 1 := by
  have hinv : (rootD (1 : F))⁻¹ = rootD 1 := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootD_add, CharTwo.add_self_eq_zero, rootD_zero]
  have hc : ⁅rootD (1 : F), (weylR : Model F)⁆ = unipotentProduct ![0,0,0,1,0,1] := by
    rw [commutatorElement_def, hinv]
    simp only [mul_assoc]
    rw [← mul_assoc weylR, weylR_rootD]
    simp [unipotentProduct]
  rw [hc, pow_two, unipotentProduct_mul]
  have ht : unipotentProductParameters (![0,0,0,1,0,1] : Fin 6 → F)
      ![0,0,0,1,0,1] = ![1,1,0,0,0,0] := by
    have h9 : (9 : F) = 1 := by
      calc
        (9 : F) = 2 * 4 + 1 := by norm_num
        _ = 1 := by rw [CharTwo.two_eq_zero]; simp
    have h3 : (3 : F) = 1 := by
      calc
        (3 : F) = 2 + 1 := by norm_num
        _ = 1 := by rw [CharTwo.two_eq_zero]; simp
    ext i
    fin_cases i <;> dsimp [unipotentProductParameters] <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, CharTwo.neg_eq, h9, h3]
  rw [ht]
  simp [unipotentProduct]

omit [CharP F 2] in
theorem rootA_one_ne_one : rootA (1 : F) ≠ 1 := by
  intro h
  exact one_ne_zero (rootA_injective (h.trans rootA_zero.symm))

omit [CharP F 2] in
theorem rootAB_one_ne_one : rootA (1 : F) * rootB 1 ≠ 1 := by
  intro h
  have he : unipotentProduct (![1,1,0,0,0,0] : Fin 6 → F) = unipotentProduct 0 := by
    simpa [unipotentProduct] using h
  have ht := congrFun (unipotentProduct_injective he) 0
  exact one_ne_zero ht

/-- Images of commutators from a short group’s actual two-core square to one. -/
theorem short_image_square {K T : Type*} [Group K] [Group T]
    (h : IsShort K) (f : K →* T) {x y : T}
    (hx : x ∈ (pCore 2 K).map f) (hy : y ∈ f.range) : ⁅x,y⁆ ^ 2 = 1 := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  let u : blockU K := ⟨⁅a,b⁆, Subgroup.commutator_mem_commutator ha (mem_top b)⟩
  have hu : u ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.elementary.exponent_dvd_p u
  have he := congrArg (fun v : blockU K => f v.val) hu
  simpa only [u, Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one,
    map_commutatorElement] using he

theorem not_short_of_short_root_images {K : Type*} [Group K] (f : K →* Model F)
    (hx : rootB 1 ∈ (pCore 2 K).map f) (hy : weylS ∈ f.range) : ¬ IsShort K := by
  intro h
  have he := short_image_square h f hx hy
  rw [short_root_commutator_square] at he
  exact rootA_one_ne_one he

theorem not_short_of_long_root_images {K : Type*} [Group K] (f : K →* Model F)
    (hx : rootD 1 ∈ (pCore 2 K).map f) (hy : weylR ∈ f.range) : ¬ IsShort K := by
  intro h
  have he := short_image_square h f hx hy
  rw [long_root_commutator_square] at he
  exact rootAB_one_ne_one he

theorem not_short_longLocal [Finite F] : ¬ IsShort (local₂ (F := F)) := by
  apply not_short_of_long_root_images (local₂ (F := F)).subtype
  · change rootD 1 ∈ (local₂ (F := F)).pCoreIn 2
    rw [local₂_pCoreIn]
    exact ⟨![0,0,0,1,0,0], rfl, by simp [unipotentProduct]⟩
  · exact ⟨⟨weylR, Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))⟩, rfl⟩

/-- The cubic moves a quaternion generator already inside the derived-group core. -/
theorem binary_cubic_commutator_square :
    ⁅BinaryCore.embedding BinaryCore.rightI, BinaryParabolicPair.cubicActor⁆ ^ 2 =
      rootA (1 : ZMod 2) := by
  have he : ⁅BinaryCore.embedding BinaryCore.rightI, BinaryParabolicPair.cubicActor⁆ =
      BinaryCore.embedding (BinaryCore.rightI *
        (BinaryParabolicPair.cubicConjugate BinaryCore.rightI)⁻¹) := by
    rw [map_mul, map_inv, ← BinaryParabolicPair.cubic_conjugate]
    rw [commutatorElement_def]
    group
  rw [he, ← map_pow]
  have hs : (BinaryCore.rightI *
      (BinaryParabolicPair.cubicConjugate BinaryCore.rightI)⁻¹) ^ 2 =
      BinaryCore.involution := by decide +kernel
  rw [hs, BinaryCore.embedding_involution]

theorem not_short_of_binary_cubic_images {K : Type*} [Group K] (f : K →* Model (ZMod 2))
    (hx : BinaryCore.embedding BinaryCore.rightI ∈ (pCore 2 K).map f)
    (hy : BinaryParabolicPair.cubicActor ∈ f.range) : ¬ IsShort K := by
  intro h
  have he := short_image_square h f hx hy
  rw [binary_cubic_commutator_square] at he
  exact rootA_one_ne_one he

theorem not_short_binaryDerivedFirst : ¬ IsShort BinaryParabolicPair.derivedFirst := by
  let f := BinaryParabolicPair.DerivedModel.subtype.comp
    BinaryParabolicPair.derivedFirst.subtype
  apply not_short_of_binary_cubic_images f
  · rw [show f = BinaryParabolicPair.DerivedModel.subtype.comp
      BinaryParabolicPair.derivedFirst.subtype from rfl, ← Subgroup.map_map]
    change BinaryCore.embedding BinaryCore.rightI ∈
      (BinaryParabolicPair.derivedFirst.pCoreIn 2).map _
    rw [BinaryParabolicPair.derivedFirst_pCore_in_model]
    exact ⟨BinaryCore.rightI, rfl, rfl⟩
  · exact ⟨⟨⟨_, BinaryParabolicPair.cubicActor_mem_derived⟩,
      BinaryParabolicPair.cubicActor_mem_derivedFirst⟩, rfl⟩

/-- The obstruction survives every surjection with a two-group kernel. -/
theorem short_surjective_square {K T : Type*} [Group K] [Group T] [Finite T]
    (h : IsShort K) (f : K →* T) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) {x y : T} (hx : x ∈ pCore 2 T) :
    ⁅x,y⁆ ^ 2 = 1 := by
  let := h.finite
  have hc : (pCore 2 K).map f = pCore 2 T := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hker, Subgroup.map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  exact short_image_square h f (hc ▸ hx) (hf y)

/-- The same transfer, retaining an ambient embedding or homomorphism of
the quotient. In particular the two-core is taken in the quotient group,
not in the group receiving that homomorphism. -/
theorem short_quotient_image_square {K T A : Type*} [Group K] [Group T]
    [Group A] [Finite T] (h : IsShort K) (f : K →* T)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) (g : T →* A)
    {x y : A} (hx : x ∈ (pCore 2 T).map g) (hy : y ∈ g.range) :
    ⁅x, y⁆ ^ 2 = 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have he := congrArg g (short_surjective_square h f hf hker (y := b) ha)
  simpa only [map_pow, map_commutatorElement, map_one] using he

/-- Every finite two-group extension of the long local group fails the
short-group commutator condition. This includes its central two-covers. -/
theorem not_short_of_longLocal_quotient [Finite F] {K : Type*} [Group K]
    (f : K →* local₂ (F := F)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : ¬ IsShort K := by
  intro h
  have hx : rootD (1 : F) ∈ (pCore 2 (local₂ (F := F))).map local₂.subtype := by
    change rootD 1 ∈ (local₂ (F := F)).pCoreIn 2
    rw [local₂_pCoreIn]
    exact ⟨![0,0,0,1,0,0], rfl, by simp [unipotentProduct]⟩
  have hy : (weylR : Model F) ∈ (local₂ (F := F)).subtype.range :=
    ⟨⟨weylR, Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))⟩, rfl⟩
  have he := short_quotient_image_square h f hf hker local₂.subtype hx hy
  rw [long_root_commutator_square] at he
  exact rootAB_one_ne_one he

/-- The binary restriction also excludes every two-group extension. The
target is the first parabolic inside G₂(2)′, not the full binary group. -/
theorem not_short_of_binaryDerivedFirst_quotient {K : Type*} [Group K]
    (f : K →* BinaryParabolicPair.derivedFirst) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : ¬ IsShort K := by
  intro h
  let g := BinaryParabolicPair.DerivedModel.subtype.comp
    BinaryParabolicPair.derivedFirst.subtype
  have hx : BinaryCore.embedding BinaryCore.rightI ∈
      (pCore 2 BinaryParabolicPair.derivedFirst).map g := by
    rw [show g = BinaryParabolicPair.DerivedModel.subtype.comp
      BinaryParabolicPair.derivedFirst.subtype from rfl, ← Subgroup.map_map]
    change BinaryCore.embedding BinaryCore.rightI ∈
      (BinaryParabolicPair.derivedFirst.pCoreIn 2).map _
    rw [BinaryParabolicPair.derivedFirst_pCore_in_model]
    exact ⟨BinaryCore.rightI, rfl, rfl⟩
  have hy : BinaryParabolicPair.cubicActor ∈ g.range :=
    ⟨⟨⟨_, BinaryParabolicPair.cubicActor_mem_derived⟩,
      BinaryParabolicPair.cubicActor_mem_derivedFirst⟩, rfl⟩
  have he := short_quotient_image_square h f hf hker g hx hy
  rw [binary_cubic_commutator_square] at he
  exact rootA_one_ne_one he

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
