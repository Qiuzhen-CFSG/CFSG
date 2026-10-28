module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RootObstructions
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Neither binary derived parabolic has a short two-residual

The cubic lies in O²(P) for the first parabolic P of the actual G₂(2)′.
Commuting it with a quaternion generator puts an element into both O²(P)
and O₂(P). The normal two-subgroup O₂(P) intersected with O²(P) lies in
O₂(O²(P)). A second commutator with the cubic still has nonidentity square.
Thus the elementary condition on [O₂(O²(P)), O²(P)] fails.

On the second side the core element C(1)D(1) has even sign and lies in
the actual derived group. Its commutator with the long cubic has square
B(1); commuting a second time gives square A(1)B(1). Pulling back the
proved long-local two-core places this element in the derived parabolic's
actual two-core, and the same residual argument applies.

This is a residual calculation, not an identification of every subnormal
block in an ambient local overgroup. Source: Aschbacher–Smith 2.3.9(7),
printed p.526, using C.1.7 and the binary local structures of F.1.12(I)(8).
The root coordinates and quaternion model come from the licensed ATLAS port
(LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup ChapterC Atlas.G2
open scoped commutatorElement

 theorem binary_double_cubic_commutator_square :
    ⁅⁅BinaryCore.embedding BinaryCore.rightI, BinaryParabolicPair.cubicActor⁆,
      BinaryParabolicPair.cubicActor⁆ ^ 2 = rootA (1 : ZMod 2) := by
  have he (q : BinaryCore.Coordinates) :
      ⁅BinaryCore.embedding q, BinaryParabolicPair.cubicActor⁆ =
        BinaryCore.embedding (q * (BinaryParabolicPair.cubicConjugate q)⁻¹) := by
    rw [map_mul, map_inv, ← BinaryParabolicPair.cubic_conjugate]
    rw [commutatorElement_def]
    group
  rw [he, he, ← map_pow]
  have hs :
      ((BinaryCore.rightI * (BinaryParabolicPair.cubicConjugate BinaryCore.rightI)⁻¹) *
        (BinaryParabolicPair.cubicConjugate
          (BinaryCore.rightI * (BinaryParabolicPair.cubicConjugate BinaryCore.rightI)⁻¹))⁻¹)^2 =
      BinaryCore.involution := by decide +kernel
  rw [hs, BinaryCore.embedding_involution]

theorem not_short_binaryDerivedFirst_residual :
    ¬ IsShort (pResidual 2 BinaryParabolicPair.derivedFirst) := by
  let P := BinaryParabolicPair.derivedFirst
  let R := pResidual 2 P
  let g := BinaryParabolicPair.DerivedModel.subtype.comp P.subtype
  have hx : BinaryCore.embedding BinaryCore.rightI ∈ (pCore 2 P).map g := by
    rw [show g = BinaryParabolicPair.DerivedModel.subtype.comp P.subtype from rfl,
      ← Subgroup.map_map]
    change BinaryCore.embedding BinaryCore.rightI ∈
      (BinaryParabolicPair.derivedFirst.pCoreIn 2).map _
    rw [BinaryParabolicPair.derivedFirst_pCore_in_model]
    exact ⟨BinaryCore.rightI, rfl, rfl⟩
  obtain ⟨q, hq, hqg⟩ := hx
  let c : P := ⟨⟨_, BinaryParabolicPair.cubicActor_mem_derived⟩,
    BinaryParabolicPair.cubicActor_mem_derivedFirst⟩
  have hc : c ∈ R := BinaryParabolicPair.cubicActor_derived_residual
  have haR : ⁅q,c⁆ ∈ R :=
    (Subgroup.commutator_le_right (⊤ : Subgroup P) R)
      (Subgroup.commutator_mem_commutator (mem_top q) hc)
  let a : R := ⟨⁅q,c⁆, haR⟩
  have ha : a ∈ pCore 2 R := by
    have hsub : (pCore 2 P).subgroupOf R ≤ pCore 2 R :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    apply hsub
    exact (Subgroup.commutator_le_left (pCore 2 P) (⊤ : Subgroup P))
      (Subgroup.commutator_mem_commutator hq (mem_top c))
  intro h
  have he := short_image_square h (g.comp R.subtype)
    (x := g ⁅q,c⁆) (y := g c) ⟨a,ha,rfl⟩ ⟨⟨c,hc⟩,rfl⟩
  rw [map_commutatorElement, hqg] at he
  change ⁅⁅BinaryCore.embedding BinaryCore.rightI, BinaryParabolicPair.cubicActor⁆,
    BinaryParabolicPair.cubicActor⁆ ^ 2 = 1 at he
  rw [binary_double_cubic_commutator_square] at he
  exact rootA_one_ne_one he

set_option maxRecDepth 10000
set_option maxHeartbeats 800000 in
theorem binary_long_cubic_commutator_square :
    ⁅rootC (1 : ZMod 2) * rootD 1, BinaryCore.movingActor⁆ ^ 2 = rootB 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
  intro j
  funext i
  simp only [Pi.basisFun_apply]
  revert j i
  decide +kernel

theorem not_short_of_binary_long_cubic_images {K : Type*} [Group K]
    (f : K →* Model (ZMod 2))
    (hx : rootC 1 * rootD 1 ∈ (pCore 2 K).map f)
    (hy : BinaryCore.movingActor ∈ f.range) : ¬ IsShort K := by
  intro h
  have he := short_image_square h f hx hy
  rw [binary_long_cubic_commutator_square] at he
  exact one_ne_zero (rootB_injective (he.trans rootB_zero.symm))

theorem binary_long_core_root_mem_derived :
    rootC (1 : ZMod 2) * rootD 1 ∈ commutator (Model (ZMod 2)) := by
  have h := (BinaryParabolicPair.embedding_mem_derived_iff BinaryCore.leftI).mpr rfl
  simpa [BinaryCore.embedding, BinaryCore.parameters, BinaryCore.leftI,
    unipotentProduct] using h

theorem binary_long_cubic_mem_derived :
    BinaryCore.movingActor ∈ commutator (Model (ZMod 2)) := by
  rw [BinaryParabolicPair.commutator_eq_longRootClosure, ← BinaryException.lineSign_kernel]
  have hp : Binary.lineSign BinaryCore.movingActor ^ 3 = 1 := by
    rw [← map_pow, BinaryCore.movingActor_cube, map_one]
  rcases Int.units_eq_one_or (Binary.lineSign BinaryCore.movingActor) with h | h
  · exact h
  · rw [h] at hp
    norm_num at hp

theorem binary_long_core_root_mem_derivedSecond_core :
    rootC (1 : ZMod 2) * rootD 1 ∈ (pCore 2 BinaryParabolicPair.derivedSecond).map
      (BinaryParabolicPair.DerivedModel.subtype.comp
        BinaryParabolicPair.derivedSecond.subtype) := by
  let P := BinaryParabolicPair.derivedSecond
  let g := BinaryParabolicPair.DerivedModel.subtype.comp P.subtype
  let f : P →* LieParabolicSetup.local₂ (F := ZMod 2) :=
    g.codRestrict _ (by
      intro x
      rw [LieParabolicSetup.local₂_binary]
      exact x.property)
  have hf : Function.Injective f := by
    intro x y h
    have he : g x = g y := congrArg (fun t : LieParabolicSetup.local₂ (F := ZMod 2) =>
      (t : Model (ZMod 2))) h
    exact Subtype.ext (Subtype.ext he)
  have hcore : (pCore 2 (LieParabolicSetup.local₂ (F := ZMod 2))).comap f ≤ pCore 2 P :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective f hf⟩
  have hxP : rootC (1 : ZMod 2) * rootD 1 ∈ BinaryCore.secondParabolic := by
    apply Subgroup.mem_sup_left
    apply Subgroup.mem_sup_left
    rw [unipotent_eq_range]
    exact ⟨![0,0,1,1,0,0], by simp [unipotentProduct]⟩
  let x : P := ⟨⟨_, binary_long_core_root_mem_derived⟩, hxP⟩
  have hx : x ∈ pCore 2 P := by
    apply hcore
    change f x ∈ pCore 2 (LieParabolicSetup.local₂ (F := ZMod 2))
    rw [LieParabolicSetup.local₂_pCore]
    change rootC (1 : ZMod 2) * rootD 1 ∈ LieParabolicSetup.radical₂
    exact ⟨![0,0,1,1,0,0], rfl, by simp [unipotentProduct]⟩
  exact ⟨x,hx,rfl⟩

theorem not_short_binaryDerivedSecond : ¬ IsShort BinaryParabolicPair.derivedSecond := by
  apply not_short_of_binary_long_cubic_images
    (BinaryParabolicPair.DerivedModel.subtype.comp BinaryParabolicPair.derivedSecond.subtype)
  · exact binary_long_core_root_mem_derivedSecond_core
  · exact ⟨⟨⟨_,binary_long_cubic_mem_derived⟩,BinaryCore.movingActor_mem⟩,rfl⟩

set_option maxHeartbeats 1600000 in
theorem binary_long_double_cubic_commutator_square :
    ⁅⁅rootC (1 : ZMod 2) * rootD 1, BinaryCore.movingActor⁆,
      BinaryCore.movingActor⁆ ^ 2 = rootA 1 * rootB 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
  intro j
  funext i
  simp only [Pi.basisFun_apply]
  revert j i
  decide +kernel

theorem not_short_binaryDerivedSecond_residual :
    ¬ IsShort (pResidual 2 BinaryParabolicPair.derivedSecond) := by
  let P := BinaryParabolicPair.derivedSecond
  let R := pResidual 2 P
  let g := BinaryParabolicPair.DerivedModel.subtype.comp P.subtype
  obtain ⟨q, hq, hqg⟩ := binary_long_core_root_mem_derivedSecond_core
  let c : P := ⟨⟨_, binary_long_cubic_mem_derived⟩, BinaryCore.movingActor_mem⟩
  have hc : c ∈ R := by
    apply Subgroup.mem_pResidual_of_orderOf_coprime
    apply Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one
      (show c ^ 3 = 1 from Subtype.ext (Subtype.ext BinaryCore.movingActor_cube)))
    decide
  have haR : ⁅q,c⁆ ∈ R :=
    (Subgroup.commutator_le_right (⊤ : Subgroup P) R)
      (Subgroup.commutator_mem_commutator (mem_top q) hc)
  let a : R := ⟨⁅q,c⁆, haR⟩
  have ha : a ∈ pCore 2 R := by
    have hsub : (pCore 2 P).subgroupOf R ≤ pCore 2 R :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    apply hsub
    exact (Subgroup.commutator_le_left (pCore 2 P) (⊤ : Subgroup P))
      (Subgroup.commutator_mem_commutator hq (mem_top c))
  intro h
  have he := short_image_square h (g.comp R.subtype)
    (x := g ⁅q,c⁆) (y := g c) ⟨a,ha,rfl⟩ ⟨⟨c,hc⟩,rfl⟩
  rw [map_commutatorElement, hqg] at he
  change ⁅⁅rootC (1 : ZMod 2) * rootD 1, BinaryCore.movingActor⁆,
    BinaryCore.movingActor⁆ ^ 2 = 1 at he
  rw [binary_long_double_cubic_commutator_square] at he
  exact rootAB_one_ne_one he

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
