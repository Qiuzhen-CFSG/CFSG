module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinCoverage
public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Theory.Representation.SL2NaturalOffenders.NaturalPair

/-!
# The seed centralizer in the actual paired action

A nonzero vector in each natural SL₂ summand has a two-group stabilizer.
Thus an element centralizing the marked seed has square in the kernel of
the original plus map. That kernel is a two-group, so the centralizer of
the B-conjugate span is also a two-group. This keeps the actual seed, action,
and subgroup B; it does not replace the original centralizer by a quotient.

Source: Aschbacher--Smith 13.6.14, printed pp.929--930.
-/

public section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G]

theorem pair_seed_centralizer_isTwoGroup_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : IsPGroup 2 (joinPlusMap K L T z v hL hz).ker)
    (F : Type*) [Field F] [Finite F] [Algebra (ZMod 2) F]
    (e : plusImage K L T z v hL hz (Kminus K T v) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (f : Additive (WK K L T z v) →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)))
    (he : ∀ (g : plusImage K L T z v hL hz (Kminus K T v)) w,
      f (wkRepresentation K L T z v hL hz g w) =
        SL2NaturalOffenders.naturalPair (F := F) (e g) (f w))
    (hzW : z ∈ WK K L T z v)
    (hz₁ : (f (Additive.ofMul ⟨z,hzW⟩)).1 ≠ 0)
    (hz₂ : (f (Additive.ofMul ⟨z,hzW⟩)).2 ≠ 0)
    (B : Subgroup G) (hBA : B ≤ K ⊔ Tv T v)
    (hBC : plusImage K L T z v hL hz B ≤ plusImage K L T z v hL hz (Kminus K T v)) :
    IsPGroup 2 ((centralizer (conjugateSpanBy (zpowers z) B : Set G)).subgroupOf B) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let A := K ⊔ Tv T v
  let q := joinPlusMap K L T z v hL hz
  let zw : Additive (WK K L T z v) := Additive.ofMul ⟨z,hzW⟩
  intro b
  let a : A := ⟨b.val,hBA b.val.property⟩
  have haC : q a ∈ plusImage K L T z v hL hz (Kminus K T v) :=
    hBC (mem_map.mpr ⟨inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a,b.val.property,rfl⟩)
  let c : plusImage K L T z v hL hz (Kminus K T v) := ⟨q a,haC⟩
  have hcomm : (b.val : G) * z = z * (b.val : G) :=
    (b.property z ((le_conjugateSpanBy (zpowers z) B) (mem_zpowers z))).symm
  have hfix : wkRepresentation K L T z v hL hz (q a) zw = zw := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((wkRepresentation K L T z v hL hz
      (plusMk K L T z v hL hz (inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a)) zw).toMul : G) = z
    rw [wkRepresentation_apply]
    change (b.val : G) * z * (b.val : G)⁻¹ = z
    rw [hcomm,mul_assoc,mul_inv_cancel,mul_one]
  have hez : SL2NaturalOffenders.naturalPair (F := F) (e c) (f zw) = f zw :=
    (he c zw).symm.trans (congrArg f hfix)
  have hsq : e c ^ 2 = 1 := by
    apply Prod.ext
    · exact Matrix.SL2.pow_two_eq_one_of_nonzero_fixed (e c).1 (f zw).1 hz₁
        (congrArg Prod.fst hez)
    · exact Matrix.SL2.pow_two_eq_one_of_nonzero_fixed (e c).2 (f zw).2 hz₂
        (congrArg Prod.snd hez)
  have hc : c ^ 2 = 1 := e.injective (by simpa only [map_pow,map_one] using hsq)
  have hasq : a ^ 2 ∈ q.ker := by
    change q (a ^ 2) = 1
    rw [map_pow]
    exact congrArg Subtype.val hc
  obtain ⟨n,hn⟩ := hk ⟨a ^ 2,hasq⟩
  refine ⟨n+1,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (fun x : q.ker => ((x.val : A) : G)) hn
  change ((b.val : G) ^ 2) ^ (2 ^ n) = 1 at hh
  change (b.val : G) ^ (2 ^ (n+1)) = 1
  rw [pow_succ,Nat.mul_comm (2 ^ n) 2,pow_mul]
  exact hh

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
