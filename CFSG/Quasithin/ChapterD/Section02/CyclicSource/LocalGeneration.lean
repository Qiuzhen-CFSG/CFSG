module
public import CFSG.Quasithin.ChapterD.Section02.CyclicEndpoints
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The literal endpoint interface for cyclic D.2.17

The source branches produce an actual normal odd prime subgroup and an
actual generating involution. This record keeps their original inclusions,
full commutators, and the displacement bound. Its consumer transports the
unchanged binary action to multiplicative notation and applies the proved
small-support endpoint classification.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Concrete local generation, produced by a source branch rather than assumed
as a replacement for D.2.17. -/
structure LocalGeneration where
  kernel : Subgroup G
  normal : kernel.Normal
  prime : ℕ
  prime_prime : prime.Prime
  prime_odd : Odd prime
  pgroup : IsPGroup prime kernel
  nontrivial : kernel ≠ ⊥
  involution : G
  order_two : orderOf involution = 2
  generated : kernel ⊔ zpowers involution = ⊤
  commutator : ⁅kernel,zpowers involution⁆ = kernel
  moved : subspaceCommutator ρ ⊤ kernel = ⊤
  codimension : fixedCodim ρ (zpowers involution) ≤ 2

end CFSG.Quasithin.ChapterD.CyclicSource

namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

/-- Each concrete source witness is consumed on the original binary module. -/
theorem LocalGeneration.endpoints (d : LocalGeneration ρ) (hf : Function.Injective ρ) :
    letI := BinaryGroupAction.action ρ
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := d.normal
    Section02.CyclicThreeEndpoint (V := Multiplicative V) d.kernel d.involution ∨
      Section02.CyclicFiveEndpoint (V := Multiplicative V) d.kernel d.involution ∨
      Section02.ElementaryNineEndpoint (V := Multiplicative V) d.kernel d.involution ∨
      Section02.ExtraspecialEndpoint (V := Multiplicative V) d.kernel d.involution := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let := d.normal
  let : Fact d.prime.Prime := ⟨d.prime_prime⟩
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ hf
  have ht : IsInvolution d.involution :=
    ⟨fun he => by have hh := d.order_two; simp [he] at hh,
      d.order_two ▸ pow_orderOf_eq_one d.involution⟩
  have hodd : Nat.Coprime 2 (Nat.card d.kernel) := by
    obtain ⟨n,hn⟩ := d.pgroup.exists_card_eq
    rw [hn]
    exact d.prime_odd.coprime_two_left.pow_right n
  have hm : commutatorAction d.kernel (Multiplicative V) = ⊤ := by
    rw [BinaryGroupAction.commutator_eq,d.moved]
    exact BinaryGroupAction.submoduleEquivSubgroup.map_top
  have hi : Nat.card (Multiplicative V) ≤
      4 * Nat.card (FixedPoints.subgroup (zpowers d.involution) (Multiplicative V)) := by
    rw [BinaryGroupAction.fixedPoints_eq,BinaryGroupAction.card_submoduleEquivSubgroup]
    have hc : Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Nat.card_congr (Multiplicative.ofAdd (α := V)).symm,
        Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rw [hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    calc
      _ ≤ 2 ^ (2 + Module.finrank (ZMod 2) (fixedSpace ρ (zpowers d.involution))) :=
        Nat.pow_le_pow_right (by decide)
          (by have h := fixedCodim_add_finrank ρ (zpowers d.involution); have := d.codimension; omega)
      _ = _ := by rw [pow_add]; norm_num
  have hfaith : fixingSubgroup G (Set.univ : Set (Multiplicative V)) = ⊥ := by
    apply bot_unique
    intro g hg
    apply eq_of_smul_eq_smul (α := Multiplicative V)
    intro v
    simpa only [one_smul] using ((mem_fixingSubgroup_iff (M := G)).mp hg v (Set.mem_univ v))
  exact Section02.smallSupportClassification d.kernel d.nontrivial d.prime d.pgroup hodd
    d.involution ht d.generated d.commutator hm hi hfaith

end CFSG.Quasithin.ChapterD.CyclicSource
