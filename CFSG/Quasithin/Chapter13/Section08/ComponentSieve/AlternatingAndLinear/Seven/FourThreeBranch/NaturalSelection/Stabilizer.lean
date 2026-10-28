module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PartitionReduction

/-!
# The relative four-plus-three stabilizer in H

The stabilizer is pulled back through the actual quotient H → H/O₂(H),
then embedded in the ambient group. Its solvability follows from the literal
permutation stabilizer and the two-group kernel. The universal conclusion of
13.8.13 places it inside H ∩ M. Order-three elements in its star image lift
through O₂(H) to elements of order three, and hence enter L₁ by 13.7.3(9).

The reverse containment and the resulting residual markings are separate
structural obligations; they are not assumed in these reductions.

Source: Aschbacher–Smith, 13.7.3(9), 13.8.13 and 13.8.24,
printed pp.936, 950–951 and 958 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
open LocalGeometry

/-- Solvability of the relative permutation stabilizer needs only faithfulness. -/
theorem relative_permutation_stabilizer_isSolvable {J : Type*} [Group J]
    (φ : J →* S7) (hφ : Function.Injective φ) :
    Group.IsSolvable (fourThreeStabilizer.comap φ) := by
  let e := MonoidHom.ofInjective hφ
  let D := fourThreeStabilizer.comap φ.range.subtype
  let : Group.IsSolvable D :=
    PermutationOvergroups.fourThreeStabilizer_comap_isSolvable φ.range
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom.subgroupComap D)
    (fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h)))

variable {G : Type*} [Group G] [Finite G]

/-- The actual stabilizer inside H, expressed as an ambient subgroup. -/
def relativeStabilizer (H : Subgroup G) (φ : Source.Hstar H →* S7) : Subgroup G :=
  ((fourThreeStabilizer.comap φ).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

/-- The full inverse image lies in H ∩ M by 13.8.13. -/
theorem relativeStabilizer_le_inter (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ) :
    relativeStabilizer H φ ≤ H ⊓ M := by
  let : Group.IsSolvable (fourThreeStabilizer.comap φ) :=
    relative_permutation_stabilizer_isSolvable φ hφ
  exact le_inf (map_subtype_le _)
    (solvable_star_lift_le_M H L₁ T G₁ M hbase hHG h13 _ hP)

omit [Finite G] in
/-- No two-core containment is needed to place the original local subgroup
inside the full stabilizer inverse image. -/
theorem local_le_relativeStabilizer (H L₁ T : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (φ : Source.Hstar H →* S7)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ) :
    L₁ ⊔ T ≤ relativeStabilizer H φ := by
  intro x hx
  exact ⟨⟨x, hbase hx⟩, hP (mem_map_of_mem _ hx), rfl⟩

/-- Every order-three star element of the relative stabilizer belongs to L₁*.
The lift has order three in H itself, rather than merely modulo O₂(H). -/
theorem order_three_mem_local_star (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ)
    (a : Source.Hstar H) (ha : φ a ∈ fourThreeStabilizer) (ho : orderOf a = 3) :
    a ∈ Source.starImage H L₁ := by
  obtain ⟨x, hx, hxo⟩ := order_three_star_lift H a ho
  have hxS : (x : G) ∈ relativeStabilizer H φ :=
    ⟨x, by change φ (QuotientGroup.mk' (pCore 2 H) x) ∈ fourThreeStabilizer; rwa [hx], rfl⟩
  have hxM := relativeStabilizer_le_inter H L₁ T G₁ M hbase hHG h13 φ hφ hP hxS
  have hxL : (x : G) ∈ L₁ := by
    rw [htheta]
    exact subset_closure ⟨hxM, (orderOf_coe x).trans hxo⟩
  exact ⟨x, hxL, hx⟩

/-- In particular the even order-three permutations in the partition
stabilizer lie in the literal image of L₁. -/
theorem even_order_three_mem_local_image (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ)
    (a : S7) (ha : a ∈ fourThreeStabilizer) (hA : a ∈ alternatingGroup (Fin 7))
    (ho : orderOf a = 3) : a ∈ (Source.starImage H L₁).map φ := by
  obtain ⟨b, rfl⟩ := hAlt hA
  exact ⟨b, order_three_mem_local_star H L₁ T G₁ M hbase hHG htheta h13 φ hφ hP b ha
    ((orderOf_injective φ hφ b).symm.trans ho), rfl⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
