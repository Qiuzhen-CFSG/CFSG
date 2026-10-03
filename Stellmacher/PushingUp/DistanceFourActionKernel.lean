module

public import Stellmacher.PushingUp.DistanceFourNormality
public import Theory.GroupAction.Quotient

/-!
# The source core fixes the actual central quotient

For the actual quotient `U/Z_a` in the chosen distance-four configuration,
this module proves that `Q_a` acts trivially whenever the supplied action is
induced by ambient conjugation and the quotient is elementary abelian.
The given normality and action instances are preserved throughout.

The five-core intersection `D` centralizes `U` pointwise. The subgroup `U`
acts trivially by inner conjugation on its abelian quotient. Transporting the
proved factorization `Q_a = D U` to the finite stabilizer therefore puts the
whole core in the fixing subgroup. The final assembly constructs the action
from the separately proved normality of `U`.

Source: B. Stellmacher, *Pushing up* (1986), (3.3)(1),(4),(6), p.15.
No finite free-amalgam or vertex-set hypothesis is used.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem quotient_fix_of_centralizes
    {H : Type*} [Group H] (L U Z : Subgroup H)
    (hZn : (Z.subgroupOf U).Normal)
    [MulDistribMulAction L (U ⧸ Z.subgroupOf U)]
    (hconjU : ∀ g : L, ∀ w : U, (g : H) * w * (g : H)⁻¹ ∈ U)
    (hact : ∀ (g : L) (w : U),
      g • (QuotientGroup.mk' (Z.subgroupOf U)) w =
        (QuotientGroup.mk' (Z.subgroupOf U))
          ⟨(g : H) * w * (g : H)⁻¹, hconjU g w⟩)
    (g : L) (hg : (g : H) ∈ Subgroup.centralizer U) :
    g ∈ fixingSubgroup L (Set.univ : Set (U ⧸ Z.subgroupOf U)) := by
  rw [mem_fixingSubgroup_iff]
  intro w _hw
  induction w using Quotient.inductionOn'
  rename_i w
  change g • (QuotientGroup.mk' (Z.subgroupOf U)) w =
    (QuotientGroup.mk' (Z.subgroupOf U)) w
  rw [hact]
  apply congrArg (QuotientGroup.mk' (Z.subgroupOf U))
  apply Subtype.ext
  have hc : (g : H) * w = (w : H) * g :=
    ((Subgroup.mem_centralizer_iff.mp hg) w w.property).symm
  change (g : H) * w * (g : H)⁻¹ = w
  rw [hc, mul_inv_cancel_right]

private theorem quotient_fix_of_mem
    {H : Type*} [Group H] (L U Z : Subgroup H)
    (hZn : (Z.subgroupOf U).Normal)
    [MulDistribMulAction L (U ⧸ Z.subgroupOf U)]
    [IsMulCommutative (U ⧸ Z.subgroupOf U)]
    (hconjU : ∀ g : L, ∀ w : U, (g : H) * w * (g : H)⁻¹ ∈ U)
    (hact : ∀ (g : L) (w : U),
      g • (QuotientGroup.mk' (Z.subgroupOf U)) w =
        (QuotientGroup.mk' (Z.subgroupOf U))
          ⟨(g : H) * w * (g : H)⁻¹, hconjU g w⟩)
    (g : L) (hg : (g : H) ∈ U) :
    g ∈ fixingSubgroup L (Set.univ : Set (U ⧸ Z.subgroupOf U)) := by
  rw [mem_fixingSubgroup_iff]
  intro w _hw
  induction w using Quotient.inductionOn'
  rename_i w
  change g • (QuotientGroup.mk' (Z.subgroupOf U)) w =
    (QuotientGroup.mk' (Z.subgroupOf U)) w
  rw [hact]
  let gu : U := ⟨g, hg⟩
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  change q (gu * w * gu⁻¹) = q w
  rw [map_mul, map_mul, map_inv]
  have hc := (IsMulCommutative.is_comm (M := U ⧸ Z.subgroupOf U)).comm (q gu) (q w)
  rw [hc, mul_inv_cancel_right]

set_option maxHeartbeats 700000 in
public theorem distanceFour_core_le_quotient_fix [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v)
    (hZn : ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).Normal)
    [MulDistribMulAction (stabilizer S a)
      ((DistanceFour.U S a c u) ⧸ (vertexZ S a).subgroupOf (DistanceFour.U S a c u))]
    [IsElementaryAbelian 2
      ((DistanceFour.U S a c u) ⧸ (vertexZ S a).subgroupOf (DistanceFour.U S a c u))]
    (hconjU : ∀ g : stabilizer S a, ∀ w : DistanceFour.U S a c u,
      (g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹ ∈ DistanceFour.U S a c u)
    (hact : ∀ (g : stabilizer S a) (w : DistanceFour.U S a c u),
      g • (QuotientGroup.mk' ((vertexZ S a).subgroupOf (DistanceFour.U S a c u))) w =
        (QuotientGroup.mk' ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)))
          ⟨(g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹, hconjU g w⟩) :
    pCore 2 (stabilizer S a) ≤ fixingSubgroup (stabilizer S a) (Set.univ : Set
      ((DistanceFour.U S a c u) ⧸ (vertexZ S a).subgroupOf (DistanceFour.U S a c u))) := by
  let G := stabilizer S a
  let U := DistanceFour.U S a c u
  let D := DistanceFour.D S a a' c u v
  let UI := U.subgroupOf G
  let DI := D.subgroupOf G
  have hi := distanceFour_initialRelations S T hTS hP hSne hA a a' c u v hb4 cfg
  have hn := distanceFour_normality S T hTS hP hSne hA a a' c u v hb4 cfg
  have hprod := distanceFour_core_product S T hTS hP hSne hA a a' c u v hb4 cfg
  have hUG : U ≤ G := hi.U_le_core.trans (Subgroup.map_subtype_le _)
  have hDG : D ≤ G :=
    (show D ≤ vertexTwoCore S a from fun _ h => h.1.1.2).trans (Subgroup.map_subtype_le _)
  have hQ : pCore 2 G = DI ⊔ UI := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDG,
      Subgroup.map_subgroupOf_eq_of_le hUG]
    exact hprod
  change pCore 2 G ≤ _
  rw [hQ]
  apply sup_le
  · intro d hd
    exact quotient_fix_of_centralizes G U (vertexZ S a) hZn hconjU hact d
      (hn.D_centralizes_U hd)
  · intro x hx
    exact quotient_fix_of_mem G U (vertexZ S a) hZn hconjU hact x hx

end Stellmacher.PushingUp
