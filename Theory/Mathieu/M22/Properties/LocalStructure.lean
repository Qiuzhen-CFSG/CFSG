module
public import Theory.Mathieu.M22.Properties.LocalSubgroups
public import Theory.Mathieu.M22.Properties.PointStabilizerMaximal
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace Sporadic.Mathieu
noncomputable section
public structure M22LocalShape where
  label : String
  carrier : Subgroup M22
  carrierCard : Nat
  carrier_card : Nat.card carrier = carrierCard
  kernelCard : Nat
  quotientCard : Nat
  split_order : carrierCard = 16 * quotientCard
@[expose] public def m22PairLocalShape : M22LocalShape where
  label := "2^4:S5"
  carrier := m22PairStabilizer
  carrierCard := 1920
  carrier_card := m22PairStabilizer_card
  kernelCard := 16
  quotientCard := 120
  split_order := by norm_num
@[expose] public def m22HexadLocalShape : M22LocalShape where
  label := "2^4:A6"
  carrier := m22HexadStabilizer
  carrierCard := 5760
  carrier_card := m22HexadStabilizer_card
  kernelCard := 16
  quotientCard := 360
  split_order := by norm_num
public structure M22NamedSubgroupShape where
  name : String
  order : Nat
  descriptor : String
@[expose] public def m22L34Shape : M22NamedSubgroupShape :=
  { name := "L3(4)", order := 20160, descriptor := "PSL(3,4)" }
@[expose] public def m22A7Shape : M22NamedSubgroupShape :=
  { name := "A7", order := 2520, descriptor := "Alt(7)" }
@[expose] public def m22PairS5Shape : M22NamedSubgroupShape :=
  { name := "2^4:S5", order := 1920, descriptor := "pair stabilizer" }
@[expose] public def m22HexadA6Shape : M22NamedSubgroupShape :=
  { name := "2^4:A6", order := 5760, descriptor := "hexad stabilizer" }
public theorem m22NamedSubgroup_orders :
    (m22L34Shape.order, m22PairS5Shape.order,
      m22HexadA6Shape.order, m22A7Shape.order) =
      (20160, 1920, 5760, 2520) := by
  rfl
public theorem m22PointStabilizer_maximal :
    IsCoatom (MulAction.stabilizer M22 (1 : Fin 22)) :=
  m22PointStabilizerOne_isCoatom
end
end Sporadic.Mathieu
