module
public import Theory.GroupTheory.TwoPlaneCover.Crossing
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.PlaneCentralizers
/-! # Marked crossing planes in the original matrix Sylow model
Actual root-plane centralizers discharge the full row and Frattini hypotheses
of the crossing argument, including literal elementary central covers.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
theorem marked_product_wing_commutes
    (f:G→*unipotent (F:=F)) (K:Subgroup G) (i:Bool)
    (hf:Function.Surjective (f.comp K.subtype)) (hKC:K≤centralizer (f.ker:Set G))
    [IsElementaryAbelian 2 ((wing (F:=F) false).comap (f.comp K.subtype))]
    [IsElementaryAbelian 2 ((wing (F:=F) true).comap (f.comp K.subtype))]
    (hc:_root_.commutator G≤center G) (hp:IsPGroup 2 G)
    (e:G≃*G) (hne:frattini f.ker≠⊥) (hd:Disjoint f.ker (f.ker.map e.toMonoidHom)) :
    (((wing (F:=F) i).comap (f.comp K.subtype)).map K.subtype).map e.toMonoidHom≤
      centralizer ((((wing (F:=F) i).comap (f.comp K.subtype)).map K.subtype):Set G) := by
  let :=center_elementary (F:=F)
  have hi:wing (F:=F) i=wing false∨wing (F:=F) i=wing true:=by cases i <;> simp
  exact Stellmacher.marked_product_plane_commutes f K (wing false) (wing true) (wing i)
    hf hKC hi (Nat.card F) Nat.card_pos wings_generate center_le_wings class_two
    centralizer_involution involution_centralizer_index (wing_self_centralizer i).le
    (fun t ht hn=>(wing_involution_geometry i t ht hn).2) hc hp e hne hd
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
