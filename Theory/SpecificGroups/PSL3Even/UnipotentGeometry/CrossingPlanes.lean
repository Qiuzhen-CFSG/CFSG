module
public import Theory.GroupTheory.TwoPlaneCover.Crossing
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.PlaneCentralizers
public import Theory.ElementaryAbelian.Injective
/-! # Marked crossing planes in the original matrix Sylow model
Actual root-plane centralizers discharge the full row and Frattini hypotheses
of the crossing argument, including literal elementary central covers.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
namespace Matrix.PSL3Even.UnipotentGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
theorem marked_product_plane_commutes
    (f:G→*U F) (K:Subgroup G) (P:Subgroup (U F))
    (hf:Function.Surjective (f.comp K.subtype)) (hKC:K≤centralizer (f.ker:Set G))
    (hP:P=V₁ F∨P=V₂ F)
    [IsElementaryAbelian 2 ((V₁ F).comap (f.comp K.subtype))]
    [IsElementaryAbelian 2 ((V₂ F).comap (f.comp K.subtype))]
    (hc:_root_.commutator G≤center G) (hp:IsPGroup 2 G)
    (e:G≃*G) (hne:frattini f.ker≠⊥) (hd:Disjoint f.ker (f.ker.map e.toMonoidHom)) :
    ((P.comap (f.comp K.subtype)).map K.subtype).map e.toMonoidHom≤
      centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G) := by
  let : IsElementaryAbelian 2 (center (U F)):=IsElementaryAbelian.of_injective
    (inclusion (center_le_planes.trans inf_le_left : center (U F)≤V₁ F)) (inclusion_injective _)
  apply Stellmacher.marked_product_plane_commutes f K (V₁ F) (V₂ F) P hf hKC hP
    (Nat.card F) Nat.card_pos planes_generate center_le_planes class_two
    (fun t ht hz=>centralizer_involution F t ht (by rwa [Z_eq_center]))
    (fun t ht hz=>involution_centralizer_index t ht hz) ?_
    (fun t ht hn=>(plane_involution_geometry P hP t ht hn).2) hc hp e hne hd
  rcases hP with rfl|rfl
  · exact plane₁_self_centralizer.le
  · exact plane₂_self_centralizer.le
end Matrix.PSL3Even.UnipotentGeometry
