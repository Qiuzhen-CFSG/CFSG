module
public import Theory.GroupTheory.TwoPlaneCover.MarkedFactor
public import Theory.GroupTheory.TwoPlaneCover.ModelRows
/-! # Crossing planes in a marked rank-two central product
The two elementary plane preimages supply the exact commutator rows and
their disjoint marked kernels. A nontrivial Frattini layer then forces each
automorphic crossing plane to commute with the original plane.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Stellmacher
variable {G Q:Type*} [Group G] [Group Q] [Finite G] [Finite Q]
theorem marked_product_plane_commutes
    (f:G→*Q) (K:Subgroup G) (P₀ P₁ P:Subgroup Q)
    (hf:Function.Surjective (f.comp K.subtype)) (hKC:K≤centralizer (f.ker:Set G))
    (hP:P=P₀∨P=P₁) (q:ℕ) (hq:1≤q)
    (hgen:P₀⊔P₁=⊤) (hZ:center Q≤P₀⊓P₁)
    [IsElementaryAbelian 2 (P₀.comap (f.comp K.subtype))]
    [IsElementaryAbelian 2 (P₁.comap (f.comp K.subtype))]
    (hcQ:_root_.commutator Q≤center Q)
    (hplanes:∀t:Q,t^2=1→t∉center Q→centralizer ({t}:Set Q)=P₀∨centralizer ({t}:Set Q)=P₁)
    (hindex:∀t:Q,t^2=1→t∉center Q→(centralizer ({t}:Set Q)).index=q)
    (hself:centralizer (P:Set Q)≤P)
    (hgeometry:∀t:Q,t^2=1→t∉P→
      P⊔centralizer ({t}:Set Q)=⊤ ∧ P⊓centralizer ({t}:Set Q)≤center Q)
    [IsElementaryAbelian 2 (center Q)]
    (hc:_root_.commutator G≤center G) (hp:IsPGroup 2 G)
    (e:G≃*G) (hne:frattini f.ker≠⊥) (hd:Disjoint f.ker (f.ker.map e.toMonoidHom)) :
    ((P.comap (f.comp K.subtype)).map K.subtype).map e.toMonoidHom≤
      centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G) := by
  let A:=P.comap (f.comp K.subtype)
  let V:=A.map K.subtype
  have hi:IsElementaryAbelian 2 A:=by rcases hP with rfl|rfl <;> infer_instance
  let :=hi
  have hVP:V.map f=P:=by
    change ((P.comap (f.comp K.subtype)).map K.subtype).map f=P
    rw [Subgroup.map_map,map_comap_eq_self_of_surjective hf]
  have hlift:=Subgroup.ClassTwo.plane_lift_centralizes f K P hf hKC
  have rows:=Subgroup.TwoPlaneCover.marked_cover_rows (f.comp K.subtype) hf
    P₀ P₁ P hP q hq hgen hZ hcQ hplanes hindex (fun t ht hn=>(hgeometry t ht hn).1)
  have full:=Subgroup.ClassTwo.plane_rows_of_factor f K P q hc hf hKC rows.1 hlift rows.2
  apply automorphic_plane_commutes f e V P hp q hne hd hVP hself hlift
    (fun v hv=>?_) (fun t ht hn=>(hgeometry t ht hn).2) full.1 full.2
  obtain ⟨a,ha,rfl⟩:=hv
  exact congrArg K.subtype (elemPow_eq_one_of_isElementaryAbelian a ha)
end Stellmacher
