module
public import Theory.GroupTheory.CommutingFactorRows
public import Theory.GroupTheory.ClassTwoProduct
public import Theory.GroupTheory.CrossingPlaneCommutator
/-! # Rows of a marked central product
Surjectivity from the first factor and centralization of the literal kernel
identify full commutator rows and preserve their disjointness from that kernel.
This supplies the source crossing-plane hypotheses in Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup.ClassTwo
variable {G Q:Type*} [Group G] [Group Q]
theorem factor_sup_kernel (f:G→*Q) (K:Subgroup G)
    (hf:Function.Surjective (f.comp K.subtype)) : K⊔f.ker=⊤ := by
  apply top_unique
  intro x _
  obtain ⟨k,hk⟩:=hf (f x)
  have hker:(k:G)⁻¹*x∈f.ker:=by
    change f ((k:G)⁻¹*x)=1
    change f (k:G)=f x at hk
    rw [map_mul,map_inv,hk,inv_mul_cancel]
  have hh:=mul_mem_sup k.property hker
  simpa only [mul_inv_cancel_left] using hh

theorem plane_row_map (K:Subgroup G) (A:Subgroup K) (k:K) :
    (⁅A,zpowers k⁆:Subgroup K).map K.subtype=⁅A.map K.subtype,zpowers (k:G)⁆ := by
  rw [map_commutator,MonoidHom.map_zpowers]
  rfl

theorem plane_rows_of_factor [Finite G] (f:G→*Q) (K:Subgroup G) (P:Subgroup Q) (q:ℕ)
    (hc:_root_.commutator G≤center G)
    (hf:Function.Surjective (f.comp K.subtype))
    (hKC:K≤centralizer (f.ker:Set G))
    (hrow:∀a∈P.comap (f.comp K.subtype),
      Nat.card (⁅(⊤:Subgroup K),zpowers a⁆:Subgroup K)≤q)
    (hlift:P.comap f≤centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G))
    (hgeom:∀k:K,(f (k:G))^2=1→f (k:G)∉P→
      q≤Nat.card (⁅P.comap (f.comp K.subtype),zpowers k⁆:Subgroup K) ∧
      Disjoint (⁅P.comap (f.comp K.subtype),zpowers k⁆:Subgroup K) (f.comp K.subtype).ker) :
    (∀v∈(P.comap (f.comp K.subtype)).map K.subtype,
      Nat.card (⁅(⊤:Subgroup G),zpowers v⁆:Subgroup G)≤q) ∧
    (∀w:G,w^2=1→w∉centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G)→
      q≤Nat.card (⁅(P.comap (f.comp K.subtype)).map K.subtype,zpowers w⁆:Subgroup G) ∧
      Disjoint (⁅(P.comap (f.comp K.subtype)).map K.subtype,zpowers w⁆:Subgroup G) f.ker) := by
  let A:=P.comap (f.comp K.subtype)
  let V:=A.map K.subtype
  have hgen:=factor_sup_kernel f K hf
  have hCV:f.ker≤centralizer (V:Set G):=by
    apply le_centralizer_iff.mp
    rintro _ ⟨a,ha,rfl⟩
    exact hKC a.property
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    change Nat.card (⁅(⊤:Subgroup G),zpowers (a:G)⁆:Subgroup G)≤q
    rw [commutator_comm (⊤:Subgroup G),row_card_eq_factor hc K f.ker hgen hKC a,
      commutator_comm (zpowers a)]
    exact hrow a ha
  · intro w hw hn
    obtain ⟨k,hk⟩:=hf (f w)
    change f (k:G)=f w at hk
    let c:=(k:G)⁻¹*w
    have hck:c∈f.ker:=by change f ((k:G)⁻¹*w)=1;rw [map_mul,map_inv,hk,inv_mul_cancel]
    have hcV:=hCV hck
    have hW:w=(k:G)*c:=by simp [c]
    have hft:(f (k:G))^2=1:=by rw [hk,←map_pow,hw,map_one]
    have hnp:f (k:G)∉P:=by
      intro hp
      apply hn
      apply hlift
      change f w∈P
      rwa [←hk]
    obtain ⟨hr,hd⟩:=hgeom k hft hnp
    have he:⁅V,zpowers w⁆=(⁅A,zpowers k⁆:Subgroup K).map K.subtype:=by
      rw [plane_row_map,commutator_comm V,hW,row_mul_centralizer hc V (k:G) c hcV,
        commutator_comm (zpowers (k:G))]
    change q≤Nat.card (⁅V,zpowers w⁆:Subgroup G) ∧ Disjoint (⁅V,zpowers w⁆:Subgroup G) f.ker
    rw [he]
    constructor
    · rwa [card_map_of_injective K.subtype_injective]
    · apply disjoint_def.mpr
      rintro x ⟨a,ha,rfl⟩ hker
      exact congrArg Subtype.val (disjoint_def.mp hd ha (show a∈(f.comp K.subtype).ker from hker))
theorem plane_lift_centralizes (f:G→*Q) (K:Subgroup G) (P:Subgroup Q)
    (hf:Function.Surjective (f.comp K.subtype))
    (hKC:K≤centralizer (f.ker:Set G))
    [IsMulCommutative (P.comap (f.comp K.subtype))] :
    P.comap f≤centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G) := by
  intro x hx
  obtain ⟨k,hk⟩:=hf (f x)
  change f (k:G)=f x at hk
  have hkP:k∈P.comap (f.comp K.subtype):=by change f (k:G)∈P;rw [hk];exact hx
  let c:=(k:G)⁻¹*x
  have hck:c∈f.ker:=by change f ((k:G)⁻¹*x)=1;rw [map_mul,map_inv,hk,inv_mul_cancel]
  have hW:x=(k:G)*c:=by simp [c]
  have hcV:c∈centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G):=by
    rintro _ ⟨a,ha,rfl⟩
    exact (hKC a.property c hck).symm
  have hkV:(k:G)∈centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G):=by
    rintro _ ⟨a,ha,rfl⟩
    let : CommGroup (P.comap (f.comp K.subtype)):=IsMulCommutative.instCommGroup
    exact congrArg (fun y:P.comap (f.comp K.subtype)=>((y:K):G))
      (mul_comm ⟨a,ha⟩ ⟨k,hkP⟩)
  rw [hW]
  exact (centralizer _).mul_mem hkV hcV
end Subgroup.ClassTwo
