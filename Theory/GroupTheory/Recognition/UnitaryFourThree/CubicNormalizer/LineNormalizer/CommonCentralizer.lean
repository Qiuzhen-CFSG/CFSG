module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.LocalProduct
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.ReflectionFixed
/-!
# The common centralizer of the original cubic and fixed four.
Coprime product uniqueness in X Tx identifies it with U S of order12.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem reflected_four_common_centralizer (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
      centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
    let S:=zpowers z⊔zpowers m.t
    normalizer (U:Set G)⊓Subgroup.centralizer (S:Set G)=U⊔S ∧
      Nat.card (normalizer (U:Set G)⊓Subgroup.centralizer (S:Set G):Subgroup G)=12 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let T:=R.cubicSylow X
  let S:=zpowers z⊔zpowers m.t
  have hSc:Nat.card S=4:=(h.reflected_four P m).2
  let : IsElementaryAbelian 2 S:=(h.reflected_four P m).1
  have hUc:Nat.card U=3:=m.common_fixed_card
  have heS:T⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_sylow_fixed h P m ht hs
  have hSC:S≤Subgroup.centralizer (U:Set G):=heS ▸ inf_le_right
  have hSU:U≤Subgroup.centralizer (S:Set G):=le_centralizer_iff.mp hSC
  have hSS:S≤Subgroup.centralizer (S:Set G):=le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hprod:normalizer (U:Set G)⊓Subgroup.centralizer (S:Set G)=U⊔S:=by
    apply le_antisymm ?_ (sup_le (le_inf le_normalizer hSU)
      (le_inf (hSC.trans (centralizer_le_normalizer _)) hSS))
    intro y hy
    have hyH:y∈centralizer z:=mem_centralizer_singleton_iff.mpr (hy.2 z (mem_sup_left (mem_zpowers z))).symm
    have hyXT:y∈X⊔T:=by
      rw[←R.cubic_local_normalizer_product h X (h.cubic_sylow_image_card P) (map_subtype_le _),←hlocal]
      exact ⟨hyH,hy.1⟩
    have hyp:y∈(X:Set G)*(T:Set G):=by
      rw[←coe_mul_of_right_le_normalizer_left X T inf_le_right]
      exact hyXT
    obtain ⟨x,hx,a,ha,rfl⟩:=hyp
    let f:=MulAut.conj m.t
    have he:f (x*a)=x*a:=mul_inv_eq_iff_eq_mul.mpr (hy.2 m.t (mem_sup_right (mem_zpowers m.t)))
    have hfx:f x∈X:=(m.t_normalizes x).mp hx
    have hfa:f a∈T:=(T.le_normalizer ht a).mp ha
    have hd:Disjoint X T:=disjoint_of_coprime_natCard (by
      rw[h.cubic_sylow_image_card P,R.cubicSylow_card h X (h.cubic_sylow_image_card P) (map_subtype_le _)];decide)
    have hep:((⟨f x,hfx⟩:X):G)*((⟨f a,hfa⟩:T):G)=((⟨x,hx⟩:X):G)*((⟨a,ha⟩:T):G):=by simpa only[map_mul] using he
    have hinj:=mul_injective_of_disjoint hd (a₁:=(⟨f x,hfx⟩,⟨f a,hfa⟩)) (a₂:=(⟨x,hx⟩,⟨a,ha⟩)) hep
    have hxf:f x=x:=congrArg (fun p:X×T=>(p.1:G)) hinj
    have haf:f a=a:=congrArg (fun p:X×T=>(p.2:G)) hinj
    have hxU:x∈U:=⟨hx,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxf).symm⟩
    have heT:T⊓Subgroup.centralizer ({m.t}:Set G)=S:=R.cubicSylow_reflection_centralizer h P m ht hs
    have haS:a∈S:=heT ▸
      (show a∈T⊓Subgroup.centralizer ({m.t}:Set G) from
        ⟨ha,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp haf).symm⟩)
    exact mul_mem_sup hxU haS
  refine ⟨hprod,?_⟩
  have hd:U⊓S=⊥:=(disjoint_of_coprime_natCard (by rw[hUc,hSc];decide)).eq_bot
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes U S (hSC.trans (centralizer_le_normalizer _))
  rw[hUc,hSc,hd,card_bot,one_mul] at hc
  rw[hprod,←hc]
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
