module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Four
/-!
# The original local U normalizer is X Tx and its centralizer is X S of order36.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem cubic_local_normalizer_product (R:RootPair z) (h:IsType z)
    (X:Subgroup G) (hX:Nat.card X=9) (hXH:X≤centralizer z) :
    centralizer z⊓normalizer (X:Set G)=X⊔R.cubicSylow X := by
  have hTL:R.cubicSylow X≤centralizer z⊓normalizer (X:Set G):=
    le_inf (inf_le_left.trans R.T_le_centralizer) inf_le_right
  have hXL:X≤centralizer z⊓normalizer (X:Set G):=le_inf hXH le_normalizer
  have hT:Nat.card (R.cubicSylow X)=8:=R.cubicSylow_card h X hX hXH
  have hd:X⊓R.cubicSylow X=⊥:=(disjoint_of_coprime_natCard (by rw[hX,hT];decide)).eq_bot
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes X (R.cubicSylow X) inf_le_right
  rw [hX,hT,hd,card_bot,one_mul] at hc
  exact (eq_of_le_of_card_ge (sup_le hXL hTL) (by
    rw [h.cubic_local_normalizer_card X hX hXH,←hc])).symm

theorem reflected_line_local_centralizer_product (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
      centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
    centralizer z⊓Subgroup.centralizer (U:Set G)=X⊔(zpowers z⊔zpowers m.t) ∧
      Nat.card (centralizer z⊓Subgroup.centralizer (U:Set G):Subgroup G)=36 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let T:=R.cubicSylow X
  let S:=zpowers z⊔zpowers m.t
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  let :=h.toCentralizerHypothesis.nine_elementary X hX hXH
  have hXC:X≤Subgroup.centralizer (U:Set G):=by
    intro x hx u hu
    exact congrArg Subtype.val (mul_comm' (⟨u,hu.1⟩:X) (⟨x,hx⟩:X))
  have hfixed:T⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_sylow_fixed h P m ht hs
  have hST:S≤T:=hfixed ▸ inf_le_left
  have hSC:S≤Subgroup.centralizer (U:Set G):=hfixed ▸ inf_le_right
  have he:centralizer z⊓Subgroup.centralizer (U:Set G)=X⊔S := by
    apply le_antisymm ?_ (sup_le (le_inf hXH hXC)
      (le_inf (hST.trans (inf_le_left.trans R.T_le_centralizer)) hSC))
    intro y hy
    have hyN:y∈centralizer z⊓normalizer (U:Set G):=⟨hy.1,(centralizer_le_normalizer _) hy.2⟩
    have hyXT:y∈X⊔T:=by
      rw [←R.cubic_local_normalizer_product h X hX hXH,←hlocal]
      exact hyN
    have hyprod:y∈(X:Set G)*(T:Set G):=by
      rw [←coe_mul_of_right_le_normalizer_left X T inf_le_right]
      exact hyXT
    obtain ⟨x,hx,t,htT,rfl⟩:=hyprod
    have htC:t∈Subgroup.centralizer (U:Set G):=
      ((Subgroup.centralizer (U:Set G)).mul_mem_cancel_left (hXC hx)).mp hy.2
    exact mul_mem_sup hx (hfixed ▸ (show t∈T⊓Subgroup.centralizer (U:Set G) from ⟨htT,htC⟩))
  refine ⟨he,?_⟩
  have hS:Nat.card S=4:=(h.reflected_four P m).2
  have hd:X⊓S=⊥:=(disjoint_of_coprime_natCard (by rw[hX,hS];decide)).eq_bot
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes X S (hST.trans inf_le_right)
  rw [hX,hS,hd,card_bot,one_mul] at hc
  rw [he,←hc]
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
