module
public import Stellmacher.ElementaryAbelianMaxPair.Normalizers
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.DisjointCommutingProduct
/-! # The centralizing core fixes every elementary maximum
Suppose J(S)=K R, where R=J(S) intersect C is elementary and C centralizes K.
Every maximum elementary subgroup absorbs R. Conjugation by C fixes its
K-coordinate and preserves R, so C normalizes each member of the family.
This supplies the original core-normalization premise in the p.555
normalizer argument, without assuming it as part of a local configuration.
Source: Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
variable {G:Type*} [Group G] [Finite G]
theorem maxFamily_core_normalizes (S K C:Subgroup G)
    (hCS:C≤S) (hKC:C≤centralizer (K:Set G))
    (hJ:elementaryAbelianMaxJ S=K⊔(elementaryAbelianMaxJ S⊓C))
    [IsElementaryAbelian 2 (elementaryAbelianMaxJ S⊓C:Subgroup G)]
    {A:Subgroup G} (hA:A∈elementaryAbelianMaxSubgroups S) : C≤normalizer (A:Set G) := by
  let R:=elementaryAbelianMaxJ S⊓C
  have hRJ:R≤elementaryAbelianMaxJ S:=inf_le_left
  have hJS:elementaryAbelianMaxJ S≤S:=sSup_le fun _ h=>h.1
  have hAJ:A≤elementaryAbelianMaxJ S:=le_sSup hA
  have hCR:C≤normalizer (R:Set G):=by
    intro c hc
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ S⊓C).map (MulAut.conj c).toMonoidHom=elementaryAbelianMaxJ S⊓C
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective]
    have hs:S.map (MulAut.conj c).toMonoidHom=S:=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (hCS hc))
    rw [←elementaryAbelianMaxJ_map_equiv,hs]
    have ht:C.map (MulAut.conj c).toMonoidHom=C:=mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer hc)
    rw [ht]
  have hRK:R≤centralizer (K:Set G):=inf_le_right.trans hKC
  have hRR:R≤centralizer (R:Set G):=by
    intro r hr u hu
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=R)).comm ⟨u,hu⟩ ⟨r,hr⟩)
  have hRA:R≤centralizer (A:Set G):=by
    apply le_trans _ (centralizer_le hAJ)
    apply le_centralizer_iff.mpr
    rw [hJ]
    exact sup_le (le_centralizer_iff.mp hRK) hRR
  have hRAle:R≤A:=by
    let : IsElementaryAbelian 2 A:=hA.2.1
    let : IsElementaryAbelian 2 (A⊔R:Subgroup G):=IsElementaryAbelian.sup_of_le_centralizer hRA
    have he:A=A⊔R:=eq_of_le_of_card_ge le_sup_left
      (hA.2.2 _ (sup_le hA.1 (hRJ.trans hJS)) inferInstance)
    exact he.symm ▸ le_sup_right
  apply le_normalizer_iff.mpr
  intro c hc a ha
  have haJ:a∈K⊔R:=hJ ▸ hAJ ha
  have haP:a∈(K:Set G)*(R:Set G):=by
    rw [←coe_mul_of_right_le_normalizer_left K R (hRK.trans (Subgroup.centralizer_le_normalizer _))]
    exact haJ
  obtain ⟨k,hk,r,hr,he⟩:=haP
  have hkA:k∈A:=by
    have hh:=A.mul_mem ha (A.inv_mem (hRAle hr))
    rw [←he,mul_inv_cancel_right] at hh
    exact hh
  have hfix:c*k*c⁻¹=k:=by
    have hh:=hKC hc k hk
    calc
      _=k*c*c⁻¹:=by rw [←hh]
      _=k:=mul_inv_cancel_right _ _
  have hr':c*r*c⁻¹∈R:=((hCR hc) r).mp hr
  rw [←he]
  have hrew:c*(k*r)*c⁻¹=(c*k*c⁻¹)*(c*r*c⁻¹):=by group
  rw [hrew,hfix]
  exact A.mul_mem hkA (hRAle hr')
end Stellmacher
