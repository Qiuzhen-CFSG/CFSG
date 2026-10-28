module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Elementary
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Reflections
public import Theory.GroupAction.DihedralCentralNine
/-!
# Elementary structure of the reflected cubic kernel

Apply the canonical odd-kernel decomposition to the actual reflection action.
The two odd involution centralizers are elementary nines and generate the
kernel over its central fixed nine. The dihedral commutator argument proves
that the entire kernel is elementary. The order-nine possibility remains for
the independently proved A₆ normalizer to exclude.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma45.7, printed p.245.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
omit [Finite G] in
private theorem map_singleton_centralizer (e : MulAut G) (a : G) :
    (Subgroup.centralizer ({a}:Set G)).map e.toMonoidHom=Subgroup.centralizer ({e a}:Set G) := by
  ext x
  obtain ⟨y,rfl⟩ := e.surjective x
  change e.toMonoidHom y∈(Subgroup.centralizer ({a}:Set G)).map e.toMonoidHom ↔ _
  rw [mem_map_iff_mem (f:=e.toMonoidHom) e.injective]
  simp only [mem_centralizer_singleton_iff]
  rw [←map_mul,←map_mul,e.injective.eq_iff]
namespace IsType
variable (h : IsType z) (X : Subgroup G) (hX : Nat.card X=9) (hXH : X≤centralizer z)
include h hX hXH in
theorem cubic_oddKernel_elementary (t s : G)
    (ht : orderOf t=2) (hs : orderOf s=2) (htN : t∈normalizer (X:Set G))
    (hzt : Commute z t) (htz : IsConj z t)
    (hsN : s∈normalizer (X:Set G)) (hst : s*t*s⁻¹=t*z)
    (hXt : Nat.card (X⊓Subgroup.centralizer ({t}:Set G) : Subgroup G)=3)
    (hr : ∀x∈X,(s*t)*x*(s*t)⁻¹=x⁻¹) : IsElementaryAbelian 3 (CubicNormalizer.oddKernel X) := by
  let V := CubicNormalizer.oddKernel X
  let F := V⊓Subgroup.centralizer ({t}:Set G)
  have ho := CubicNormalizer.oddKernel_odd X
  have hVZ : V⊓centralizer z=X := h.toCentralizerHypothesis.cubic_oddKernel_fixed X hX hXH
  have hXV : X≤V := hVZ ▸ inf_le_left
  let : IsElementaryAbelian 3 X := h.toCentralizerHypothesis.nine_elementary X hX hXH
  obtain ⟨hFc,hcard⟩ := h.cubic_oddKernel_reflection_count X hX hXH t s ht htN hzt htz hsN hst hXt
  rcases hFc with hF3 | hF9
  · have hV9 : Nat.card V=9 := by rw [hcard,hF3]; norm_num
    have he : X=V := eq_of_le_of_card_ge hXV (by rw [hX,hV9])
    change IsElementaryAbelian 3 V
    rw [←he]
    infer_instance
  have hFodd : Odd (Nat.card F) := Odd.of_dvd_nat ho (card_dvd_of_le inf_le_left)
  let : IsElementaryAbelian 3 F := h.odd_subgroup_elementary_of_isConj t htz F hFodd inf_le_right
  have htV := CubicNormalizer.normalizer_normalizes_oddKernel X htN
  have hsV := CubicNormalizer.normalizer_normalizes_oddKernel X hsN
  have hzX : z∈Subgroup.centralizer (X:Set G) := fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx)
  have hzV := CubicNormalizer.normalizer_normalizes_oddKernel X ((centralizer_le_normalizer _) hzX)
  let sn : normalizer (V:Set G) := ⟨s,hsV⟩
  let tn : normalizer (V:Set G) := ⟨t,htV⟩
  let zn : normalizer (V:Set G) := ⟨z,hzV⟩
  let sa := V.normalizerMonoidHom sn
  let ta := V.normalizerMonoidHom tn
  let za := V.normalizerMonoidHom zn
  let A := F.subgroupOf V
  let Z := X.subgroupOf V
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.subgroupOf inf_le_left
  let : IsElementaryAbelian 3 Z := IsElementaryAbelian.subgroupOf hXV
  have hZmap : Z.map V.subtype=X := map_subgroupOf_eq_of_le hXV
  have hAmap : A.map V.subtype=F := map_subgroupOf_eq_of_le inf_le_left
  have hZc : Z≤center V := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (((map_subtype_le _ : V≤Subgroup.centralizer (X:Set G)) y.property) x hx).symm
  have hZ9 : Nat.card Z=9 := (Nat.card_congr (subgroupOfEquivOfLe hXV).toEquiv).trans hX
  have hA9 : Nat.card A=9 := (Nat.card_congr (subgroupOfEquivOfLe (show F≤V from inf_le_left)).toEquiv).trans hF9
  have hZA : Nat.card (Z⊓A : Subgroup V)=3 := by
    rw [←card_map_of_injective V.subtype_injective,map_inf _ _ _ V.subtype_injective,hZmap,hAmap]
    change Nat.card (X⊓(V⊓Subgroup.centralizer ({t}:Set G)) : Subgroup G)=3
    rw [←inf_assoc,inf_of_le_left hXV]
    exact hXt
  have hs2 : sn^2=1 := Subtype.ext (by exact hs ▸ pow_orderOf_eq_one s)
  have ht2 : tn^2=1 := Subtype.ext (by exact ht ▸ pow_orderOf_eq_one t)
  have hz2 : zn^2=1 := Subtype.ext (by exact h.involution ▸ pow_orderOf_eq_one z)
  have hsa : Function.Involutive sa := fun x=>DFunLike.congr_fun
    (show sa^2=1 by rw [←map_pow,hs2,map_one]) x
  have hta : Function.Involutive ta := fun x=>DFunLike.congr_fun
    (show ta^2=1 by rw [←map_pow,ht2,map_one]) x
  have hcompat : V.subtype.comp sa.toMonoidHom=(MulAut.conj s).toMonoidHom.comp V.subtype := by ext x; rfl
  have hBmap : (A.map sa.toMonoidHom).map V.subtype=F.map (MulAut.conj s).toMonoidHom := by
    rw [map_map,hcompat,←map_map,hAmap]
  have hVm : V.map (MulAut.conj s).toMonoidHom=V := mem_normalizer_iff_map_conj_eq.mp hsV
  have hXm : X.map (MulAut.conj s).toMonoidHom=X := mem_normalizer_iff_map_conj_eq.mp hsN
  have hB : F.map (MulAut.conj s).toMonoidHom=V⊓Subgroup.centralizer ({t*z}:Set G) := by
    change (V⊓Subgroup.centralizer ({t}:Set G)).map _=_
    rw [map_inf _ _ _ (MulAut.conj s).injective,hVm,
      map_singleton_centralizer]
    change V⊓Subgroup.centralizer ({s*t*s⁻¹}:Set G)=_
    rw [hst]
  have hsZ : Z.map sa.toMonoidHom=Z := by
    apply map_injective V.subtype_injective
    rw [map_map,hcompat,←map_map,hZmap,hXm]
  have hgenG : (X⊔F)⊔F.map (MulAut.conj s).toMonoidHom=V := by
    apply le_antisymm (sup_le (sup_le hXV inf_le_left) (hB ▸ inf_le_left))
    intro v hv
    obtain ⟨x,hx,y,hy,w,hw,rfl⟩ := V.exists_three_odd_centralizers ho zn tn hz2 ht2
      (show Commute zn tn from Subtype.ext hzt.eq) v hv
    change x∈V⊓centralizer z at hx
    rw [hVZ] at hx
    change w∈V⊓Subgroup.centralizer ({z*t}:Set G) at hw
    have hw' : w∈F.map (MulAut.conj s).toMonoidHom := by rw [hB,←hzt.eq]; exact hw
    exact ((X⊔F)⊔F.map (MulAut.conj s).toMonoidHom).mul_mem
      (((X⊔F)⊔F.map (MulAut.conj s).toMonoidHom).mul_mem
        (mem_sup_left (mem_sup_left hx)) (mem_sup_left (mem_sup_right hy))) (mem_sup_right hw')
  have hgen : (Z⊔A)⊔A.map sa.toMonoidHom=⊤ := by
    apply map_injective V.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,hZmap,hAmap,hBmap,
      ←MonoidHom.range_eq_map,V.range_subtype]
    exact hgenG
  have hc : _root_.commutator V≤Z := by
    intro x hx
    have hh := mem_map_of_mem V.subtype hx
    rw [map_commutator_eq,V.range_subtype] at hh
    exact (h.toCentralizerHypothesis.cubic_oddKernel_inversion X hX hXH).2 hh
  apply MulAut.elementary_of_dihedral_central_nines Z A hZc hZ9 hA9 hZA sa ta hsa hsZ hgen hc
  · intro a ha
    apply Subtype.ext
    change t*(a:G)*t⁻¹=(a:G)
    rw [←mem_centralizer_singleton_iff.mp (show (a:G)∈Subgroup.centralizer ({t}:Set G) from ha.2),mul_inv_cancel_right]
  · intro b hb
    have hbG : (b:G)∈V⊓Subgroup.centralizer ({t*z}:Set G) := by
      rw [←hB,←hBmap]
      exact mem_map_of_mem V.subtype hb
    have hfix : ta (za b)=b := by
      apply Subtype.ext
      change t*(z*(b:G)*z⁻¹)*t⁻¹=(b:G)
      calc
        t*(z*(b:G)*z⁻¹)*t⁻¹ = (t*z)*(b:G)*(t*z)⁻¹ := by group
        _ = b := by rw [←mem_centralizer_singleton_iff.mp hbG.2,mul_inv_cancel_right]
    have he : za b=ta b := (hta (za b)).symm.trans (congrArg ta hfix)
    change (ta b:G)*(b:G)∈X
    rw [←he]
    exact (h.toCentralizerHypothesis.cubic_oddKernel_inversion X hX hXH).1 b b.property
  · intro x hx
    apply Subtype.ext
    change s*(t*(x:G)*t⁻¹)*s⁻¹=(x:G)⁻¹
    calc
      s*(t*(x:G)*t⁻¹)*s⁻¹ = (s*t)*(x:G)*(s*t)⁻¹ := by group
      _ = (x:G)⁻¹ := hr x hx
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
