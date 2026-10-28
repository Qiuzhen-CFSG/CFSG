module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.KleinFourFactorization.Ambient
/-!
# Recovering an odd kernel from four-group centralizers

A four-group normalizing an odd group factors it through three fixed groups.
If the corresponding common centralizers with a cubic lie in their product,
normalizing the four and cubic preserves that product and its characteristic
normal Sylow three-subgroup. A transitive action on the three nonidentity
actors supplies the centralizer bounds from one order36 centralizer.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem normalizer_four_centralizers_le (V S U:Subgroup G)
    (hV:IsPGroup 3 V) (hVc:Nat.card V=81) (hS:Nat.card S=4)
    (hSV:S≤normalizer (V:Set G)) (hVC:V≤centralizer (U:Set G))
    (a b:G) (ha:a∈S) (hb:b∈S) (ha2:a^2=1) (hb2:b^2=1)
    (hab:Commute a b) (hane:a≠1) (hbne:b≠1) (habne:a*b≠1)
    (hc:∀s∈S,s≠1→centralizer (U:Set G)⊓centralizer ({s}:Set G)≤S⊔V) :
    normalizer (U:Set G)⊓normalizer (S:Set G)≤normalizer (V:Set G) := by
  let J:=S⊔V
  have hJV:J≤normalizer (V:Set G):=sup_le hSV le_normalizer
  have hd:V⊓S=⊥:=(disjoint_of_coprime_natCard (by rw[hVc,hS];decide)).eq_bot
  have hcard:Nat.card J=324 := by
    have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes V S hSV
    rw [hVc,hS,hd,card_bot,one_mul] at hh
    change Nat.card (S⊔V:Subgroup G)=324
    rw [sup_comm,←hh]
  let V':=V.subgroupOf J
  have hVn:V'.Normal := normal_subgroupOf_of_le_normalizer hJV
  have hi:V'.index=4 := by
    have hh:=V'.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show V≤J from le_sup_right)).toEquiv,hVc,hcard] at hh
    omega
  let P:Sylow 3 J := (hV.comap_subtype:IsPGroup 3 V').toSylow (by change ¬3∣V'.index;rw [hi];decide)
  let : V'.Characteristic := P.characteristic_of_normal hVn
  have hNJ:normalizer (J:Set G)≤normalizer (V:Set G) := by
    have hh:=normalizer_le_normalizer_characteristic_image J V'
    rwa [map_subgroupOf_eq_of_le (show V≤J from le_sup_right)] at hh
  apply le_trans ?_ hNJ
  apply le_normalizer_iff.mpr
  intro g hg j hj
  let f:=MulAut.conj g
  have hSmap:S.map f.toMonoidHom=S := mem_normalizer_iff_map_conj_eq.mp hg.2
  have hSC:S≤J := le_sup_left
  have hfix (s:G) (hs:s∈S) (hsne:s≠1) (v:G)
      (hv:v∈V⊓centralizer ({s}:Set G)) : f v∈J := by
    have hgv:f v∈centralizer (U:Set G) :=
      ((normalizer_le_normalizer_centralizer U hg.1) v).mp (hVC hv.1)
    have hgs:f s∈S := hSmap ▸ mem_map_of_mem f.toMonoidHom hs
    have hgne:f s≠1 := fun he=>hsne (f.injective (he.trans (map_one f).symm))
    have hcomm:f v∈centralizer ({f s}:Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      rw [←map_mul,←map_mul]
      exact congrArg f (mem_centralizer_singleton_iff.mp hv.2)
    exact hc (f s) hgs hgne ⟨hgv,hcomm⟩
  have hVle:V≤J.comap f.toMonoidHom := by
    intro v hv
    let an:normalizer (V:Set G):=⟨a,hSV ha⟩
    let bn:normalizer (V:Set G):=⟨b,hSV hb⟩
    obtain ⟨u,hu,w,hw,y,hy,rfl⟩:=V.exists_three_odd_centralizers (by rw[hVc];decide)
      an bn (Subtype.ext ha2) (Subtype.ext hb2) (Subtype.ext hab.eq) v hv
    change f (u*w*y)∈J
    rw [map_mul,map_mul]
    exact J.mul_mem (J.mul_mem (hfix a ha hane u hu) (hfix b hb hbne w hw))
      (hfix (a*b) (S.mul_mem ha hb) habne y hy)
  have hSle:S≤J.comap f.toMonoidHom := fun s hs=>hSC (hSmap ▸ mem_map_of_mem f.toMonoidHom hs)
  exact (sup_le hSle hVle) hj
end Subgroup

open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem four_fixed_centralizer_of_orbit (U S V:Subgroup G) [IsMulCommutative S]
    (hS:Nat.card S=4) (hSV:S≤normalizer (V:Set G))
    (hSC:S≤centralizer (U:Set G)) (hVC:V≤centralizer (U:Set G))
    (z:G) (_hz:z∈S) (_hz1:z≠1)
    (hc:Nat.card (centralizer (U:Set G)⊓centralizer ({z}:Set G):Subgroup G)=36)
    (hfixed:∀s∈S,s≠1→Nat.card (V⊓centralizer ({s}:Set G):Subgroup G)=9)
    (horb:∀s∈S,s≠1→∃w∈normalizer (U:Set G),w*z*w⁻¹=s) :
    ∀s∈S,s≠1→centralizer (U:Set G)⊓centralizer ({s}:Set G)≤S⊔V := by
  intro s hs hs1
  let F:=V⊓centralizer ({s}:Set G)
  have hSF:S≤centralizer ({s}:Set G):=fun a ha=>mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm' (⟨a,ha⟩:S) (⟨s,hs⟩:S)))
  have hFN:S≤normalizer (F:Set G):=by
    apply le_trans (le_inf hSV ?_) inf_normalizer_le_normalizer_inf
    exact hSF.trans le_normalizer
  have hF:Nat.card F=9:=hfixed s hs hs1
  have hd:F⊓S=⊥:=(disjoint_of_coprime_natCard (by rw[hF,hS];decide)).eq_bot
  have hprod:Nat.card (S⊔F:Subgroup G)=36:=by
    have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes F S hFN
    rw[hF,hS,hd,card_bot,one_mul] at hh
    rw[sup_comm,←hh]
  have hle:S⊔F≤centralizer (U:Set G)⊓centralizer ({s}:Set G):=
    sup_le (le_inf hSC hSF) (le_inf (inf_le_left.trans hVC) inf_le_right)
  have hcard:Nat.card (centralizer (U:Set G)⊓centralizer ({s}:Set G):Subgroup G)=36:=by
    obtain ⟨w,hw,he⟩:=horb s hs hs1
    have hh:=(centralizer (U:Set G)).card_inf_centralizer_conj w
      (normalizer_le_normalizer_centralizer U hw) z
    rw[he] at hh
    exact hh.symm.trans hc
  have he:S⊔F=centralizer (U:Set G)⊓centralizer ({s}:Set G):=
    eq_of_le_of_card_ge hle (by rw[hprod,hcard])
  rw[←he]
  exact sup_le_sup_left inf_le_left _
end Subgroup
