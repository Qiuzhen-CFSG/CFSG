module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ResidualNormalizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Frattini

/-!
# The literal cubic normalizer in the involution centralizer

Frattini applied to the actual two-residual proves H = Q N_H(X).
Independent cubic actions identify Q ∩ N_H(X) with the marked central
involution, so the original order1152 hypothesis gives |N_H(X)| = 72.
These are the source inputs to the dihedral reflection construction.

Source: Aschbacher, Sporadic Groups,45.3(5), printed p.243.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G]

private theorem relative_frattini {p : ℕ} [Fact p.Prime]
    (H W : Subgroup G) (hHW : H≤W) (hWH : W≤normalizer (H:Set G))
    (R : Sylow p H) :
    W=(W⊓normalizer ((R:Subgroup H).map H.subtype:Set G))⊔H := by
  let H' := H.subgroupOf W
  let : H'.Normal := (normal_subgroupOf_iff_le_normalizer hHW).mpr hWH
  let e : H≃*H' := (subgroupOfEquivOfLe hHW).symm
  let R' : Sylow p H' := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  let A := (R:Subgroup H).map H.subtype
  have hAW : A≤W := (map_subtype_le _).trans hHW
  have hm : ((R':Subgroup H').map H'.subtype).map W.subtype=A := by
    change (((R:Subgroup H).map e.toMonoidHom).map H'.subtype).map W.subtype=_
    rw [map_map,map_map]
    rfl
  have he : (R':Subgroup H').map H'.subtype=A.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [hm,map_subgroupOf_eq_of_le hAW]
  have hf := congrArg (fun K:Subgroup W=>K.map W.subtype) R'.normalizer_sup_eq_top
  rw [Subgroup.map_sup,he,←subgroupOf_normalizer_eq hAW,subgroupOf_map_subtype,
    ←MonoidHom.range_eq_map,W.range_subtype,subgroupOf_map_subtype,inf_of_le_left hHW] at hf
  simpa only [inf_comm] using hf.symm

namespace IsType
variable {z : G} (h : IsType z) (X : Subgroup G)
    (hX : Nat.card X=9) (hXH : X≤centralizer z)
include h hX hXH

theorem core_cubic_normalizer_intersection :
    core z ⊓ normalizer (X:Set G) = zpowers z := by
  have hQC : core z⊓normalizer (X:Set G)≤Subgroup.centralizer (X:Set G) :=
    (inf_le_inf_right _ (pCoreIn_le 2 (residual z))).trans
      (h.toCentralizerHypothesis.residual_normalizer_centralizes_cubic X hX hXH)
  have hd : Disjoint (core z) X := disjoint_of_coprime_natCard
    (by rw [h.toCentralizerHypothesis.core_card,hX]; decide)
  have hzX : zpowers z≤Subgroup.centralizer (X:Set G) :=
    zpowers_le.mpr (fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx))
  apply le_antisymm
  · intro g hg
    have hgC : g∈X⊔zpowers z := h.toCentralizerHypothesis.cubic_centralizer X hX hXH ▸
      ⟨RootPair.core_le_centralizer hg.1,hQC hg⟩
    have hp : g∈(X:Set G)*(zpowers z:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right X (zpowers z)
        ((le_centralizer_iff.mp hzX).trans (centralizer_le_normalizer _))]
      exact hgC
    obtain ⟨x,hx,w,hw,rfl⟩ := hp
    have hxQ : x∈core z := by
      simpa using (core z).mul_mem hg.1 ((core z).inv_mem (h.toCentralizerHypothesis.line_le_core hw))
    have hx1 : x=1 := Subgroup.mem_bot.mp (hd.eq_bot ▸ show x∈core z⊓X from ⟨hxQ,hx⟩)
    change x*w∈zpowers z
    rw [hx1,one_mul]
    exact hw
  · exact le_inf h.toCentralizerHypothesis.line_le_core
      (hzX.trans (centralizer_le_normalizer _))

theorem centralizer_eq_core_sup_cubic_normalizer :
    centralizer z = core z ⊔ (centralizer z⊓normalizer (X:Set G)) := by
  have hXR : X≤residual z := CentralizerHypothesis.cubic_le_residual X hX hXH
  let S : Sylow 3 (residual z) := Sylow.ofCard (X.subgroupOf (residual z)) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXR).toEquiv,hX,h.toCentralizerHypothesis.residual_card]
    decide +kernel)
  have hm : (S:Subgroup (residual z)).map (residual z).subtype=X :=
    map_subgroupOf_eq_of_le hXR
  have hf := relative_frattini (residual z) (centralizer z) (map_subtype_le _)
    CentralizerHypothesis.centralizer_normalizes_residual S
  rw [hm,h.toCentralizerHypothesis.residual_eq_core_sup_cubic X hX hXH] at hf
  have hXN : X≤centralizer z⊓normalizer (X:Set G) := le_inf hXH X.le_normalizer
  calc
    centralizer z = (centralizer z⊓normalizer (X:Set G))⊔(core z⊔X) := hf
    _ = core z⊔((centralizer z⊓normalizer (X:Set G))⊔X) := by ac_rfl
    _ = _ := by rw [sup_eq_left.mpr hXN]

theorem cubic_local_normalizer_card :
    Nat.card (centralizer z⊓normalizer (X:Set G) : Subgroup G)=72 := by
  have hn : centralizer z⊓normalizer (X:Set G)≤normalizer (core z:Set G) :=
    inf_le_left.trans CentralizerHypothesis.centralizer_normalizes_core
  have hi : core z⊓(centralizer z⊓normalizer (X:Set G))=zpowers z := by
    rw [←inf_assoc,inf_eq_left.mpr RootPair.core_le_centralizer,h.core_cubic_normalizer_intersection X hX hXH]
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (core z)
    (centralizer z⊓normalizer (X:Set G)) hn
  rw [hi,←h.centralizer_eq_core_sup_cubic_normalizer X hX hXH,
    h.toCentralizerHypothesis.core_card,h.centralizer_card,Nat.card_zpowers,h.involution] at hc
  omega
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
