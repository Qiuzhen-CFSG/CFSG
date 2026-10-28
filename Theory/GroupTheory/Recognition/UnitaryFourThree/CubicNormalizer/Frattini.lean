module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Source
/-!
# Frattini decomposition for the original cubic normalizer

The order-two Sylow subgroup of the cubic centralizer is the marked line.
Frattini’s argument therefore decomposes the full cubic normalizer into
its canonical odd kernel and its intersection with C_G(z). The final theorem
applies to an actual Sylow-three subgroup of the IsType involution centralizer.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.7, printed p.245.
-/

@[expose] public section
open Subgroup
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
namespace CentralizerHypothesis
variable {z:G} (h : CentralizerHypothesis z) (X : Subgroup G)
  (hX : Nat.card X=9) (hXH : X≤centralizer z)
include h hX hXH in
theorem cubic_normalizer_split :
    normalizer (X:Set G)=CubicNormalizer.oddKernel X⊔(normalizer (X:Set G)⊓centralizer z) := by
  let N := normalizer (X:Set G)
  let C := Subgroup.centralizer (X:Set G)
  obtain ⟨S,hS⟩ := CubicNormalizer.exists_centralizer_sylow h X hX hXH
    (h.cubic_centralizer X hX hXH)
  have hf := relative_frattini C N (centralizer_le_normalizer _)
    (normalizer_le_normalizer_centralizer X) S
  rw [hS,normalizer_zpowers_eq_centralizer_of_order_two z h.involution] at hf
  change N=(N⊓centralizer z)⊔C at hf
  rw [show C=Subgroup.centralizer (X:Set G) from rfl,
    h.cubic_centralizer_split X hX hXH] at hf
  have hzC : z∈Subgroup.centralizer (X:Set G) :=
    fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx)
  have hz : zpowers z≤N⊓centralizer z := le_inf
    ((zpowers_le.mpr hzC).trans
      (centralizer_le_normalizer _))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  calc
    N = (N⊓centralizer z)⊔(CubicNormalizer.oddKernel X⊔zpowers z) := hf
    _ = CubicNormalizer.oddKernel X⊔((N⊓centralizer z)⊔zpowers z) := by ac_rfl
    _ = CubicNormalizer.oddKernel X⊔(N⊓centralizer z) := by rw [sup_eq_left.mpr hz]
end CentralizerHypothesis
namespace IsType
variable {z:G} (h : IsType z) (P : Sylow 3 (centralizer z))
include h in
theorem cubic_sylow_image_card :
    Nat.card ((P:Subgroup (centralizer z)).map (centralizer z).subtype)=9 := by
  rw [card_map_of_injective (centralizer z).subtype_injective,P.card_eq_multiplicity,
    h.centralizer_card]
  decide +kernel
include h in
theorem cubic_sylow_structure :
    let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V := CubicNormalizer.oddKernel X
    Odd (Nat.card V) ∧
      Subgroup.centralizer (X:Set G)=V⊔zpowers z ∧
      normalizer (X:Set G)=V⊔(normalizer (X:Set G)⊓centralizer z) ∧
      normalizer (X:Set G)≤normalizer (V:Set G) ∧
      V⊓centralizer z=X ∧ (∀v∈V,z*v*z⁻¹*v∈X) ∧ ⁅V,V⁆≤X := by
  dsimp only
  let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hX : Nat.card X=9 := h.cubic_sylow_image_card P
  have hXH : X≤centralizer z := map_subtype_le _
  let h0 := h.toCentralizerHypothesis
  exact ⟨CubicNormalizer.oddKernel_odd X,h0.cubic_centralizer_split X hX hXH,
    h0.cubic_normalizer_split X hX hXH,CubicNormalizer.normalizer_normalizes_oddKernel X,
    h0.cubic_oddKernel_fixed X hX hXH,h0.cubic_oddKernel_inversion X hX hXH⟩
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
