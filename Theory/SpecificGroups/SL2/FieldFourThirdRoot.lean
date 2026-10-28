module
public import Theory.SpecificGroups.SL2.FieldFourCubicSubgroups
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.SpecificGroups.SL2.OddSylowCentralizer
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The cubic-normalized third root in the field-four obstruction

A proper subgroup of SL₂(4) meeting two different root groups nontrivially
has trivial two-core. If one of its cubics normalizes a third root, its
intersection with that root is either trivial or the entire root: an
invariant subgroup of order two would centralize the cubic. The entire
root is impossible, since a proper overgroup lies in its Borel and would
then have nontrivial two-core.

This retains the actual root subgroups and cubic. It is the rank-one
obstruction used by the terminal-centralizer argument of DGS (10.8),
Groups and Graphs (1985), printed p.161. The companion source application
uses the literal beta quotient; no finite computation or model tag is
substituted for the subgroup argument.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem sylow_eq_of_shared (R T : Sylow 2 SL(2,F))
    (A : Subgroup SL(2,F)) (hAR : A≤R) (hAT : A≤T) (hA : A≠⊥) : R=T := by
  let e := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let R' := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  let T' := T.mapSurjective (f:=e.toMonoidHom) e.surjective
  have he : R'=T' := Theory.PSL2.sylow_eq_of_inf_ne_bot R' T' (by
    change (R:Subgroup SL(2,F)).map e.toMonoidHom⊓
      (T:Subgroup SL(2,F)).map e.toMonoidHom≠⊥
    rw [←map_inf (R:Subgroup SL(2,F)) (T:Subgroup SL(2,F)) e.toMonoidHom e.injective]
    intro hz
    have hh := (map_eq_bot_iff_of_injective _ e.injective).mp hz
    exact hA (le_bot_iff.mp (hh ▸ le_inf hAR hAT)))
  apply Sylow.ext
  exact Subgroup.map_injective e.injective (congrArg Sylow.toSubgroup he)

private theorem distinct_roots_core_bot
    (R T : Sylow 2 SL(2,F)) (hne : R≠T)
    (A B H : Subgroup SL(2,F)) (hAR : A≤R) (hBT : B≤T)
    (hAH : A≤H) (hBH : B≤H) (hA : A≠⊥) (hB : B≠⊥) : pCore 2 H=⊥ := by
  by_contra hc
  let N := (pCore 2 H).map H.subtype
  obtain ⟨U,hU⟩ := ((pCore_isPGroup (p:=2) (G:=H)).map H.subtype).exists_le_sylow
  have hAN : A≤N := by
    have hh := isPGroup_le_twoCore_of_ne_bot H hc (A.subgroupOf H)
      ((R.isPGroup'.to_le hAR).comap_subtype)
    simpa only [map_subgroupOf_eq_of_le hAH] using map_mono (f:=H.subtype) hh
  have hBN : B≤N := by
    have hh := isPGroup_le_twoCore_of_ne_bot H hc (B.subgroupOf H)
      ((T.isPGroup'.to_le hBT).comap_subtype)
    simpa only [map_subgroupOf_eq_of_le hBH] using map_mono (f:=H.subtype) hh
  exact hne ((sylow_eq_of_shared R U A hAR (hAN.trans hU) hA).trans
    (sylow_eq_of_shared T U B hBT (hBN.trans hU) hB).symm)

private theorem cubic_invariant_root
    (hF : Nat.card F=4) (R : Sylow 2 SL(2,F))
    (A : Subgroup SL(2,F)) (hAR : A≤R) (hA : A≠⊥)
    (d : SL(2,F)) (hd : d≠1) (hd3 : d^3=1)
    (hdA : d∈normalizer (A:Set SL(2,F))) : A=R := by
  have hR : Nat.card R=4 :=
    (Nat.card_congr (sylowEquivAdditive F 2 R).toEquiv).symm.trans hF
  obtain ⟨n,hn⟩ := (R.isPGroup'.to_le hAR).exists_card_eq
  change Nat.card A=2^n at hn
  have hge : 2≤n := by
    by_contra hlt
    have casesn : n=0 ∨ n=1 := by omega
    rcases casesn with rfl|rfl
    · exact hA ((card_eq_one).mp (by simpa only [pow_zero] using hn))
    · obtain ⟨⟨a,ha⟩,ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
      have ha1 : a≠1 := fun he => ha1' (Subtype.ext he)
      have hda := normalizer_le_centralizer_of_card_two A
        (by simpa only [pow_one] using hn) hdA a ha
      exact ha1 (eq_one_of_sylow_commutes_nontrivial_odd R a d (hAR ha)
        hd (by decide : Odd 3) hd3 hda)
  exact eq_of_le_of_card_ge hAR (by rw [hR,hn]; exact (show 2^2≤2^n from Nat.pow_le_pow_right (by decide : 0<2) hge))

/-- In a proper field-four subgroup meeting two distinct roots, a cubic
normalizes only roots that have trivial intersection with that subgroup. -/
theorem field_four_cubic_third_root_trivial
    (hF : Nat.card F=4) (H : Subgroup SL(2,F)) (hH : H≠⊤)
    (R T U : Sylow 2 SL(2,F)) (hne : R≠T)
    (A B : Subgroup SL(2,F)) (hAR : A≤R) (hBT : B≤T)
    (hAH : A≤H) (hBH : B≤H) (hA : A≠⊥) (hB : B≠⊥)
    (d : SL(2,F)) (hdH : d∈H) (hd : d≠1) (hd3 : d^3=1)
    (hdU : d∈normalizer (U:Set SL(2,F))) : H⊓(U:Subgroup SL(2,F))=⊥ := by
  have hcore := distinct_roots_core_bot R T hne A B H hAR hBT hAH hBH hA hB
  by_contra hne'
  have hdI : d∈normalizer ((H⊓(U:Subgroup SL(2,F)):Subgroup SL(2,F)):Set SL(2,F)) :=
    inf_normalizer_le_normalizer_inf ⟨H.le_normalizer hdH,hdU⟩
  have hI := cubic_invariant_root hF U (H⊓(U:Subgroup SL(2,F))) inf_le_right hne'
    d hd hd3 hdI
  have hUH : (U:Subgroup SL(2,F))≤H := hI ▸ inf_le_left
  have hHN := proper_overgroup_le_sylow_normalizer U H hUH hH
  let N := (U:Subgroup SL(2,F)).subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer hHN
  have hN : IsPGroup 2 N := U.isPGroup'.comap_subtype
  have hNb : N=⊥ := bot_unique (hcore ▸ (show N≤pCore 2 H from le_sSup ⟨inferInstance,hN⟩))
  have hUb : (U:Subgroup SL(2,F))=⊥ := by
    have hh := congrArg (fun J : Subgroup H => J.map H.subtype) hNb
    simpa only [N,map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] using hh
  have hc : Nat.card U=4 := (Nat.card_congr (sylowEquivAdditive F 2 U).toEquiv).symm.trans hF
  rw [show Nat.card U=Nat.card (U:Subgroup SL(2,F)) from rfl,hUb,card_bot] at hc
  contradiction

end Matrix.SpecialLinearGroup
