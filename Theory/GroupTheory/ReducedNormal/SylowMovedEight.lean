module
public import Theory.GroupTheory.ReducedNormal.SylowMovedPlane
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# An eight-element orbit from a moved plane and a central fixed line

A reduced elementary four-group with a nonidentity fixed vector is central:
its conjugation image has order at most two, and reducedness kills that image.
For a Sylow-center orbit U with a normal moved plane W, Sylow averaging and
a single central fixed line therefore give U=W⟨z⟩, z∉W and |U|=8.

The source consumer applies this to the actual omega orbit in C_G(z),
not to the original five-dimensional chosen module V.
Source: Aschbacher–Smith B.2.14 and13.4.9, printed pp.78 and906.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A reduced four-group with a nonidentity ambient fixed point is central. -/
theorem IsPReduced.central_of_card_four_fixed_point
    (U : Subgroup G) (hU : IsPReduced 2 U) (hcard : Nat.card U = 4)
    (z : U) (hz : z ≠ 1) (hzc : z.val ∈ center G) : U ≤ center G := by
  let := hU.normal
  let f : G →* MulAut U := MulAut.conjNormal
  have hk : f.ker = centralizer (U : Set G) := MulAut.conjNormal_ker_eq_centralizer U
  have hb : Nat.card f.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hcard z hz f.range (by
      rintro a ⟨g,rfl⟩
      apply Subtype.ext
      change g*z.val*g⁻¹ = z.val
      rw [mem_center_iff.mp hzc g,mul_inv_cancel_right])
  let e : (G ⧸ centralizer (U : Set G)) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hp : IsPGroup 2 f.range := by
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    have hn : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
    rcases hn with hn | hn
    · exact IsPGroup.of_card (n := 0) (by simpa using hn)
    · exact IsPGroup.of_card (n := 1) (by simpa using hn)
  have hbot : pCore 2 f.range = ⊥ := by
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have ht : (⊤ : Subgroup f.range) ≤ pCore 2 f.range :=
    le_sSup ⟨inferInstance,hp.of_equiv topEquiv.symm⟩
  rw [hbot] at ht
  intro u hu
  apply mem_center_iff.mpr
  intro g
  have hf : f g = 1 := congrArg Subtype.val (ht (mem_top (⟨f g,g,rfl⟩ : f.range)))
  exact (hk.le hf u hu).symm

end Theory.GroupTheory

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The original central orbit has order eight when a normal moved plane has one central fixed line. -/
theorem IsPReduced.omegaCenter_span_eight_of_moved_plane
    (U : Subgroup G) (hU : IsPReduced 2 U) (S : Sylow 2 G)
    (hUS : U ≤ S)
    (hspan : U = conjugateSpanBy (omegaOneCenterAmbient (S : Subgroup G)) ⊤)
    (A : Subgroup G) (hcard : Nat.card (⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) = 4)
    (z : G) (hz1 : z ≠ 1) (hzS : z ∈ omegaOneCenterAmbient (S : Subgroup G))
    (hzc : z ∈ center G)
    (hfixed : omegaOneCenterAmbient (S : Subgroup G) ⊓
      centralizer (conjugateSpanBy A ⊤ : Set G) = zpowers z) :
    U = (⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) ⊔ zpowers z ∧
      z ∉ (⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) ∧ Nat.card U = 8 := by
  let := hU.normal
  let := hU.elementary
  let N := conjugateSpanBy A ⊤
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy A ⊤))
  let W := ⁅U,N⁆
  have hWU : W ≤ U := commutator_le_left U N
  have hZU : omegaOneCenterAmbient (S : Subgroup G) ≤ U :=
    hspan.symm ▸ le_conjugateSpanBy _ _
  have hzU : z ∈ U := hZU hzS
  have hzW : zpowers z ≤ U := zpowers_le.mpr hzU
  have hsplit := omegaCenter_le_moved_sup_fixed U N S hUS hZU
  rw [hfixed] at hsplit
  have hzn : (zpowers z).Normal := ⟨fun n hn g => by
    have hc : n ∈ center G := (zpowers_le.mpr hzc) hn
    rw [mem_center_iff.mp hc g,mul_inv_cancel_right]
    exact hn⟩
  let := hzn
  have hgen : U = W ⊔ zpowers z := by
    apply le_antisymm ?_ (sup_le hWU hzW)
    rw [hspan]
    exact conjugateSpanBy_le hsplit le_normalizer_of_normal
  have hne : W ≠ U := by
    intro he
    have hc : Nat.card U = 4 := he ▸ hcard
    have hcent := hU.central_of_card_four_fixed_point U hc ⟨z,hzU⟩
      (fun he => hz1 (congrArg Subtype.val he)) hzc
    have hw : W = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hcent.trans (center_le_centralizer (N : Set G)))
    change Nat.card W = 4 at hcard
    rw [hw,card_bot] at hcard
    omega
  have hznot : z ∉ W := by
    intro hz
    apply hne
    exact le_antisymm hWU (hgen.le.trans (sup_le le_rfl (zpowers_le.mpr hz)))
  have hlow : 8 ≤ Nat.card U := by
    have hidx : 2 ≤ W.relIndex U := by
      have h0 : W.relIndex U ≠ 0 := (W.subgroupOf U).index_ne_zero_of_finite
      have h1 : W.relIndex U ≠ 1 := fun hi => hne (le_antisymm hWU (relIndex_eq_one.mp hi))
      omega
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) W U bot_le hWU
    simp only [relIndex_bot_left] at hc
    change Nat.card W = 4 at hcard
    rw [hcard] at hc
    omega
  have hline : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzS).2.1 hz1
  have hupp : Nat.card U ≤ 8 := by
    have hbot : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      ext g
      simp [mem_centralizer_iff]
    have hb := card_fixed_sup_le_mul_of_centralizes W (⊥ : Subgroup G) (zpowers z)
      ((zpowers_le.mpr hzc).trans (center_le_centralizer _)) (by rw [hbot]; exact le_top)
    rw [hbot,inf_top_eq,inf_top_eq,← hgen,hline] at hb
    change Nat.card W = 4 at hcard
    rw [hcard] at hb
    exact hb
  exact ⟨hgen,hznot,le_antisymm hupp hlow⟩

end Theory.GroupTheory
