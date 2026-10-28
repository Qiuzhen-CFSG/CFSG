module

public import Stellmacher.Recognition.LargeTerminalInvertingSylowData
public import Theory.SpecificGroups.ReeTwo.RootTwistedSylow
public import Stellmacher.Recognition.LargeTerminalReeCoreModelOrientation
public import Stellmacher.Recognition.LargeTerminalFirstCoreSecondCenter
public import Theory.SpecificGroups.ReeTwo.CoreFiveActionNormalization
public import Theory.SpecificGroups.ReeTwo.InvertingExtensionFirstCore

/-!
# Excluding inversion in the actual marked Sylow extension

A squaring inverter lies in a Sylow subgroup of the second parabolic, which
it generates together with the actual two-core. Its fourth power is one or
the marked central involution. Normalize the faithful five-action on that
core while preserving the fixed root and its square. The family-wide Ree
extension theorem then forces every automorphism of the centralizer of the
second center to fix the mark, for both action orbits and both fourth powers.

Marked Sylow conjugacy returns to the original Sylow. Its intrinsic first-core
identity contradicts the neighboring-parabolic automorphism moving the mark.
Thus inversion is impossible without assuming that the extension splits or
identifying all the extensions with one comparison group. The earlier generic
marked-transfer interface is retained.

Source: Thompson VI, pp.629–630, the terminal geometry in
`LargeTerminalFirstCoreSecondCenter` and `LargeTerminalReeCoreModelOrientation`,
and the coordinate certificates in `ReeTwo.InvertingExtensionFirstCore`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

/-- A marked model of any Sylow subgroup of the second parabolic gives the
same marked model of the original Sylow. -/
public theorem LargeTerminalContext.marked_sylow_equiv_of_local_equiv
    {G K : Type*} [Group G] [Finite G] [Group K] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (T : Sylow 2 ctx.second)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (zT : T) (hzT : ((zT : ctx.second) : G) = z)
    (eT : T ≃* K) (k : K) (heT : eT zT = k) :
    ∃ hzS : z ∈ S, ∃ eS : S ≃* K, eS ⟨z, hzS⟩ = k := by
  have hzTP : ∃ hzP : z ∈ ctx.second, (⟨z, hzP⟩ : ctx.second) ∈ T := by
    refine ⟨hzT ▸ (zT : ctx.second).property, ?_⟩
    have he : (⟨z, hzT ▸ (zT : ctx.second).property⟩ : ctx.second) = zT :=
      Subtype.ext hzT.symm
    rw [he]
    exact zT.property
  obtain ⟨hzS, e, he⟩ := ctx.marked_equiv_local_sylow T z hz hgen hzTP
  refine ⟨hzS, e.trans eT, ?_⟩
  have hez : e ⟨z, hzS⟩ = zT := Subtype.ext (Subtype.ext (he.trans hzT.symm))
  exact (congrArg eT hez).trans heT


private theorem normalized_five_action
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t z : twoCoreIn ctx.second)
    (hgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (het : eQ t = ReeTwo.Core.root 2) (hez : eQ z = ReeTwo.Core.root 9) :
    ∃ (e : twoCoreIn ctx.second ≃* ReeTwo.Core) (a : A),
      e t = ReeTwo.Core.root 2 ∧ e z = ReeTwo.Core.root 9 ∧
      ctx.reeCoreAction e (inclusion hAP a) = ReeTwo.Core.c := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  let f := ctx.reeCoreAction eQ
  let rho := f (inclusion hAP a)
  have hrho : orderOf rho = 5 := by
    apply orderOf_eq_prime
    · change f (inclusion hAP a) ^ 5 = 1
      rw [← map_pow, ← map_pow]
      have hp : a ^ 5 = 1 := hA ▸ pow_card_eq_one' (x := a)
      rw [hp, map_one, map_one]
    · intro he
      have htriv : ∀ b : A, f (inclusion hAP b) = 1 := by
        intro b
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (ha b)
        rw [← hn, map_zpow, map_zpow]
        change rho ^ n = 1
        rw [he, one_zpow]
      have htop : (centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second) = ⊤ := by
        apply eq_top_iff.mpr
        intro q _
        apply mem_centralizer_iff.mpr
        intro b hb
        have hh := ctx.reeCoreAction_apply eQ (inclusion hAP ⟨b, hb⟩) q
        rw [htriv] at hh
        simp only [MulAut.one_apply, eQ.symm_apply_apply] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh.symm
      rw [htop, card_top, Nat.card_congr eQ.toEquiv, ReeTwo.Core.card] at hcard
      norm_num at hcard
  have htfix : rho (ReeTwo.Core.root 2) = ReeTwo.Core.root 2 := by
    rw [← het]
    apply eQ.symm.injective
    apply Subtype.ext
    rw [ctx.reeCoreAction_apply, eQ.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp (hgen.le (mem_zpowers (t : G))).2 a a.property)
  obtain ⟨d, hdt, hdz, hd⟩ := ReeTwo.Core.exists_marked_conjugator_of_orderOf_eq_five rho hrho htfix
  refine ⟨eQ.trans d, a, ?_, ?_, ?_⟩
  · exact (congrArg d het).trans hdt
  · exact (congrArg d hez).trans hdz
  · change d * rho * d⁻¹ = ReeTwo.Core.c
    exact hd

/-- No element of the actual second parabolic inverts the marked fixed root.
The proof covers both inverting action orbits and nonsplit order-eight lifts,
and uses the original Sylow and its actual neighboring core throughout. -/
public theorem LargeTerminalContext.ree_no_local_inversion_of_marked_core
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t z : twoCoreIn ctx.second) (ht4 : orderOf (t : G) = 4)
    (htsq : t ^ 2 = z) (hz2 : orderOf (z : G) = 2)
    (hzgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G))
    (htgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (het : eQ t = ReeTwo.Core.root 2) (hez : eQ z = ReeTwo.Core.root 9)
    (b : G) (hbP : b ∈ ctx.second) : b * (t : G) * b⁻¹ ≠ (t : G)⁻¹ := by
  intro hinv
  obtain ⟨e, a, het, hez, ha⟩ := normalized_five_action ctx A hA hAP hcard t z htgen eQ het hez
  obtain ⟨s, hsP, T, hsT, hsA, _hsR, _hsQ, hfour, _h8, _hord, hsa, hst, hQT⟩ :=
    ctx.exists_local_sylow_inverting_lift hS A hA hAP hcard t b t.property ht4 htgen hbP hinv
  let f := ctx.reeCoreAction e
  let sP : ctx.second := ⟨s, hsP⟩
  let beta := f sP
  have hconj : ∀ q, (e.symm (beta q) : G) = s * (e.symm q : G) * s⁻¹ := by
    intro q
    simpa only [e.apply_symm_apply] using ctx.reeCoreAction_apply e sP (e.symm q)
  have hbc : beta * ReeTwo.Core.c * beta⁻¹ = ReeTwo.Core.c ^ 2 := by
    rw [← ha]
    change f sP * f (inclusion hAP a) * (f sP)⁻¹ = f (inclusion hAP a) ^ 2
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    apply congrArg f
    exact Subtype.ext (hsa a a.property)
  have hbinv : beta (ReeTwo.Core.root 2) = (ReeTwo.Core.root 2)⁻¹ := by
    rw [← het, ← map_inv]
    apply e.symm.injective
    apply Subtype.ext
    rw [ctx.reeCoreAction_apply, e.symm_apply_apply]
    exact hst
  have hs4 : s ^ 4 = 1 ∨ s ^ 4 = (z : G) := by
    simpa only [← htsq, coe_pow] using hfour
  have hb4 : beta ^ 4 = 1 := by
    change (f sP) ^ 4 = 1
    rw [← map_pow]
    rcases hs4 with hh | hh
    · rw [show sP ^ 4 = 1 from Subtype.ext hh, map_one]
    · apply MulEquiv.ext
      intro q
      apply e.symm.injective
      apply Subtype.ext
      have hhq := ctx.reeCoreAction_apply e (sP ^ 4) (e.symm q)
      simp only [e.apply_symm_apply] at hhq
      rw [hhq]
      change s ^ 4 * (e.symm q : G) * (s ^ 4)⁻¹ = (e.symm q : G)
      rw [hh]
      have hzc : z ∈ center (twoCoreIn ctx.second) := by
        apply mem_center_iff.mpr
        intro x
        apply e.injective
        simpa only [map_mul, hez] using
          mem_center_iff.mp ReeTwo.Core.root_nine_mem_center (e x)
      exact mul_inv_eq_iff_eq_mul.mpr
        (congrArg Subtype.val (mem_center_iff.mp hzc (e.symm q))).symm
  let i : T →* G := ctx.second.subtype.comp T.toSubgroup.subtype
  have hi : Function.Injective i := ctx.second.subtype_injective.comp T.toSubgroup.subtype_injective
  let j : ReeTwo.Core →* T :=
    { toFun := fun q => ⟨⟨(e.symm q : G), twoCoreIn_le ctx.second (e.symm q).property⟩, hQT (e.symm q)⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : twoCoreIn ctx.second => (q : G)) e.symm.map_one
      map_mul' := fun x y => by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : twoCoreIn ctx.second => (q : G)) (e.symm.map_mul x y) }
  let sT : T := ⟨sP, hsT⟩
  have hj : ∀ q, i (j q) = (e.symm q : G) := fun _ => rfl
  have hjz : i (j (ReeTwo.Core.root 9)) = (z : G) := by
    rw [hj, ← hez, e.symm_apply_apply]
  have hgen : j.range ⊔ zpowers sT = ⊤ := by
    apply Subgroup.map_injective hi
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    have hrange : j.range.map i = twoCoreIn ctx.second := by
      rw [← MonoidHom.range_comp]
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact (e.symm q).property
      · intro hx
        refine ⟨e ⟨x, hx⟩, ?_⟩
        exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    rw [hrange]
    have hs4Q : s ^ 4 ∈ twoCoreIn ctx.second := by
      rcases hs4 with hh | hh
      · rw [hh]; exact one_mem _
      · rw [hh]; exact z.property
    have hG := ctx.local_sylow_generated_by_squaring_lift hS A hA hAP s hsP hsA hsa hs4Q T hsT
    change twoCoreIn ctx.second ⊔ zpowers s = (⊤ : Subgroup T).map i
    rw [hG, ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype]
  have hcardT : Nat.card T = 4096 := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    exact (Nat.card_congr ((T.equiv (S.subtype hSP)).trans
      (subgroupOfEquivOfLe hSP)).toEquiv).trans hS
  have hjconj : ∀ q, sT * j q * sT⁻¹ = j (beta q) := by
    intro q
    apply hi
    exact (hconj q).symm
  have hjfour : sT ^ 4 = 1 ∨ sT ^ 4 = j (ReeTwo.Core.root 9) := by
    rcases hs4 with hh | hh
    · exact Or.inl (hi (by rw [map_pow, map_one]; exact hh))
    · exact Or.inr (hi (by rw [map_pow, hjz]; exact hh))
  obtain ⟨hzK, hfixed⟩ := ReeTwo.InvertingExtension.root_nine_firstCore_obstruction
    hcardT j sT beta hgen hb4 hbc hbinv hjconj hjfour
  obtain ⟨hzS, eS, heS⟩ := ctx.marked_equiv_local_sylow T z hz2 hzgen
    ⟨twoCoreIn_le ctx.second z.property, hQT z⟩
  have hfirst := ctx.first_core_eq_second_center_centralizer hS eQ
  have hcoreS : twoCoreIn ctx.first ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.first :=
      ctx.terminal.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
    rintro x ⟨p, hp, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.first)).le_sylow_of_normal (S.subtype hSP) hp
  let eK : twoCoreIn ctx.first ≃* ReeTwo.InvertingExtension.firstCore T :=
    (subgroupOfEquivOfLe hcoreS).symm.trans
      ((MulEquiv.subgroupCongr hfirst).trans (centralizerUpperCentralSeriesEquiv eS 2))
  let zK : ReeTwo.InvertingExtension.firstCore T := ⟨j (ReeTwo.Core.root 9), hzK⟩
  apply ctx.first_core_not_equiv_fixed_involution
    ⟨z, ctx.central_involution_mem_first_core z hzgen⟩ hz2 hzgen zK hfixed
  refine ⟨eK, ?_⟩
  apply Subtype.ext
  apply hi
  exact heS.trans hjz.symm


end Stellmacher.Recognition
