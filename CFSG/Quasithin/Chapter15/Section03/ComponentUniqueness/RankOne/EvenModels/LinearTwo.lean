module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BorelFields
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner

/-!
# The upstairs PSL₂(4) Borel centralizer

The normal four-group forces field order four and fills the component Sylow
subgroup. An automorphism fixing the actor therefore fixes that Sylow subgroup
pointwise, so the binary PSL₂ automorphism calculation makes it conjugation
by an element of the four-group. The self-centralizing plane identifies the
actor with A₄. Its trivial centre kills the conjugating element.

This proves the literal upstairs centralizer equality without using either
the contrary centralizer inequality or the exclusion of A₄. Together with
the linear-three and unitary calculations it completes the Borel argument
in Aschbacher--Smith, proof of 15.3.43, printed p.1140.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The linear Borel gives the actual centralizer equality in the ambient
group; its proof does not use either retained contradiction. -/
theorem linear_borel_centralizers
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ}
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) (hB : M ⊓ L = borel L S) :
    S ⊓ centralizer (Yplus : Set G) = S ⊓ centralizer (L : Set G) := by
  have hn := linear_borel_degree_eq_two c hm hB
  have hm4 : ClassicalGroup.IsPSL L 2 4 := by
    simpa only [hn, show (2 : ℕ) ^ 2 = 4 from rfl] using hm
  obtain ⟨P, hP⟩ := component_sylow c
  obtain ⟨eY⟩ := actor_alternating_four_of_plane_centralizer c
    (RankTwo.RankOnePlane.linear_four_plane_selfCentralizing hm4 P hP
      c.plane_two_le (plane_le_component c) c.plane_two_card)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm4
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using
      (show Nat.card F = 2 ^ 2 from hF))
  let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hPi : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hVP : V₂.subgroupOf L ≤ (P : Subgroup L) := by
    rw [← hPi]
    exact subgroupOf_mono L (le_inf c.plane_two_le (plane_le_component c))
  have hcardV : Nat.card (V₂.subgroupOf L) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (plane_le_component c)).toEquiv).trans
      c.plane_two_card
  have hcardP : Nat.card P = 4 :=
    (RankTwo.RankOnePlane.linear_sylow_card f P).trans hF
  have hPV : (P : Subgroup L) = V₂.subgroupOf L :=
    (eq_of_le_of_card_ge hVP (by rw [hcardV]; exact hcardP.le)).symm
  have hPY (x : L) (hx : x ∈ P) : (x : G) ∈ Yplus :=
    plane_le_actor c (show x ∈ V₂.subgroupOf L from hPV ▸ hx)
  apply le_antisymm
  · rintro s ⟨hs, hsy⟩
    let si : normalizer (L : Set G) :=
      ⟨s, c.normalizes ((sylow_le_local c hs).2)⟩
    let a := L.normalizerMonoidHom si
    have hfix (x : L) (hx : (x : G) ∈ Yplus) : a x = x := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hsy x hx).symm
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    obtain ⟨x, hx, ha⟩ := Theory.PSL2.aut_fixing_sylow_inner Q (MulAut.congr e a) (by
      rintro _ ⟨x, hx, rfl⟩
      change e (a (e.symm (e x))) = e x
      rw [e.symm_apply_apply, hfix x (hPY x hx)])
    obtain ⟨p, hp, rfl⟩ := hx
    have ha' : a = MulAut.conj p := by
      apply (MulAut.congr e).injective
      rw [MulAut.congr_conj]
      exact ha
    let pY : Yplus := ⟨p, hPY p hp⟩
    have hpZ : eY pY ∈ center (alternatingGroup (Fin 4)) := by
      apply mem_center_iff.mpr
      intro q
      obtain ⟨y, rfl⟩ := eY.surjective q
      change eY y * eY pY = eY pY * eY y
      rw [← map_mul, ← map_mul]
      apply congrArg eY
      apply Subtype.ext
      have h := congrArg Subtype.val (hfix ⟨y, c.y_le_component y.property⟩ y.property)
      rw [ha'] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [alternatingGroup.center_eq_bot (by simp)] at hpZ
    have hpY : pY = 1 := eY.injective ((mem_bot.mp hpZ).trans eY.map_one.symm)
    have hp1 : p = 1 := Subtype.ext (congrArg (fun y : Yplus => (y : G)) hpY)
    have ha1 : a = 1 := by rw [ha', hp1, map_one]
    have hc : si ∈ L.normalizerMonoidHom.ker := ha1
    rw [normalizerMonoidHom_ker] at hc
    exact ⟨hs, hc⟩
  · exact inf_le_inf_left S (centralizer_le c.y_le_component)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
