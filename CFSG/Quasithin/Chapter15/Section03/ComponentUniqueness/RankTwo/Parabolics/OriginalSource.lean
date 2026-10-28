module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.WreathRecognition

/-!
# The actual Borel action in the final rank-two contradiction

The recognized quotient parabolic contains the quotient Sylow Borel.
The centralizer kernel normalizes Y₊, so this containment lifts to the
original local subgroup. The natural orthogonal actor has order72;
consequently every element of order prime to6 acts trivially on V.
This discharges the last Borel-action premise in the characteristic-two
branch of15.3.35, including central covers of the component.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics
variable {G : Type*} [Group G] [Finite G]

namespace Selection
variable {L MI Y S : Subgroup G} [L.Normal]

theorem sylowBorel_le_local (d : Setup L MI Y S)
    (hN : normalizer (Y : Set G) = MI)
    {z : G} {α : MulAut L} (a : SourceAction L S z α) : sylowBorel L S ≤ MI := by
  let q := centralizerQuotientMap L
  obtain ⟨P,hP⟩ := d.sylow
  have hk : q.ker ≤ MI := by
    intro x hx
    change x ∈ (centralizerQuotientMap L).ker at hx
    rw [centralizerQuotientMap, QuotientGroup.ker_mk'] at hx
    rw [← hN]
    exact Subgroup.centralizer_le_normalizer _ (centralizer_le d.yplus_le hx)
  have hb : (sylowBorel L S).map q ≤
      sylowBorel (centralizerQuotientComponent L) (S.map q) := by
    rintro _ ⟨x, ⟨l,hl,rfl⟩,rfl⟩
    have ht := component_borel_preimage L S P hP
    rw [← ht] at hl
    exact hl
  have hi := hb.trans ((quotientParabolic d a).contains_borel.trans inf_le_left)
  have hh := map_le_iff_le_comap.mp hi
  rw [comap_map_eq, sup_eq_left.mpr hk] at hh
  exact hh

end Selection

variable {I L M Y S V V₁ V₂ Yplus : Subgroup G} [(L.subgroupOf I).Normal]

omit [Finite G] in
private theorem selectionSetup
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S) :
    Selection.Setup (L.subgroupOf I) (M.subgroupOf I) (Yplus.subgroupOf I)
      (S.subgroupOf I) := by
  let := c.component_quasisimple
  refine ⟨IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.component_le).symm,
    comap_mono c.yplus_le, ?_, ?_, c.quotient_local⟩
  · apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le c.component_le,
      map_subgroupOf_eq_of_le (c.join_eq ▸ le_sup_right)]
    simpa only [← MonoidHom.range_eq_map, range_subtype] using c.join_eq.symm
  · obtain ⟨P,hP⟩ := c.sylow
    refine ⟨P, ?_⟩
    apply Subgroup.map_injective I.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (c.join_eq ▸ le_sup_right)]

private theorem borel_le_original_local
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    {z : I} {α : MulAut (L.subgroupOf I)}
    (a : Selection.SourceAction (L.subgroupOf I) (S.subgroupOf I) z α)
    {B : Subgroup G} (hB : BorelOverSylow L S B) : B ≤ M ⊓ I := by
  have hYI : Yplus ≤ I := c.yplus_le.trans c.component_le
  have hN : normalizer (Yplus.subgroupOf I : Set I) = M.subgroupOf I := by
    rw [← subgroupOf_normalizer_eq hYI]
    ext x
    exact ⟨fun hx => (c.normalizer_eq.le ⟨x.property,hx⟩).1,
      fun hx => (c.normalizer_eq.ge ⟨hx,x.property⟩).2⟩
  have hb := Selection.sylowBorel_le_local (selectionSetup c) hN a
  obtain ⟨P,hP,hB⟩ := hB
  have hPS : (P : Subgroup L) = S.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hP, subgroupOf_map_subtype]
  rw [hB]
  change (normalizer ((P : Subgroup L) : Set L)).map L.subtype ≤ M ⊓ I
  rw [hPS]
  rintro _ ⟨l,hl,rfl⟩
  let l' : L.subgroupOf I := ⟨⟨l,c.component_le l.property⟩,l.property⟩
  have hl' : l' ∈ normalizer ((S.subgroupOf I).subgroupOf (L.subgroupOf I) : Set (L.subgroupOf I)) := by
    intro x
    exact hl ((subgroupOfEquivOfLe c.component_le) x)
  exact ⟨hb ⟨l',hl',rfl⟩,c.component_le l.property⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics

namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

omit [Finite G] in
/-- The actual natural actor kills every element of order prime to six. -/
theorem NaturalOrthogonalAction.sixPrimeResidual_centralizes
    (d : NaturalOrthogonalAction M V) {B : Subgroup G} (hBM : B ≤ M) :
    closure {x : G | x ∈ B ∧ Nat.Coprime (orderOf x) 6} ≤ centralizer (V : Set G) := by
  apply (closure_le _).mpr
  rintro x ⟨hx,hcop⟩
  let xM : M := ⟨x,hBM hx⟩
  have hd : orderOf (d.actor xM) ∣ 72 := by
    rw [← WreathRecognition.orthogonalActor_card]
    exact orderOf_dvd_natCard _
  have he : orderOf (d.actor xM) ∣ orderOf x := by
    simpa only [xM, Subgroup.orderOf_mk] using orderOf_map_dvd d.actor xM
  have hc : Nat.Coprime (orderOf x) 72 := by
    have h2 : Nat.Coprime (orderOf x) 2 := hcop.of_dvd_right (by decide)
    have h3 : Nat.Coprime (orderOf x) 3 := hcop.of_dvd_right (by decide)
    simpa using (h2.pow_right 3).mul_right (h3.pow_right 2)
  have hone : d.actor xM = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc he hd)
  have hk : xM ∈ d.actor.ker := hone
  rw [d.ker_actor] at hk
  exact hk

end CFSG.Quasithin.Chapter15.Section03

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics
variable {G : Type*} [Group G] [Finite G]
variable {I L M Y S V V₁ V₂ Yplus : Subgroup G} [(L.subgroupOf I).Normal]

/-- The characteristic-two source contradiction with its actual Borel action
proved from the quotient parabolic and the natural orthogonal actor. -/
theorem no_characteristicTwo_of_original_action
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (a : NonCharacteristicTwo.ActionSetup M Y S V V₁ V₂ Yplus)
    (natural : NaturalOrthogonalAction M V)
    {z : I} {α : MulAut (L.subgroupOf I)}
    (action : Selection.SourceAction (L.subgroupOf I) (S.subgroupOf I) z α)
    (hV : ⁅V₂,Yplus⁆ = V₂) (hSV : S ≤ normalizer (V₂ : Set G)) : False := by
  apply no_characteristicTwo_of_source I L M Y S V V₁ V₂ Yplus c a natural action hV hSV
  intro B _ hB _
  have hBMI := borel_le_original_local c action hB
  have hBV := (hBMI.trans inf_le_left).trans a.normalized
  have hBY := hBMI.trans (c.normalizer_eq.symm.le.trans inf_le_right)
  refine ⟨?_,natural.sixPrimeResidual_centralizes (hBMI.trans inf_le_left)⟩
  intro b hb
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    (mem_normalizer_iff_map_conj_eq.mp (hBV hb)),
    (mem_normalizer_iff_map_conj_eq.mp (hBY hb))]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics
