module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.SourceStructure.Centralizer
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
/-!
# The two source cores induce the full action on E

Both extraspecial cores normalize E because it contains their centers. Each
core has an action image of order two, with kernel the corresponding literal
intersection of order sixteen. The images differ: the first fixes z and the
second fixes u, and fixing both generators of E forces the identity. The join
therefore induces all six automorphisms of the four-group.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(1,5), 46.2–46.3,
printed pp.29–30 and 251. All actions below are restrictions of the literal
normalizer conjugation map.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

theorem E_kleinFour : IsKleinFour P.E := by
  let : IsElementaryAbelian 2 P.E := P.E_elementary
  let : Nontrivial P.E := Finite.one_lt_card_iff_nontrivial.mp (by rw [P.E_card]; decide)
  exact ⟨P.E_card, IsElementaryAbelian.exponent_eq_prime⟩

omit [Finite G] in
private theorem extraspecial_normalizes {Q E : Subgroup G} [IsExtraspecial 2 Q]
    (hE : E ≤ Q) (hZ : (center Q).map Q.subtype ≤ E) :
    Q ≤ normalizer (E : Set G) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro q hq r hr
  have hc : ⁅(⟨q, hq⟩ : Q), (⟨r, hE hr⟩ : Q)⁆ ∈ center Q :=
    (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _))
  exact hZ (mem_map_of_mem Q.subtype hc)

theorem core_le_normalizer_E : ambientCore D.z ≤ normalizer (P.E : Set G) := by
  let := D.localType.ambientCore_isExtraspecial
  apply extraspecial_normalizes P.E_le_core
  rw [D.localType.core_center_image]
  exact le_sup_left

theorem conjugateCore_extraspecial : IsExtraspecial 2 P.conjugateCore :=
  IsExtraspecial.of_mulEquiv
    ((ambientCore D.z).equivMapOfInjective (MulAut.conj P.g).toMonoidHom
      (MulAut.conj P.g).injective) D.localType.ambientCore_isExtraspecial

theorem conjugateCore_center_image :
    (center P.conjugateCore).map P.conjugateCore.subtype = zpowers P.u := by
  let := conjugateCore_extraspecial P
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · apply zpowers_le.mpr
    refine mem_map.mpr ⟨⟨P.u, P.u_mem_conjugateCore⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le x.property))
  · rw [card_map_of_injective P.conjugateCore.subtype_injective,
      IsExtraspecial.center_order_p (p := 2), Nat.card_zpowers, P.u_order]

theorem conjugateCore_le_normalizer_E (L : LocalCensus D) :
    P.conjugateCore ≤ normalizer (P.E : Set G) := by
  let := conjugateCore_extraspecial P
  apply extraspecial_normalizes (P.E_le_conjugateCore L)
  rw [conjugateCore_center_image P]
  exact le_sup_right

def coreJoin : Subgroup G := ambientCore D.z ⊔ P.conjugateCore

theorem coreJoin_le_normalizer_E (L : LocalCensus D) :
    coreJoin P ≤ normalizer (P.E : Set G) :=
  sup_le (core_le_normalizer_E P) (conjugateCore_le_normalizer_E P L)

def coreJoinAction (L : LocalCensus D) : coreJoin P →* MulAut P.E :=
  P.E.normalizerMonoidHom.comp (inclusion (coreJoin_le_normalizer_E P L))

private def restrictedAction (E K : Subgroup G) (h : K ≤ normalizer (E : Set G)) :
    K →* MulAut E := E.normalizerMonoidHom.comp (inclusion h)

omit [Finite G] in
private theorem restrictedAction_ker (E K : Subgroup G) (h : K ≤ normalizer (E : Set G)) :
    (restrictedAction E K h).ker = (centralizer (E : Set G)).subgroupOf K := by
  rw [restrictedAction, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

theorem core_inf_centralizer_E : ambientCore D.z ⊓ centralizer (P.E : Set G) = P.leftCore := by
  rw [centralizer_E_eq, ← inf_assoc, inf_eq_left.mpr (ambientCore_le D.z)]
  rfl

theorem conjugateCore_inf_centralizer_E :
    P.conjugateCore ⊓ centralizer (P.E : Set G) = P.rightCore := by
  rw [centralizer_E_eq, inf_comm (involutionCentralizer D.z), ← inf_assoc,
    inf_eq_left.mpr P.conjugateCore_le]
  rfl

private theorem restrictedAction_range_card (K : Subgroup G)
    (hK : K ≤ normalizer (P.E : Set G))
    (hk : Nat.card K = 32) (hc : Nat.card (K ⊓ centralizer (P.E : Set G) : Subgroup G) = 16) :
    Nat.card (restrictedAction P.E K hK).range = 2 := by
  have hker : Nat.card (restrictedAction P.E K hK).ker = 16 := by
    rw [restrictedAction_ker]
    rw [← inf_subgroupOf_right (centralizer (P.E : Set G)) K]
    rw [Nat.card_congr (subgroupOfEquivOfLe (show centralizer (P.E : Set G) ⊓ K ≤ K from inf_le_right)).toEquiv]
    rwa [inf_comm]
  have hh := (restrictedAction P.E K hK).ker.card_mul_index
  rw [hker, index_ker, hk] at hh
  omega

private theorem E_aut_ext (a b : MulAut P.E)
    (hz : a ⟨D.z, P.z_mem_E⟩ = b ⟨D.z, P.z_mem_E⟩)
    (hu : a ⟨P.u, P.u_mem_E⟩ = b ⟨P.u, P.u_mem_E⟩) : a = b := by
  let K := a.toMonoidHom.eqLocus b.toMonoidHom
  have h : P.E ≤ K.map P.E.subtype :=
    sup_le (zpowers_le.mpr ⟨⟨D.z, P.z_mem_E⟩, hz, rfl⟩)
      (zpowers_le.mpr ⟨⟨P.u, P.u_mem_E⟩, hu, rfl⟩)
  apply MulEquiv.ext
  intro x
  obtain ⟨y, hy, he⟩ := h x.property
  have hyx : y = x := Subtype.ext he
  subst y
  exact hy

theorem coreJoinAction_surjective (L : LocalCensus D) :
    Function.Surjective (coreJoinAction P L) := by
  let : IsKleinFour P.E := E_kleinFour P
  let f := coreJoinAction P L
  let a := restrictedAction P.E (ambientCore D.z) (core_le_normalizer_E P)
  let b := restrictedAction P.E P.conjugateCore (conjugateCore_le_normalizer_E P L)
  have ha : Nat.card a.range = 2 := restrictedAction_range_card P _ _
    D.localType.ambientCore_card (by rw [core_inf_centralizer_E, P.leftCore_card])
  have hqb : Nat.card P.conjugateCore = 32 := by
    rw [ReturningPair.conjugateCore, card_map_of_injective (MulAut.conj P.g).injective]
    exact D.localType.ambientCore_card
  have hb : Nat.card b.range = 2 := restrictedAction_range_card P _ _ hqb
    (by rw [conjugateCore_inf_centralizer_E, P.rightCore_card L])
  have ha_le : a.range ≤ f.range := by
    rintro x ⟨q, rfl⟩
    exact ⟨⟨q, (le_sup_left : ambientCore D.z ≤ coreJoin P) q.property⟩, rfl⟩
  have hb_le : b.range ≤ f.range := by
    rintro x ⟨q, rfl⟩
    exact ⟨⟨q, (le_sup_right : P.conjugateCore ≤ coreJoin P) q.property⟩, rfl⟩
  have hne : a.range ≠ b.range := by
    intro he
    have hbot : a.range = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      apply mem_bot.mpr
      apply E_aut_ext P x 1
      · obtain ⟨q, rfl⟩ := hx
        apply Subtype.ext
        change (q : G) * D.z * (q : G)⁻¹ = D.z
        exact mul_inv_eq_iff_eq_mul.mpr
          (mem_centralizer_singleton_iff.mp (ambientCore_le D.z q.property))
      · obtain ⟨q, hq⟩ := he ▸ hx
        rw [← hq]
        apply Subtype.ext
        change (q : G) * P.u * (q : G)⁻¹ = P.u
        exact mul_inv_eq_iff_eq_mul.mpr
          (mem_centralizer_singleton_iff.mp (P.conjugateCore_le q.property))
    rw [hbot, card_bot] at ha
    omega
  have hd : Nat.card f.range ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using card_subgroup_dvd_card f.range
  have hd2 : 2 ∣ Nat.card f.range := ha ▸ card_dvd_of_le ha_le
  have hc : Nat.card f.range = 2 ∨ Nat.card f.range = 6 := by
    have hu := Nat.le_of_dvd (by decide : 0 < 6) hd
    interval_cases hn : Nat.card f.range <;>
      (try norm_num [hn] at hd) <;> (try norm_num [hn] at hd2) <;> simp_all
  have hc6 : Nat.card f.range = 6 := hc.resolve_left (fun h => hne
    ((eq_of_le_of_card_ge ha_le (by omega)).trans
      (eq_of_le_of_card_ge hb_le (by omega)).symm))
  apply MonoidHom.range_eq_top.mp
  exact eq_top_of_card_eq f.range (hc6.trans (IsKleinFour.card_mulAut P.E).symm)
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
