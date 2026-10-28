module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CentralOrbitQuasisimple
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.Alternating.OddCentralCovers

/-!
# Intrinsic preparation for the alternating-six MS reconstruction

The proper odd-index radical is a two-subgroup containing the ambient two-core.
The product and subnormality identify the component with the two-residual of
LR, hence give normality relative to LR. MS3 transports along the literal
subgroup equivalence, without promoting the radical to a Sylow subgroup.

Coprime commutator idempotence identifies [O₂(LR), L] with the embedded entire
blockU L. The initial central-omega action is an FF module, and its orbit has
kernel O₂(LR) on the radical. This does not assert that the full action kernel
is O₂(LR) in the triple-cover case. The Schur multiplier and trivial two-core
of L/O₂(L) leave precisely the trivial and order-three centers.

These results prepare the two separate reconstruction branches assembled in
`Source`. They do not assume or establish whole-core elementary abelianness.
Source: Aschbacher--Smith C.1.31--32, printed pp.135--136; Meierfrankenfeld--
Stellmacher (1993), (2.2), (3.2), and Main Theorem (2),(6), pp.829--830.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
namespace SmallMSPair
variable (h : SmallMSPair κ L R)
include h

omit [Finite G] in
/-- The source product on the literal subgroup carrier LR. -/
theorem relative_product : ∀ g : (L ⊔ R : Subgroup G),
    ∃ l ∈ L.subgroupOf (L ⊔ R), ∃ r ∈ R.subgroupOf (L ⊔ R), l * r = g := by
  intro g
  obtain ⟨l, hl, r, hr, he⟩ := h.product g g.property
  exact ⟨⟨l, mem_sup_left hl⟩, hl, ⟨r, mem_sup_right hr⟩, hr, Subtype.ext he⟩

omit [Finite G] in
/-- MS2(a) after restricting its original odd-index witness to LR. -/
theorem relative_radical : MSOddIndexRadical (R.subgroupOf (L ⊔ R)) := by
  obtain ⟨A, hA, ho, he⟩ := h.radical
  refine ⟨A.subgroupOf (L ⊔ R), ?_, ho, ?_⟩
  · apply lt_top_iff_ne_top.mpr
    intro ht
    exact hA.not_ge (subgroupOf_eq_top.mp ht)
  · change (A.subgroupOf (L ⊔ R)).pCoreIn 2 = R.subgroupOf (L ⊔ R)
    rw [pCoreIn_subgroupOf 2 A (L ⊔ R) hA.le, he]

/-- The relative component is two-perfect. -/
theorem relative_twoPerfect : IsPPerfect 2 (L.subgroupOf (L ⊔ R)) :=
  h.component_twoPerfect.of_surjective
    (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)).symm.surjective

/-- Subnormality and the two-group supplement identify the actual residual. -/
theorem relative_residual : pResidual 2 (L ⊔ R : Subgroup G) = L.subgroupOf (L ⊔ R) :=
  pResidual_eq_of_subnormal_product _ _ h.component.subnormal h.relative_twoPerfect
    h.relative_radical.isPGroup h.relative_product

/-- Normality is inside LR; no ambient normality in G is asserted. -/
theorem relative_normal : (L.subgroupOf (L ⊔ R)).Normal :=
  h.relative_residual ▸ inferInstance

omit [Group G] [Finite G] h in
private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy,
    e.apply_symm_apply (a (e y))⟩

omit [Finite G] in
/-- MS3 on the actual relative radical, retaining all characteristic subgroups. -/
theorem relative_characteristic : MSCharacteristicCondition (R.subgroupOf (L ⊔ R)) := by
  intro C hC hne hn
  let := hC
  let e := subgroupOfEquivOfLe (show R ≤ L ⊔ R from le_sup_right)
  let D : Subgroup R := C.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv e C
  have he : (D.map R.subtype).subgroupOf (L ⊔ R) =
      C.map (R.subgroupOf (L ⊔ R)).subtype := by
    apply map_injective (L ⊔ R).subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le D).trans le_sup_right)]
    change (C.map e.toMonoidHom).map R.subtype = _
    rw [map_map, map_map]
    rfl
  have hz : D = ⊥ := h.characteristic D inferInstance (he ▸ hn)
  exact hne ((C.map_eq_bot_iff_of_injective e.injective).mp hz)

/-- The two-core of LR is self-centralizing by the generalized Fitting theorem. -/
theorem relative_self_centralizing :
    centralizer (pCore 2 (L ⊔ R : Subgroup G) : Set (L ⊔ R : Subgroup G)) ≤
      pCore 2 (L ⊔ R : Subgroup G) := by
  rw [← h.fitting]
  exact centralizer_generalizedFitting_le _

/-- A trivial radical would make the characteristic-two ambient group trivial. -/
theorem relative_radical_ne_bot : R.subgroupOf (L ⊔ R) ≠ ⊥ := by
  intro hb
  have hq : pCore 2 (L ⊔ R : Subgroup G) = ⊥ :=
    bot_unique (hb ▸ h.relative_radical.twoCore_le)
  have ht : (⊤ : Subgroup (L ⊔ R : Subgroup G)) ≤ ⊥ := by
    have hc := h.relative_self_centralizing
    rw [hq] at hc
    intro x _
    apply hc
    intro y hy
    rw [mem_bot.mp hy]
    simp
  exact h.component.ne_bot (bot_unique (le_top.trans ht))

/-- The whole MS ambient commutator is the embedded intrinsic component core. -/
theorem ambient_commutator_eq_relative_core :
    ⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆ =
      (blockU (L.subgroupOf (L ⊔ R))).map (L.subgroupOf (L ⊔ R)).subtype := by
  apply le_antisymm
  · exact commutator_le_core_commutator_of_isSubnormal _ _ h.component.subnormal
      h.relative_twoPerfect pCore_isPGroup le_normalizer_of_normal
  · rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact commutator_mono (pCoreIn_le_of_subnormal 2 h.component.subnormal) le_rfl

/-- Identify the MS commutator with blockU on the original carrier L. -/
theorem ambient_commutator_eq_blockU :
    (⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆).map (L ⊔ R).subtype =
      (blockU L).map L.subtype := by
  rw [h.ambient_commutator_eq_relative_core, map_map]
  let e := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  have he : (blockU (L.subgroupOf (L ⊔ R))).map e.toMonoidHom = blockU L := by
    rw [blockU, blockU, map_commutator, pCore_map_iso,
      map_top_of_surjective _ e.surjective]
  rw [← he, map_map]
  rfl

/-- The core identification and MS3 exclude the zero commutator module. -/
theorem blockU_ne_bot : blockU L ≠ ⊥ := by
  intro hz
  have hcomm : ⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (L ⊔ R).subtype_injective).mp
    rw [h.ambient_commutator_eq_blockU, hz, Subgroup.map_bot]
  apply MSCentralOrbit.component_not_centralizes_omegaOrbit _ _
    h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_product
    h.relative_characteristic
  apply le_centralizer_iff.mp
  apply (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans'
  exact (MSCentralOrbit.omegaOrbit_le_centralOmega _ h.relative_radical.twoCore_le
    h.relative_self_centralizing).trans (fun x hx => (mem_omegaCenterIn_iff _ _).mp hx |>.1)

/-- The specified symplectic-derived marking as the literal central quotient of L/O₂(L). -/
def alternatingCentralQuotientEquiv
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) :=
  (centralPreimageQuotientEquiv (pCore 2 L)).symm.trans
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))

/-- When the center vanishes, the same marking identifies the full quotient with A₆. -/
def alternatingQuotientEquivOfCenterEqBot
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
    (hz : center (L ⧸ pCore 2 L) = ⊥) :
    (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) :=
  QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans (alternatingCentralQuotientEquiv e))

/-- The actual quotient center is trivial or has order three; neither case is discarded. -/
theorem alternating_center_cases
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    center (L ⧸ pCore 2 L) = ⊥ ∨ Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.core_quasisimple_of_centralCore
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun hd =>
      PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2) _ le_rfl (even_iff_two_dvd.mp hd))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (alternatingCentralQuotientEquiv e) ho with hz | ⟨_, hz⟩
  · exact Or.inl (Subgroup.card_eq_one.mp hz)
  · exact Or.inr hz

omit [Finite G] in
/-- The central-core marking supplies quasisimplicity on the relative component. -/
theorem relative_core_quasisimple
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    IsQuasisimple ((L.subgroupOf (L ⊔ R)) ⧸ pCore 2 (L.subgroupOf (L ⊔ R))) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.core_quasisimple_of_centralCore
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm

/-- The initial omega orbit detects every radical element outside O₂(LR). -/
theorem relative_orbit_edge_centralizer
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    R.subgroupOf (L ⊔ R) ⊓ centralizer
      (MSCentralOrbit.omegaOrbit (R.subgroupOf (L ⊔ R)) : Set (L ⊔ R : Subgroup G)) =
      pCore 2 (L ⊔ R : Subgroup G) := by
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  exact MSCentralOrbit.omegaOrbit_radical_centralizer _ _ h.component
    h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_radical.twoCore_le
    h.relative_self_centralizing h.relative_product h.relative_characteristic

/-- The initial central-omega FF action follows uniformly for the original odd-index radical. -/
theorem relative_centralOmega_isFFModule
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    let X := omegaCenterIn (pCore 2 (L ⊔ R : Subgroup G))
    Representation.BinaryOffender.IsFFModule
      (Representation.NormalElementaryQuotient.representation X
        (QuotientGroup.mk' (centralizer (X : Set (L ⊔ R : Subgroup G))))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) := by
  dsimp only
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  apply MSCentralOrbit.layer_isFFModule _ _ _ h.component
    h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_radical.twoCore_le
    h.relative_self_centralizing h.relative_product h.relative_characteristic
  · exact MSCentralOrbit.omegaOrbit_le_centralOmega _ h.relative_radical.twoCore_le
      h.relative_self_centralizing
  · intro x hx
    exact h.relative_radical.twoCore_le ((mem_omegaCenterIn_iff _ _).mp hx).1

end SmallMSPair
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
