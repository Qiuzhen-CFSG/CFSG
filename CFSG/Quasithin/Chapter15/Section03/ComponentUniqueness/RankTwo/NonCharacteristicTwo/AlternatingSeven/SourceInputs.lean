module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.PartitionObstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Solvability
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PCoreImage

/-!
# Source inputs in the actual alternating-seven model

The normalizer identity makes every characteristic subgroup of Y₊ normal
in the original M ∩ I. Its characteristic-two hypothesis therefore kills
O₃(Y₊). Cubic exponent modulo O₂ makes Y₊ solvable. Intersecting the supplied
Sylow two-subgroup with L uses only normality of L inside I and gives the
compatible Sylow subgroup in any actual seven-point model of L.

The nonsplit triple-cover alternative has center of order three, incompatible
with either the supplied two-core identity for the center or the trivial odd
core. No conclusion about partition placement is assumed here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3d),
printed pp.501--502, and 15.3.11, 15.3.36, 15.3.41--42, pp.1124,1135,1138.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
variable {G : Type*} [Group G] [Finite G]
variable {I L M Yplus S : Subgroup G} [(L.subgroupOf I).Normal]

omit [Finite G] in
theorem yplus_le_intersection (h : ComponentSetup I L M Yplus S) : Yplus ≤ M ⊓ I :=
  h.theta_eq ▸ theta_le (M ⊓ I)

omit [Finite G] in
theorem intersection_normalizes (h : ComponentSetup I L M Yplus S) :
    M ⊓ I ≤ normalizer (Yplus : Set G) := by
  rw [← h.normalizer_eq]
  exact inf_le_right

omit [Finite G] in
theorem sylow_normalizes (h : ComponentSetup I L M Yplus S) :
    S ≤ normalizer (Yplus : Set G) :=
  (le_inf h.sylow_le_M (h.join_eq ▸ le_sup_right)).trans (intersection_normalizes h)

theorem yplus_solvable (h : ComponentSetup I L M Yplus S) : Group.IsSolvable Yplus := by
  have hp : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus) :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨1, by simpa using h.yplus_exponent x⟩)
  let := hp.isNilpotent
  let : Group.IsNilpotent (pCore 2 Yplus) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 Yplus)).mpr
    ⟨inferInstance, inferInstance⟩

theorem yplus_join_solvable (h : ComponentSetup I L M Yplus S) :
    Group.IsSolvable (Yplus ⊔ S : Subgroup G) := by
  obtain ⟨P, hP⟩ := h.sylow
  apply solvable_yplus_join_of_threeGroup_quotient (hP ▸ P.isPGroup'.map I.subtype)
    (sylow_normalizes h)
  exact isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨1, by simpa using h.yplus_exponent x⟩)

theorem yplus_isPPerfect (h : ComponentSetup I L M Yplus S) : IsPPerfect 2 Yplus := by
  have he : Stellmacher.twoResidualAmbient Yplus = (pResidual 2 Yplus).map Yplus.subtype := by
    unfold Stellmacher.twoResidualAmbient Stellmacher.twoResidualSubgroup pResidual
    congr 1
    apply congrArg sInf
    ext N
    constructor
    · rintro ⟨hN, n, hn⟩
      exact ⟨hN, IsPGroup.of_card hn⟩
    · rintro ⟨hN, hp⟩
      exact ⟨hN, IsPGroup.iff_card.mp hp⟩
  apply (pResidual_eq_top_iff 2 Yplus).mp
  apply Subgroup.map_injective Yplus.subtype_injective
  rw [← he, h.yplus_twoResidual, ← MonoidHom.range_eq_map, range_subtype]

theorem yplus_threeCore_eq_bot (h : ComponentSetup I L M Yplus S) :
    pCore 3 Yplus = ⊥ := by
  let C := Yplus.pCoreIn 3
  have hC : C ≤ M ⊓ I := (pCoreIn_le 3 Yplus).trans (yplus_le_intersection h)
  have hn : M ⊓ I ≤ normalizer (C : Set G) :=
    (intersection_normalizes h).trans
      (normalizer_le_normalizer_characteristic_image Yplus (pCore 3 Yplus))
  let : (C.subgroupOf (M ⊓ I)).Normal := normal_subgroupOf_of_le_normalizer hn
  have hz : C.subgroupOf (M ⊓ I) = ⊥ :=
    normal_pGroup_eq_bot_of_generalizedFitting_eq_pCore (by decide : 2 ≠ 3)
      h.intersection_fitting _ (isPGroup_pCoreIn 3 Yplus).comap_subtype
  have hc : C = ⊥ := by
    rw [← map_subgroupOf_eq_of_le hC, hz, Subgroup.map_bot]
  exact ((pCore 3 Yplus).map_eq_bot_iff_of_injective Yplus.subtype_injective).mp hc

omit [(L.subgroupOf I).Normal] in
theorem no_three_center_of_center_eq (hcenter : center L = pCore 2 L)
    (e : center L ≃* Multiplicative (ZMod 3)) : False := by
  have hc : Nat.card (center L) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 3
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [← hcenter, hc] at hn
  have hd : 3 ∣ 2 ^ n := hn ▸ dvd_rfl
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

omit [Finite G] [(L.subgroupOf I).Normal] in
theorem no_three_center_of_oddCore (hodd : pPrimeCore 2 L = ⊥)
    (e : center L ≃* Multiplicative (ZMod 3)) : False := by
  have hc : Nat.card (center L) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 3
  have hle : center L ≤ pPrimeCore 2 L := le_sSup ⟨inferInstance, by rw [hc]; decide⟩
  have hz := (center L).card_eq_one.mpr (le_bot_iff.mp (hodd ▸ hle))
  omega

theorem alternatingAction_has_simple_model (h : ComponentSetup I L M Yplus S)
    (α : MulAut L) (σ : Equiv.Perm (Fin 7))
    (ha : Candidates.ComponentStructure.AlternatingAction α 7 σ) :
    Nonempty (L ≃* alternatingGroup (Fin 7)) := by
  rcases ha with ⟨e, _⟩ | ⟨_, ⟨e⟩, _⟩
  · exact ⟨e⟩
  · exact (no_three_center_of_center_eq h.center_eq e).elim

/-- The concrete subgroup in the supplied seven-point model. -/
abbrev modelY (e : L ≃* alternatingGroup (Fin 7)) : Subgroup (alternatingGroup (Fin 7)) :=
  (Yplus.subgroupOf L).map e.toMonoidHom

/-- This equivalence uses the inclusion Y₊ ≤ L, not a centralizer quotient. -/
noncomputable def modelYEquiv (h : ComponentSetup I L M Yplus S)
    (e : L ≃* alternatingGroup (Fin 7)) : Yplus ≃* modelY (Yplus := Yplus) e :=
  (subgroupOfEquivOfLe h.yplus_le).symm.trans
    ((Yplus.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)

/-- Intersect the given Sylow subgroup with the relatively normal component. -/
theorem component_sylow (h : ComponentSetup I L M Yplus S) :
    ∃ P : Sylow 2 L, (P : Subgroup L) ≤ S.subgroupOf L := by
  obtain ⟨T, hT⟩ := h.sylow
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal (L.subgroupOf I)
  let e := subgroupOfEquivOfLe h.component_le
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  change (a : G) ∈ S
  rw [← hT]
  rw [hP] at ha
  exact ⟨a, ha, rfl⟩

omit [Finite G] in
/-- The original Sylow normalization passes to Y₊ inside L. -/
theorem component_sylow_normalizes (h : ComponentSetup I L M Yplus S)
    (P : Sylow 2 L) (hP : (P : Subgroup L) ≤ S.subgroupOf L) :
    (P : Subgroup L) ≤ normalizer (Yplus.subgroupOf L : Set L) := by
  apply le_normalizer_iff.mpr
  intro x hx y hy
  exact ((sylow_normalizes h) (hP hx) y).mp hy

/-- Solvability, Sylow invariance, two-perfectness and rank are all derived
from the source inputs, in the same actual A₇ model. -/
theorem model_input (h : ComponentSetup I L M Yplus S)
    (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ P : Sylow 2 (alternatingGroup (Fin 7)),
      (P : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (modelY (Yplus := Yplus) e : Set _) ∧
      IsPPerfect 2 (modelY (Yplus := Yplus) e) ∧
      primeRank 3 (modelY (Yplus := Yplus) e) = 2 ∧
      Group.IsSolvable (modelY (Yplus := Yplus) e ⊔ (P : Subgroup (alternatingGroup (Fin 7))) : Subgroup _) := by
  obtain ⟨T, hT⟩ := component_sylow h
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q := modelY (Yplus := Yplus) e
  let f := modelYEquiv h e
  have hn : (P : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (Q : Set (alternatingGroup (Fin 7))) := by
    rw [← map_equiv_normalizer_eq (Yplus.subgroupOf L) e]
    exact map_mono (component_sylow_normalizes h T hT)
  refine ⟨P, hn, (yplus_isPPerfect h).of_surjective f.toMonoidHom f.surjective,
    (primeRank_equiv 3 f).symm.trans h.yplus_three_rank, ?_⟩
  let : Group.IsSolvable Yplus := yplus_solvable h
  let : Group.IsSolvable Q := Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let J := Q ⊔ (P : Subgroup (alternatingGroup (Fin 7)))
  let N := Q.subgroupOf J
  let D := (P : Subgroup (alternatingGroup (Fin 7))).subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le Q.le_normalizer hn)
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show Q ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show Q ≤ J from le_sup_left)).injective
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show (P : Subgroup (alternatingGroup (Fin 7))) ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show (P : Subgroup (alternatingGroup (Fin 7))) ≤ J from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top N D
    (codisjoint_subgroupOf_sup Q (P : Subgroup (alternatingGroup (Fin 7)))).eq_top

/-- The obstruction remains in the original intersection M ∩ I. Transport
uses Y₊ itself, so no normal odd subgroup is lifted across a two-kernel. -/
theorem model_threeCore_eq_bot (h : ComponentSetup I L M Yplus S)
    (e : L ≃* alternatingGroup (Fin 7)) : pCore 3 (modelY (Yplus := Yplus) e) = ⊥ := by
  rw [← pCore_map_iso 3 (modelYEquiv h e), yplus_threeCore_eq_bot h, Subgroup.map_bot]

/-- The center of Y₊, once its model gives order three, is an actual normal
subgroup of M ∩ I. This never identifies M ∩ I with a quotient image. -/
theorem impossible_of_yplus_center_card (h : ComponentSetup I L M Yplus S)
    (hcard : Nat.card (center Yplus) = 3) : False := by
  let C := (center Yplus).map Yplus.subtype
  have hC : C ≤ M ⊓ I := (map_subtype_le _).trans (yplus_le_intersection h)
  have hn : M ⊓ I ≤ normalizer (C : Set G) :=
    (intersection_normalizes h).trans
      (normalizer_le_normalizer_characteristic_image Yplus (center Yplus))
  let : (C.subgroupOf (M ⊓ I)).Normal := normal_subgroupOf_of_le_normalizer hn
  apply not_characteristicTwo_of_normal_three (C.subgroupOf (M ⊓ I)) _ h.intersection_fitting
  rw [Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv,
    card_map_of_injective Yplus.subtype_injective, hcard]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
