module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MaximalNormalizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalResidual
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.SylowThreeCubic
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The genuine local quotients in Goldschmidt's general case

Exclude the cubic and alternating-four residual cases at both endpoints of
an actual primitive cubic tree action. A normal overlap at one endpoint
would make every nontrivial characteristic subgroup of the opposite Sylow
two-subgroup nonnormal there. The existing local pushing-up theorem then
forces one of the excluded residuals. Thus neither overlap is normal, and
the three-coset action identifies each quotient by its two-core with S₃.

A normal Sylow three-subgroup would itself be the cubic two-residual.
The existing S₃-quotient dichotomy also makes the two-core self-centralizing.
Conjugation transports these conclusions to every actual coset vertex,
providing the local hypotheses used by the central-involution interval proof.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the standing
hypotheses of Section 6, printed p.395, following (4.1)--(4.2); local
pushing-up (2.14), printed pp.384--385.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem overlap_le_local (i : Bool) : F false ⊓ F true ≤ F i := by
  cases i
  · exact inf_le_left
  · exact inf_le_right

private theorem local_pair_sup (i : Bool) : F i ⊔ F (!i) = F false ⊔ F true := by
  cases i <;> simp only [Bool.not_false, Bool.not_true, sup_comm]

private def overlapSylow (h : CubicTreeAction F) (i : Bool) : Sylow 2 (F i) :=
  (h.primitive.sylow.isPGroup.comap_subtype :
    IsPGroup 2 ((F false ⊓ F true).subgroupOf (F i))).toSylow
      (by change ¬ 2 ∣ (F false ⊓ F true).relIndex (F i)
          rw [h.overlap_relIndex i]
          decide)

private theorem local_normalized_overlap_eq_bot (h : CubicTreeAction F)
    (K : Subgroup G) (hK : K ≤ F false ⊓ F true) (i : Bool)
    (hi : F i ≤ normalizer (K : Set G))
    (hj : F (!i) ≤ normalizer (K : Set G)) : K = ⊥ := by
  have hn : (⊤ : Subgroup G) ≤ normalizer (K : Set G) := by
    rw [← h.generated, ← local_pair_sup i]
    exact sup_le hi hj
  let : K.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  exact bot_unique ((normal_le_normalCore.mpr hK).trans h.common_core_eq_bot.le)

private theorem overlap_ne_bot (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3))) :
    F false ⊓ F true ≠ ⊥ := by
  intro hbot
  let : Finite (F false) := h.finite false
  let P := overlapSylow h false
  have hP : (P : Subgroup (F false)) = ⊥ := by
    change (F false ⊓ F true).subgroupOf (F false) = ⊥
    rw [hbot, bot_subgroupOf]
  have hc : Nat.card (F false) = 3 := by
    have hi := h.overlap_relIndex false
    change (P : Subgroup (F false)).index = 3 at hi
    simpa only [hP, index_bot] using hi
  have hr : pResidual 2 (F false) = ⊤ := by
    simpa only [hP, sup_bot_eq] using pResidual_sup_sylow_eq_top P
  apply hC false
  refine ⟨mulEquivOfPrimeCardEq (p := 3) ?_ (by simp)⟩
  rw [hr, Nat.card_congr Subgroup.topEquiv.toEquiv]
  exact hc

private theorem opposite_characteristic_not_normal (h : CubicTreeAction F)
    (i : Bool) (hi : ((F false ⊓ F true).subgroupOf (F i)).Normal)
    (K : Subgroup (overlapSylow h (!i))) (hK : K.Characteristic) (hne : K ≠ ⊥) :
    ¬ (K.map (overlapSylow h (!i) : Subgroup (F (!i))).subtype).Normal := by
  intro hn
  let : K.Characteristic := hK
  let P := overlapSylow h (!i)
  let D := K.map (P : Subgroup (F (!i))).subtype
  let H := D.map (F (!i)).subtype
  have hPT : (P : Subgroup (F (!i))).map (F (!i)).subtype = F false ⊓ F true :=
    map_subgroupOf_eq_of_le (overlap_le_local (!i))
  have hH : H ≤ F false ⊓ F true := by
    rw [← hPT]
    exact map_mono (map_subtype_le K)
  have hiN : F i ≤ normalizer (H : Set G) := by
    have hiT := (normal_subgroupOf_iff_le_normalizer (overlap_le_local i)).mp hi
    have hc := normalizer_le_normalizer_characteristic_map (F (!i)).subtype
      (F (!i)).subtype_injective (P : Subgroup (F (!i))) K
    rw [hPT] at hc
    exact hiT.trans hc
  have hjN : F (!i) ≤ normalizer (H : Set G) := by
    let : D.Normal := hn
    have hh := D.le_normalizer_map (F (!i)).subtype
    simpa only [D.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have he := local_normalized_overlap_eq_bot h H hH i hiN hjN
  apply hne
  apply (map_eq_bot_iff_of_injective K (P : Subgroup (F (!i))).subtype_injective).mp
  exact (map_eq_bot_iff_of_injective D (F (!i)).subtype_injective).mp he

/-- The original overlap is nonnormal at either endpoint after excluding the
small residual cases. -/
theorem CubicTreeAction.overlap_not_normal_of_large_residual (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (i : Bool) : ¬ ((F false ⊓ F true).subgroupOf (F i)).Normal := by
  intro hi
  let : Finite (F (!i)) := h.finite (!i)
  let P := overlapSylow h (!i)
  have hn : ¬ (P : Subgroup (F (!i))).Normal := by
    intro hj
    apply overlap_ne_bot h hC
    exact local_normalized_overlap_eq_bot h _ le_rfl i
      ((normal_subgroupOf_iff_le_normalizer (overlap_le_local i)).mp hi)
      ((normal_subgroupOf_iff_le_normalizer (overlap_le_local (!i))).mp hj)
  have hp : pCore 2 (F (!i)) < (P : Subgroup (F (!i))) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    apply hn
    rw [← he]
    infer_instance
  obtain ⟨e⟩ := sylow_index_three_core_quotient P (h.overlap_relIndex (!i)) hp
  rcases local_residual_cubic_or_alternatingFour e P
    (opposite_characteristic_not_normal h i hi) with hc | ha
  · exact hC (!i) hc
  · exact hA (!i) ha

/-- The quotient of each original local group by its own two-core is S₃. -/
theorem CubicTreeAction.local_quotient_symmetricThree_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (i : Bool) : Nonempty (((F i) ⧸ pCore 2 (F i)) ≃* Equiv.Perm (Fin 3)) := by
  let : Finite (F i) := h.finite i
  let P := overlapSylow h i
  apply sylow_index_three_core_quotient P (h.overlap_relIndex i)
  refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
  intro he
  apply h.overlap_not_normal_of_large_residual hC hA i
  change (P : Subgroup (F i)).Normal
  rw [← he]
  infer_instance

private theorem residual_cubic_of_normal_three {H : Type*} [Group H] [Finite H]
    (S : Subgroup H) (hS : IsPGroup 2 S) (hi : S.index = 3)
    (P : Sylow 3 H) [(P : Subgroup H).Normal] :
    Nonempty ((pResidual 2 H) ≃* Multiplicative (ZMod 3)) := by
  have hc := card_sylow_three_of_two_group_index_three S hS hi P
  have hcomp := three_complement_of_two_group_index_three S (P : Subgroup H) hS hi hc
  have hr : pResidual 2 H = (P : Subgroup H) := by
    apply le_antisymm
    · exact sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top
        (P : Subgroup H) S hS hcomp.sup_eq_top⟩
    · intro x hx
      apply mem_pResidual_of_orderOf_coprime
      exact (by decide : Nat.Coprime 2 3).of_dvd_right
        (hc ▸ (P : Subgroup H).orderOf_dvd_natCard hx)
  refine ⟨mulEquivOfPrimeCardEq (p := 3) ?_ (by simp)⟩
  rw [hr]
  exact hc

/-- A normal local Sylow three-subgroup would be the excluded cubic residual. -/
theorem CubicTreeAction.local_sylow_three_not_normal_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (i : Bool) (P : Sylow 3 (F i)) : ¬ (P : Subgroup (F i)).Normal := by
  intro hn
  let : Finite (F i) := h.finite i
  let : (P : Subgroup (F i)).Normal := hn
  exact hC i (residual_cubic_of_normal_three _ (overlapSylow h i).isPGroup'
    (h.overlap_relIndex i) P)

private noncomputable def localStabilizerEquiv (v : RankTwo.Vertex F) :
    F v.type ≃* RankTwo.stabilizer F v := by
  let g := (exists_smul_base F v).choose
  have hg : g • base F v.type = v := (exists_smul_base F v).choose_spec
  exact (MulEquiv.subgroupCongr (stabilizer_base F v.type).symm).trans
    (MulAction.stabilizerEquivStabilizer hg.symm)

/-- The actual vertex stabilizer has the required S₃ quotient by its two-core. -/
theorem CubicTreeAction.stabilizer_quotient_symmetricThree_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (v : RankTwo.Vertex F) : Nonempty
      (((RankTwo.stabilizer F v) ⧸ pCore 2 (RankTwo.stabilizer F v)) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := h.local_quotient_symmetricThree_of_large_residual hC hA v.type
  let f := localStabilizerEquiv v
  exact ⟨(QuotientGroup.congr _ _ f.symm (pCore_map_iso 2 f.symm)).trans e⟩

/-- No Sylow three-subgroup of an actual vertex stabilizer is normal. -/
theorem CubicTreeAction.stabilizer_sylow_three_not_normal_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (v : RankTwo.Vertex F) (P : Sylow 3 (RankTwo.stabilizer F v)) :
    ¬ (P : Subgroup (RankTwo.stabilizer F v)).Normal := by
  intro hn
  let f := localStabilizerEquiv v
  let : Finite (F v.type) := h.finite v.type
  let : Finite (RankTwo.stabilizer F v) := Finite.of_equiv (F v.type) f.toEquiv
  let Q := P.mapSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  apply h.local_sylow_three_not_normal_of_large_residual hC v.type Q
  exact hn.map f.symm.toMonoidHom f.symm.surjective

/-- Each actual vertex stabilizer has a self-centralizing two-core. This is
the local input for the positive margins of a central-involution interval. -/
theorem CubicTreeAction.stabilizer_centralizer_twoCore_le_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (v : RankTwo.Vertex F) :
    centralizer (pCore 2 (RankTwo.stabilizer F v) : Set (RankTwo.stabilizer F v)) ≤
      pCore 2 (RankTwo.stabilizer F v) := by
  let f := localStabilizerEquiv v
  let : Finite (F v.type) := h.finite v.type
  let : Finite (RankTwo.stabilizer F v) := Finite.of_equiv (F v.type) f.toEquiv
  obtain ⟨e⟩ := h.stabilizer_quotient_symmetricThree_of_large_residual hC hA v
  have hfit : generalizedFitting (RankTwo.stabilizer F v) =
      pCore 2 (RankTwo.stabilizer F v) := by
    by_contra hn
    have hc : Nat.card (pResidual 2 (RankTwo.stabilizer F v)) = 3 := by
      rw [SymmetricThreeTwoCore.residual_eq_oddCore e hn]
      exact SymmetricThreeTwoCore.oddCore_card_of_not_characteristic_two e hn
    apply hC v.type
    let r := (f.subgroupMap (pResidual 2 (F v.type))).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 f))
    exact ⟨r.trans (mulEquivOfPrimeCardEq hc (by simp))⟩
  rw [← hfit]
  exact centralizer_generalizedFitting_le (RankTwo.stabilizer F v)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
