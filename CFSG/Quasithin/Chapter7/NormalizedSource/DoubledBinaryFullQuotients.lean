module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarRadicals
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarIntersection
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.Alternating.OddCentralCovers
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups

/-!
# Full component quotients and marked binary intersections

The remaining doubled-orbit catalogue identifies the literal comparison
K/O₂(K) → K*. Cyclic odd Sylow transfer treats SL₃(2); the alternating
multiplier treats A₈; the universal cover treats SL₅(2). In the triple-six
row the source center bound forces injectivity while preserving the cubic
center. Thus the original component's star kernel is exactly O₂(K).

The original orbit in the canonical star module places the full kernel in
M. A component Sylow inside the original local Sylow then marks a complete
binary flag, and M ∩ K is exactly the inverse image of a partial flag in the
same coordinates. The moving two-perfect residual excludes a complete flag;
escape excludes the empty flag. Both the full kernel and intersection index
are retained. These conclusions identify group quotients and intersections,
without asserting full block recognition or ambient containment.

The Chapter12 companion discharges all premises on the original chosen
module. Source: Aschbacher--Smith, proof after 7.7.10, pp.708--709, C.2.7,
pp.145--147, and I.1.2--3, p.407, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFullQuotients
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K Q M : Subgroup G}

private def comparisonCover (h : Input KnownSimple.IsKnownSimple H Q M K) :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K) (starImage K Q K) where
  toMonoidHom := coreToStar h.normalizes
  surjective := coreToStar_surjective h.normalizes
  isPerfect := h.quasisimple.toIsPerfect
  ker_le_center := coreToStar_ker_central_from_source h

private def modelCover {A : Type*} [Group A]
    (h : Input KnownSimple.IsKnownSimple H Q M K) (e : starImage K Q K ≃* A) :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K) A where
  toMonoidHom := e.toMonoidHom.comp (coreToStar h.normalizes)
  surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
  isPerfect := h.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source h

/-- No odd central kernel survives above the binary three-dimensional model. -/
theorem linearThree_comparison_injective
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (F : BinaryField) (hF : F.degree = 1)
    (e : starImage K Q K ≃* SL(3,F.Carrier)) :
    Function.Injective (coreToStar h.normalizes) := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  let a : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,F.card_eq,hF]
    simp)
  let b := modelCover h (e.trans (Atlas.fieldEquivSL 3 a))
  let c := Matrix.PSL3Two.centralCoverEquiv b (pCore_quotient_pCore_eq_bot 2)
  intro x y he
  apply c.injective
  rw [Matrix.PSL3Two.centralCoverEquiv_apply,Matrix.PSL3Two.centralCoverEquiv_apply]
  exact congrArg (e.trans (Atlas.fieldEquivSL 3 a)) he

/-- The nonexceptional alternating multiplier removes the comparison kernel
in the four-dimensional binary model, retaining the literal star map. -/
theorem alternatingEight_comparison_injective
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (e : starImage K Q K ≃* alternatingGroup (Fin 8)) :
    Function.Injective (coreToStar h.normalizes) := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let f := modelCover h e
  let a := f.quotientCenterEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot)
  have hd := GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
    8 (by decide) (by decide) (by decide) a
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 1 := by
    rcases coreQuotient_center_card_from_source h with hh | hh
    · exact hh
    · rw [hh] at hd
      norm_num at hd
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique ((coreToStar_ker_central_from_source h).trans_eq ((eq_bot_iff_card _).mpr hc))

/-- Universality of the actual PSL₅(2) identity removes the full comparison kernel. -/
theorem linearFive_comparison_injective
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (e : starImage K Q K ≃* SL(5,ZMod 2)) :
    Function.Injective (coreToStar h.normalizes) := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : IsQuasisimple PSL(5,ZMod 2) := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple _
  let a := e.trans Theory.SpecificGroups.PSL5Two.UniversalCover.projectiveEquivSL.symm
  let f := (modelCover h a).toCovering
  have hd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
    (Covering.id : Covering PSL(5,ZMod 2) PSL(5,ZMod 2))
    Theory.SpecificGroups.PSL5Two.UniversalCover.identity_isUniversal f
  have hc : Nat.card f.toMonoidHom.ker = 1 := by simpa using hd
  have hi : Function.Injective f.toMonoidHom :=
    (MonoidHom.ker_eq_bot_iff _).mp ((eq_bot_iff_card _).mpr hc)
  exact fun _ _ he => hi (congrArg a he)

/-- If the star component retains its cubic center, the source center bound
forces the comparison to retain it faithfully as well. -/
theorem cubicCenter_comparison_injective
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (hc : Nat.card (center (starImage K Q K)) = 3) :
    Function.Injective (coreToStar h.normalizes) := by
  let f := comparisonCover h
  have hm : (center (K ⧸ pCore 2 K)).map f.toMonoidHom = center (starImage K Q K) := by
    rw [←f.comap_center,map_comap_eq_self_of_surjective f.surjective]
  have hker := (coreToStar_ker_central_from_source h)
  let r := f.toMonoidHom.subgroupMap (center (K ⧸ pCore 2 K))
  have hd := r.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr (f.toMonoidHom.subgroupMap_surjective _),card_top] at hd
  have hkcard : Nat.card r.ker = Nat.card f.toMonoidHom.ker := by
    change Nat.card (f.toMonoidHom.subgroupMap _).ker = _
    rw [ker_subgroupMap]
    exact Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv
  rw [hkcard,hm,hc] at hd
  rcases coreQuotient_center_card_from_source h with hh | hh
  all_goals
    rw [hh] at hd
    have hk : Nat.card f.toMonoidHom.ker = 1 := by omega
    exact (MonoidHom.ker_eq_bot_iff _).mp ((eq_bot_iff_card _).mpr hk)

/-- The previous exhaustive exclusions now identify the literal core quotient
with the star component, including the cubic center of the triple-six row. -/
theorem comparison_injective_of_remaining
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (hm : DoubledBinaryStarRadicals.RemainingStarModel (starImage K Q K))
    (h6 : ¬ Nonempty (starImage K Q K ≃* alternatingGroup (Fin 6)))
    (h7 : ¬ Nonempty (starImage K Q K ≃* alternatingGroup (Fin 7)))
    (hg : ¬ Nonempty (starImage K Q K ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Function.Injective (coreToStar h.normalizes) := by
  rcases hm with h3 | hrest
  · obtain ⟨F,hF,⟨e⟩⟩ := h3
    exact linearThree_comparison_injective h F hF e
  rcases hrest with halt | hrest
  · obtain ⟨n,hn,⟨e⟩⟩ := halt
    rcases hn with rfl | rfl | rfl
    · exact (h6 ⟨e⟩).elim
    · exact (h7 ⟨e⟩).elim
    · exact alternatingEight_comparison_injective h e
  rcases hrest with hg2 | hrest
  · exact (hg hg2).elim
  rcases hrest with h5 | ht
  · obtain ⟨e⟩ := h5
    exact linearFive_comparison_injective h e
  · obtain ⟨⟨e⟩,_⟩ := ht
    exact cubicCenter_comparison_injective h (by rw [Nat.card_congr e.toEquiv]; simp)

omit [Finite G] in
/-- Identification of the comparison map removes exactly O₂(K) from K. -/
theorem star_kernel_eq_core
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (hf : Function.Injective (coreToStar h.normalizes)) :
    (toStarImage K Q).ker = pCore 2 K := by
  change ((coreToStar h.normalizes).comp (QuotientGroup.mk' (pCore 2 K))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ hf,QuotientGroup.ker_mk']

omit [Finite G] in
/-- The kernel fixes the original orbit, hence belongs to the original marked
intersection. This retains the full star centralizer, not just its two-core. -/
theorem kernel_le_intersection (W : Subgroup G)
    (hW : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hc : K ⊓ centralizer (W : Set G) ≤ M) :
    (toStarImage K Q).ker ≤ M.subgroupOf K := by
  intro k hk
  apply hc
  refine ⟨k.property,?_⟩
  have hstar : inclusion (show K ≤ K ⊔ Q from le_sup_left) k ∈ starKernel K Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val hk
  intro w hw
  obtain ⟨v,hv,he⟩ := hW hw
  subst w
  exact congrArg Subtype.val (hstar v hv)

omit [Finite G] in
/-- Exact preimage of the marked intersection under the literal star map. -/
theorem intersection_star_preimage (W : Subgroup G)
    (hW : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hc : K ⊓ centralizer (W : Set G) ≤ M) :
    ((starM K Q M).subgroupOf (starImage K Q K)).comap (toStarImage K Q) =
      M.subgroupOf K := by
  rw [←DoubledBinaryStarIntersection.intersection_star_map,comap_map_eq,
    sup_eq_left.mpr (kernel_le_intersection W hW hc)]

omit [Finite G] in
private theorem intersection_image_not_twoGroup
    {Z : Type*} [Group Z] (f : K →* Z) (W A : Subgroup G)
    (hk : f.ker ≤ (centralizer (W : Set G)).subgroupOf K)
    (hAK : A ≤ K) (hAM : A ≤ M) (hp : IsPPerfect 2 A)
    (hm : ⁅W,A⁆ ≠ ⊥) : ¬ IsPGroup 2 ((M.subgroupOf K).map f) := by
  intro hB
  let g : A →* (M.subgroupOf K).map f :=
    (f.comp (inclusion hAK)).codRestrict _
      (fun a => mem_map_of_mem f (hAM a.property))
  have hz := hp.hom_eq_one_of_isPGroup hB g
  apply hm
  rw [commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  have hgz : g (⟨a,ha⟩ : A) = 1 := by
    simpa only [MonoidHom.one_apply] using DFunLike.congr_fun hz (⟨a,ha⟩ : A)
  have hzero := congrArg (fun b : (M.subgroupOf K).map f => (b : Z)) hgz
  exact hk hzero

open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

/-- The original Sylow and intersection have a common complete/partial binary
flag, and the full intersection is its inverse image with kernel exactly O₂(K). -/
theorem binary_flag_intersection
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (hf : Function.Injective (coreToStar h.normalizes))
    (W : Subgroup G) (hW : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hc : K ⊓ centralizer (W : Set G) ≤ M)
    (A : Subgroup G) (hAK : A ≤ K) (hAM : A ≤ M)
    (hp : IsPPerfect 2 A) (hm : ⁅W,A⁆ ≠ ⊥)
    (S : Sylow 2 K) (hSM : (S : Subgroup K).map K.subtype ≤ M)
    {m : ℕ} (e : starImage K Q K ≃* SL(m+1,ZMod 2)) :
    let f := (e.trans (slEquivLinear (m+1))).toMonoidHom.comp (toStarImage K Q)
    ∃ (b : Basis m) (cuts : Set (Fin m)), cuts.Nonempty ∧ cuts ≠ Set.univ ∧
      (S : Subgroup K).map f = cutStabilizer b Set.univ ∧
      (M.subgroupOf K).map f = cutStabilizer b cuts ∧
      M.subgroupOf K = (cutStabilizer b cuts).comap f ∧
      f.ker = pCore 2 K ∧
      (M.subgroupOf K).index = (cutStabilizer b cuts).index := by
  dsimp only
  let a := e.trans (slEquivLinear (m+1))
  let f := a.toMonoidHom.comp (toStarImage K Q)
  have hfs : Function.Surjective f := a.surjective.comp (toStarImage_surjective K Q)
  have hk : f.ker ≤ M.subgroupOf K := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    exact kernel_le_intersection W hW hc
  let P := S.mapSurjective hfs
  let B := (M.subgroupOf K).map f
  have hPB : (P : Subgroup _) ≤ B := by
    apply map_mono
    intro x hx
    exact hSM (mem_map_of_mem K.subtype hx)
  obtain ⟨b,cuts,hP,hB⟩ := BinaryLinear.SylowFlagOvergroups.exists_flag_of_sylow_le P B hPB
  have hpre : B.comap f = M.subgroupOf K := by
    rw [comap_map_eq,sup_eq_left.mpr hk]
  have hproper : B ≠ ⊤ := by
    intro ht
    have he : M.subgroupOf K = ⊤ := by rw [←hpre,ht,comap_top]
    exact h.outside (subgroupOf_eq_top.mp he)
  have hnp : ¬ IsPGroup 2 B := intersection_image_not_twoGroup f W A (by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    exact kernel_le_intersection W hW inf_le_right) hAK hAM hp hm
  refine ⟨b,cuts,?_,?_,hP,hB,?_,?_,?_⟩
  · by_contra hn
    apply hproper
    rw [hB,Set.not_nonempty_iff_eq_empty.mp hn]
    ext x
    simp only [mem_cutStabilizer,Set.mem_empty_iff_false,forall_false,forall_true_iff,mem_top]
  · intro hfull
    apply hnp
    have he : B = (P : Subgroup _) := by rw [hB,hfull,←hP]
    exact he.symm ▸ P.isPGroup'
  · exact hpre.symm.trans (congrArg (comap f) hB)
  · rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    exact star_kernel_eq_core h hf
  · rw [←hB]
    exact ((M.subgroupOf K).index_map_eq hfs hk).symm

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFullQuotients
