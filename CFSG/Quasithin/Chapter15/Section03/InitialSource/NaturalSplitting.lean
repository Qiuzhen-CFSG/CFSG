module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.OddImage
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SylowGeneration
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.ThompsonRank
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.FixedComplement
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Centralizer
public import Mathlib.RepresentationTheory.Invariants
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.InvariantSummands


/-!
# Elimination of the original fixed summand in 14.1.7

The actual quotient factors are the ones constructed from B.2.7 and the
proved solvable B.1.8 theorem. Their centralizer fixes the nonzero moved
module. If their fixed summand is nonzero, the original unique-overgroup
hypothesis places both the product and its centralizer in Mc. The Sylow
supplement then forces M = Mc. Alternatively, if Ω₁Z(T) has order two,
the complementary nonzero invariant summands would yield two distinct
central involutions. Both original alternatives therefore kill the fixed
summand. Faithfulness kills the factor centralizer as well.

The final producer derives all these conclusions for the original reduced
U, preserving its literal M/C_M(U) action, natural planes and selected
J(M) image. Only the genuine universal Theorems A and C remain earlier
inputs. Neither solvability of M nor a natural-action conclusion is assumed.
Source: Aschbacher–Smith, 14.1.7, printed p.977.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

/-- A normal actor with nonzero fixed space has its full preimage inside Mc. -/
theorem normal_actor_preimage_le_partner_of_fixed_ne_bot
    (T : Sylow 2 G) {M Mc : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (A : Subgroup (M ⧸ centralizer (U : Set M))) [A.Normal]
    (hfix : fixedSpace (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) A ≠ ⊥) :
    (A.comap (QuotientGroup.mk' (centralizer (U : Set M)))).map M.subtype ≤ Mc := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  have he : (A.comap q).map q = A := map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) A
  by_contra hescape
  have hbot := fixed_eq_bot_of_image_normalized T hTM hunique U (A.comap q)
    (by rw [he]; exact le_normalizer_of_normal) hescape
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  have hc : (v.toMul : M) ∈ centralizer (A.comap q : Set M) :=
    (NormalElementaryQuotient.mem_fixedSpace_image U q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) (A.comap q) v).mp (he.symm ▸ hv)
  have hm : (v.toMul : M) ∈ U ⊓ centralizer (A.comap q : Set M) := ⟨v.toMul.property, hc⟩
  rw [hbot] at hm
  apply hv0
  exact Additive.toMul.injective (Subtype.ext (Subgroup.mem_bot.mp hm))

/-- Fixed-summand elimination on the original M ≠ Mc branch. -/
theorem fixed_eq_bot_of_factors_and_ne_partner
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hneq : M ≠ Mc) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (d : ChapterB.SolvableFFFactors (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)))
    (hn : d.count = 1 ∨ d.count = 2) :
    fixedSpace (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
      (offenderSubgroup (NormalElementaryQuotient.representation U
        (QuotientGroup.mk' (centralizer (U : Set M)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))) = ⊥ := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let K := offenderSubgroup ρ
  let C := centralizer (K : Set (M ⧸ centralizer (U : Set M)))
  let W := subspaceCommutator ρ ⊤ K
  let : K.Normal := offenderSubgroup_normal ρ
  let : C.Normal := inferInstance
  change fixedSpace ρ K = ⊥
  by_contra hF
  have hKMc := normal_actor_preimage_le_partner_of_fixed_ne_bot T hM.2 hunique U K hF
  have hWne : W ≠ ⊥ := by
    intro he
    have hi : subspaceCommutator ρ ⊤ (d.factor ⟨0, d.count_pos⟩) ≤ W := by
      exact (le_iSup (fun j => subspaceCommutator ρ ⊤ (d.factor j))
        ⟨0, d.count_pos⟩).trans d.iSup_support.le
    exact d.support_ne_bot ⟨0, d.count_pos⟩ (bot_unique (he ▸ hi))
  have hCW : W ≤ fixedSpace ρ C := by
    intro v hv c
    exact d.centralizer_fixes_moved c c.property hv
  have hCfix : fixedSpace ρ C ≠ ⊥ := fun he => hWne (bot_unique (he ▸ hCW))
  have hCMc := normal_actor_preimage_le_partner_of_fixed_ne_bot T hM.2 hunique U C hCfix
  let S := T.subtype hM.2
  let B := Mc.subgroupOf M
  have hKB : K.comap q ≤ B := by
    intro x hx
    exact hKMc (mem_map_of_mem M.subtype hx)
  have hCB : C.comap q ≤ B := by
    intro x hx
    exact hCMc (mem_map_of_mem M.subtype hx)
  have hSB : (S : Subgroup M) ≤ B := by
    intro t ht
    apply centralizer_le_partner T hunique
    intro z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hKm : K ≤ B.map q := by
    rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) (H := K)]
    exact map_mono hKB
  have hCm : C ≤ B.map q := by
    rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) (H := C)]
    exact map_mono hCB
  have hgen := d.sylow_factor_generation hn (S.mapSurjective (QuotientGroup.mk'_surjective _))
  have hBm : B.map q = ⊤ := top_unique (by
    rw [← hgen]
    exact sup_le (sup_le hKm hCm) (map_mono hSB))
  have hker : q.ker ≤ B := by
    intro x hx
    apply hKB
    change q x ∈ K
    rw [show q x = 1 from hx]
    exact K.one_mem
  have hBtop : B = ⊤ := by
    rw [← comap_map_eq_self hker, hBm, comap_top]
  have hMMc : M ≤ Mc := by
    intro x hx
    exact (show (⟨x, hx⟩ : M) ∈ B by rw [hBtop]; trivial)
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  exact hneq (hM.1.eq_of_le hMc.1 hMMc)


end CFSG.Quasithin.Chapter15.Section03.InitialSource


open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

/-- The source central involution line also eliminates the fixed summand. -/
theorem fixed_eq_bot_of_factors_and_central_order_two
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hZ : Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (d : ChapterB.SolvableFFFactors (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))) :
    fixedSpace (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
      (offenderSubgroup (NormalElementaryQuotient.representation U
        (QuotientGroup.mk' (centralizer (U : Set M)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))) = ⊥ := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let K := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let W := subspaceCommutator ρ ⊤ K
  let F := fixedSpace ρ K
  have hWne : W ≠ ⊥ := by
    intro he
    have hi : subspaceCommutator ρ ⊤ (d.factor ⟨0, d.count_pos⟩) ≤ W :=
      (le_iSup (fun j => subspaceCommutator ρ ⊤ (d.factor j))
        ⟨0, d.count_pos⟩).trans d.iSup_support.le
    exact d.support_ne_bot ⟨0, d.count_pos⟩ (bot_unique (he ▸ hi))
  have hW := subspaceCommutator_invariant_normalizer ρ
    (A := ((T.subtype hTM : Sylow 2 M) : Subgroup M).map q) (X := K)
    (le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top))
    (le_normalizer_of_normal)
  have hF : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map q ≤ subspaceStabilizer ρ F :=
    le_subspaceStabilizer ρ F (fun g _ v hv => Representation.le_comap_invariants ρ K g hv)
  exact (disjoint_stable_subspaces_of_central_order_two T hTM hZ U W F
    d.moved_complement.disjoint hW hF).resolve_left hWne

universe u

/-- The actual original reduced action is the sum of its one or two natural planes. -/
theorem reduced_natural_sum_from_source
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let P := ChapterB.maxOffenderImages (⊤ : Subgroup M) U q
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧ IsStable (V := Additive U) ρ P ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q = generatedBy P ⊤ ∧
      (d.toSolvableFFFactors.stableFactorSet P).Nonempty ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q =
        ⨆ i ∈ d.toSolvableFFFactors.stableFactorSet P, d.factor i ∧
      fixedSpace ρ (offenderSubgroup ρ) = ⊥ ∧
      subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤ ∧
      centralizer (offenderSubgroup ρ : Set (M ⧸ centralizer (U : Set M))) = ⊥ := by
  let := hU.normal
  let := hU.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  obtain ⟨d, hd⟩ := reduced_thompson_factors_from_source hA hC hG T hempty hH U hU hJ
  have hrank : primeRank 3 M ≤ 2 :=
    Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG.quasithin M hM.1.1 3 (by decide) (by decide)
  have hn := d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank q
    (QuotientGroup.mk'_surjective _) hrank
  have hF : fixedSpace ρ (offenderSubgroup ρ) = ⊥ := by
    rcases hcase with hneq | hZ
    · exact fixed_eq_bot_of_factors_and_ne_partner T hM hunique hneq U
        d.toSolvableFFFactors hn
    · exact fixed_eq_bot_of_factors_and_central_order_two T hM.2 hZ U d.toSolvableFFFactors
  have hW : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤ := by
    have he := d.toSolvableFFFactors.moved_complement.sup_eq_top
    rw [hF, sup_bot_eq] at he
    exact he
  have hcentral : centralizer (offenderSubgroup ρ : Set (M ⧸ centralizer (U : Set M))) = ⊥ := by
    apply bot_unique
    intro c hc
    apply Subgroup.mem_bot.mpr
    apply NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    apply LinearMap.ext
    intro v
    change ρ c v = ρ 1 v
    rw [map_one, Module.End.one_apply]
    exact d.toSolvableFFFactors.centralizer_fixes_moved c hc (hW.symm ▸ Submodule.mem_top)
  exact ⟨d, hn, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, hF, hW, hcentral⟩


end CFSG.Quasithin.Chapter15.Section03.InitialSource