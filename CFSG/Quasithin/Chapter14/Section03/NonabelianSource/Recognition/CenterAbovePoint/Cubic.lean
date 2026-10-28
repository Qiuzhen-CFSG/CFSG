module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Residual
public import Theory.GroupTheory.CubicSylowJoin

/-!
# Cubic exclusion inside the center-centralizing residual

A normal cubic in the dotted image of a normal subgroup centralizing Z(U)
lifts with two-group kernel. Its join with the ambient Sylow has index three,
so original 14.2.20 places it in M. The seed-line and orbit-generation
argument then kills its dotted image, a contradiction. This works without
the center-point equality, and is applied to the actual residual of 14.3.15.

Source: Aschbacher--Smith 14.3.5 and 14.3.15, printed pp.992,995.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {L M : Subgroup G}
/-- A normal cubic inside the dotted image of a normal center-centralizing
subgroup lifts with two-group kernel. Original cubic-index recognition then
places it in M, contradicting its action on the spanning seed orbit. -/
theorem no_normal_cubic_in_dot_of_center_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (A : Subgroup G) (hAH : A ≤ F.H)
    (hHA : F.H ≤ normalizer (A : Set G)) (hAC : A ≤ centralizer (F.ZU : Set G))
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : Nat.card C = 3)
    (hCA : C ≤ F.terminalDot A) : False := by
  classical
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let D := A.subgroupOf F.H ⊓ C.comap q
  let : (A.subgroupOf F.H).Normal := (normal_subgroupOf_iff_le_normalizer hAH).mpr hHA
  let : D.Normal := inferInstance
  let DA := D.map F.H.subtype
  have hDH : DA ≤ F.H := map_subtype_le _
  have hHD : F.H ≤ normalizer (DA : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      D.le_normalizer_map F.H.subtype
  have hmap : D.map q = C := by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact ha.2
    · intro c hc
      obtain ⟨a,ha,he⟩ := hCA hc
      exact ⟨a,⟨ha,show q a ∈ C from he.symm ▸ hc⟩,he⟩
  let f : D →* F.TerminalHdot := q.comp D.subtype
  have hfr : f.range = C := by
    rw [MonoidHom.range_comp,D.range_subtype]
    exact hmap
  have hker : IsPGroup 2 f.ker := by
    have hp : IsPGroup 2 ((pCore 2 F.H).comap D.subtype) :=
      pCore_isPGroup.comap_subtype
    apply hp.to_le
    intro a ha
    exact terminal_kernel_centralizer_le_core F d
      ⟨hAC a.property.1,(QuotientGroup.eq_one_iff (a : F.H)).mp ha⟩
  obtain ⟨n,hn⟩ := hker.exists_card_eq
  have hcD : Nat.card DA = 3 * 2 ^ n := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hfr,hC,hn] at hh
    rw [Nat.card_congr (equivMapOfInjective D F.H.subtype F.H.subtype_injective).symm.toEquiv]
    exact hh.symm.trans (Nat.mul_comm _ _)
  have hDtwo : ¬ IsPGroup 2 DA := by
    intro hp
    have hc3 : 3 ∣ Nat.card DA := by rw [hcD]; exact dvd_mul_right _ _
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk] at hc3
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hc3)
  have hTJ : (T : Subgroup G) ≤ DA ⊔ T := le_sup_right
  have hJH : DA ⊔ (T : Subgroup G) ≤ F.H := sup_le hDH (F.invariant 1)
  have hJmem : DA ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTJ hJH
      ⟨(h.pointNormalizer_mem_Hz F).1.1,F.invariant 1⟩
  have hi : (T : Subgroup G).relIndex (DA ⊔ T) = 3 :=
    normalized_cubic_join_index_of_card_dvd T DA ((F.invariant 1).trans hHD)
      ⟨n,hcD ▸ dvd_refl _⟩ hDtwo
  have hDM : DA ≤ M := by
    apply (show DA ≤ DA ⊔ (T : Subgroup G) from le_sup_left).trans
    by_contra hout
    exact hnot (SolvableAmalgam.source_theoremE_of_index_three hG T hempty hM hu hmany
      hcard e (DA ⊔ T) hJmem hout hi)
  have hb := terminalDot_eq_bot_of_normalizes_seed F d DA hDH hHD
    (hDM.trans RankTwoHypothesis.M_normalizes_seed)
  have hdot : F.terminalDot DA = C := by
    change (DA.comap F.H.subtype).map q = C
    rw [comap_map_eq_self_of_injective F.H.subtype_injective]
    exact hmap
  rw [hdot] at hb
  simp [hb] at hC


/-- Original 14.3.15 applied to its actual residual: no ambient-normal cubic
can lie in its dotted image. The parent source producer supplies this same F. -/
theorem no_normal_cubic_in_center_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : Nat.card C = 3)
    (hCK : C ≤ F.terminalDot (centerConjugateResidual F g)) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hg := F.conjugate_center_le_H g (F.P_le_seed_normalizer _ h.L_normalizes_seed hgP)
  exact no_normal_cubic_in_dot_of_center_centralizer hG T hempty hM hu hmany hcard e hnot F d
    (centerConjugateResidual F g) (centerConjugateResidual_le_H F g hg)
    (centerConjugateResidual_normalized F g)
    (centerConjugateResidual_centralizes F g (rankTwo_centers_commute h F d hne g hgP hgH)) C hC hCK


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
