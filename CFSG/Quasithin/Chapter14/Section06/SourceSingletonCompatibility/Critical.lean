module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonClassification
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCritical
public import Theory.Representation.BinaryQuinticDisplacement

/-!
# Critical geometry of the original elementary-nine singleton

The singleton endpoint has cubic ratio two. If a critical conjugate of U
lay in O₂(J), the point commutator bound would make every nontrivial
involution in its inverse conjugate move at most one dimension on U/Z.
The ratio-two bound forbids this. Thus the same critical conjugate escapes
the core, and F.9.17 reverses every J-normalized label with one conjugator.
The abelian Mc-span also forces the critical conjugator outside Mc.

The source consumer discharges starred cyclicity using the primitive
singleton theorem. These conclusions supply critical geometry; they do
not yet exclude the elementary-nine endpoint.
Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032, and F.9.13--17.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab


/-- Ratio two forces the same critical span outside the original two-core. -/
theorem source_rankTwo_critical_core_escape_of_ratio_two
    (J : Subgroup G) (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (hq : cubicRatio a.representation = 2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
    ∀ i : h.CriticalEndpoint, ¬ i.conjugate D.UH ≤ D.QH := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  have hUV : D.UH = D.VH := rfl
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ
  change ∀ i : h.CriticalEndpoint, ¬ i.conjugate D.UH ≤ D.QH
  intro i hc
  let g := i.representative
  let A := D.UH.conjBy g⁻¹
  let B := D.V₁.conjBy g⁻¹
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ D.H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (i.reverse_le hb)
    change (D.VH.conjBy g⁻¹) ≤ (D.H.conjBy g).conjBy g⁻¹ at hh
    rw [conjBy_inv] at hh
    simpa only [A,hUV] using hh
  have hAB : ⁅A,D.UH⁆ ≤ B := by
    have hh := (commutator_mono le_rfl hc).trans h.commutator_UH_QH_le_point
    have hh' := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
    rw [map_commutator] at hh'
    change ⁅A,(D.UH.conjBy g).conjBy g⁻¹⁆ ≤ B at hh'
    rwa [conjBy_inv] at hh'
  have hB : Nat.card B = 2 :=
    (card_map_of_injective (MulAut.conj g⁻¹).injective).trans h.point_card
  let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
  let σ := a.representation
  have hqσ : cubicRatio σ = 2 := hq
  let c : Representation.BinaryConjugationSection D.H D.UH D.V₁
      (σ.comp (QuotientGroup.mk' (pCore 2 D.H))) := {
    section_le := a.le_local
    kernel_le := a.kernel_le
    normalized := a.normalizes
    coordinates := (MulEquiv.multiplicativeAdditive (D.UH ⧸ D.V₁.subgroupOf D.UH)).symm.toMonoidHom.comp
      (QuotientGroup.mk' (D.V₁.subgroupOf D.UH))
    onto := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
      (QuotientGroup.mk'_surjective _)
    kernel_eq := by ext u; exact QuotientGroup.eq_one_iff u
    equivariant := fun x u => (a.conjugation x u).symm }

  have hker : A.subgroupOf D.H ≤ (QuotientGroup.mk' (pCore 2 D.H)).ker := by
    intro x hx
    by_contra hn
    let t := QuotientGroup.mk' (pCore 2 D.H) x
    have ht : t ≠ 1 := hn
    have hx2 : x ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (x : G) (show (x : G) ∈ A from hx))
    have ht2 : t ^ 2 = 1 := by
      change (QuotientGroup.mk' (pCore 2 D.H) x) ^ 2 = 1
      rw [←map_pow,hx2,map_one]
    have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht
    obtain ⟨he,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim σ t ho
    have hl : 2 ≤ (fixedCodim σ (zpowers t) : ENNReal) := by
      have hh : cubicRatio σ ≤ actionRatio σ (zpowers t) :=
        iInf_le_of_le (zpowers t) (iInf_le_of_le ⟨he,isCubic_of_isQuadratic hquad⟩ le_rfl)
      simpa only [hqσ,actionRatio,hr,Nat.cast_one,div_one] using hh
    have hl' : 2 ≤ fixedCodim σ (zpowers t) := by exact_mod_cast hl
    have hb := c.displacement_le_one_of_commutator_card_two A B hAH hAB hB.le x hx
    change Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) ≤ 1 at hb
    rw [← fixedCodim_zpowers_eq_displacement_rank] at hb
    omega
  rw [QuotientGroup.ker_mk'] at hker
  have hAQ : A ≤ D.QH := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hker ha,rfl⟩
  have hcomm : ⁅D.UH,A⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl hAQ).trans h.commutator_UH_QH_le_point
  have hcommg := map_mono (f := (MulAut.conj g).toMonoidHom) hcomm
  rw [map_commutator] at hcommg
  change ⁅i.conjugate D.UH,(D.UH.conjBy g⁻¹).conjBy g⁆ ≤ i.conjugate D.V₁ at hcommg
  rw [conjBy_inv'] at hcommg
  apply i.noncentral
  exact (commutator_mono le_rfl (show D.V ≤ D.UH by
    rw [hUV]; exact le_conjugateSpanBy _ _)).trans hcommg
/-- A critical conjugator leaves the original maximal point centralizer. -/
theorem source_rankTwo_critical_not_mem_Mc
    (J : Subgroup G) (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
    ∀ i : h.CriticalEndpoint, i.representative ∉ Mc := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
  change ∀ i : h.CriticalEndpoint, i.representative ∉ Mc
  intro i hi
  have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e J hJ.1 hJ.2).1
  have hJMc : J ≤ Mc := by
    have hm : Mc ∈ maximalTwoLocalOvergroups J := hHZ ▸ Set.mem_singleton _
    exact hm.2
  let W := conjugateSpanBy (localModule T M) Mc
  have hUW : D.UH ≤ W := conjugateSpanBy_mono le_rfl hJMc
  have hgW : i.conjugate D.UH ≤ W := by
    apply (map_mono (f := (MulAut.conj i.representative).toMonoidHom) hUW).trans
    exact (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy _ _ hi)).le
  let : IsMulCommutative W := hab
  have hc : ⁅i.conjugate D.UH,D.V⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hgW.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show D.V ≤ W from le_conjugateSpanBy _ _)))
  exact i.noncentral (hc ▸ bot_le)

/-- The original elementary-nine singleton has a reciprocal critical pair.
Cyclicity of its starred actors is discharged by the primitive source theorem. -/
theorem source_singleton_nine_critical_reciprocity
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    cubicRatio a.representation = 2 ∧
    (let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
     let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
     3 ≤ h.b ∧ Odd h.b ∧
      ∃ i : h.CriticalEndpoint,
        i.representative ∉ Mc ∧ ¬ i.conjugate D.UH ≤ D.QH ∧
        ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
          J ≤ normalizer (A : Set G) →
          (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A) := by
  obtain ⟨k,hk⟩ := Nat.card_eq_one_iff_exists.mp hone
  have hc := source_singleton_factor_star_cyclic hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone k
  have hq := source_ratio_singleton_nine_ratio_two hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd k hk hc hnine
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨hb,ho,⟨i⟩⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ.1
  have hn := source_rankTwo_critical_core_escape_of_ratio_two
    hG T hempty hM hu hmany hcard e hab J hJ.1 a hq i
  have hg := source_rankTwo_critical_not_mem_Mc
    hG T hempty hM hu hmany hcard e hab J hJ.1 i
  exact ⟨hq,hb,ho,i,hg,hn,i.reverse_labels hb hn⟩

end CFSG.Quasithin.Chapter14.Section06
