module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscape

/-!
# The actual quadratic actor after the three-prime reduction

Reduce an original local to J = ⟨Kᵀ⟩L₁T using component escape. The
same Suzuki component keeps its intrinsic two-core quotient. Its orbit
image is normal, three-free, and supplements the point-parabolic image.
The normal point cubic retains order three, full movement, and commutation
with that entire orbit. The existing source edge then constructs a
faithful quadratic actor on the literal U_J/V₁ section. The theorem records
the exact orbit identity, so faithfulness is used on the whole orbit.

Source: Aschbacher–Smith, 14.7.7, printed p.1045, using 14.5.18–19,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem three_free_of_twoCore_image {D : Type*} [Group D] [Finite D]
    (N : Subgroup D) (hN : N.map (QuotientGroup.mk' (pCore 2 D)) ≤ pPrimeCore 3 (D ⧸ pCore 2 D)) :
    Nat.Coprime 3 (Nat.card N) := by
  let f := (QuotientGroup.mk' (pCore 2 D)).comp N.subtype
  have hp : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hq : Nat.Coprime 3 (Nat.card f.range) := by
    rw [MonoidHom.range_comp,range_subtype]
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le hN)
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hn]
  exact hq.mul_right ((by decide : Nat.Coprime 3 2).pow_right n)

/-- The source reduction of a nonzero three-prime core produces the actual
Suzuki component, its Sylow orbit and a quadratic actor on the literal reduced
local section. The normal point cubic retains full movement and commutes with
the whole orbit image. No natural-module recognition is assumed. -/
theorem local_threePrime_reduced_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).Normal)
    (hne : pPrimeCore 3 (HStar I) ≠ ⊥) :
    ∃ (K : Subgroup I) (m : ℕ), K.IsCComponent ∧ 1 ≤ m ∧
      K.map (QuotientGroup.mk' (pCore 2 I)) ≤ pPrimeCore 3 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp K.subtype).ker = pCore 2 K ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
      let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
      let KJ := (K.map I.subtype).subgroupOf J
      let X := (N.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
      let Z := ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
      J ≤ I ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧ KJ.IsCComponent ∧
      Nonempty ((KJ ⧸ pCore 2 KJ) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp KJ.subtype).ker = pCore 2 KJ ∧
      X = conjugateSpanBy (KJ.map (QuotientGroup.mk' (pCore 2 J)))
        (((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) ∧
      X.Normal ∧ Nat.Coprime 3 (Nat.card X) ∧
      X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map
        (QuotientGroup.mk' (pCore 2 J)) = ⊤ ∧
      ((F.Li L 1).subgroupOf J).Normal ∧ Z.Normal ∧ Nat.card Z = 3 ∧
      X ≤ centralizer (Z : Set (HStar J)) ∧ ⁅F.UH J,F.Li L 1⁆ = F.UH J ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH J),
        let := hU
        ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
          fixedSpace a.representation Z = ⊥ ∧ quadraticRatio a.representation ≤ 2 ∧
          ∃ A : Subgroup J,
            A ≤ (F.Ri L 1).subgroupOf J ∧
            IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 J))) ∧
            IsQuadratic a.representation (A.map (QuotientGroup.mk' (pCore 2 J))) ∧
            fixedCodim a.representation (A.map (QuotientGroup.mk' (pCore 2 J))) ≤
              2 * rank (A.map (QuotientGroup.mk' (pCore 2 J))) ∧
            A.map (QuotientGroup.mk' (pCore 2 J)) ⊓ centralizer (X : Set (HStar J)) = ⊥ := by
  obtain ⟨K,hK,hK3,hker,m,hm,⟨eK⟩⟩ :=
    local_threePrime_component h hab structural previous faithful I hI hne
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let X := (N.subgroupOf J).map q
  let Z := ((F.Li L 1).subgroupOf J).map q
  obtain ⟨hNI,hJI,hJ⟩ := local_component_reduced_mem_Hz h structural I hI K hK
  have hNJ : N ≤ J := le_sup_left
  have hKI : ((K.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hK
  have hKJle : K.map I.subtype ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hKJ : KJ.IsCComponent := hKI.subgroupOf_of_le hKJle hJI
  let e : KJ ≃* K := (subgroupOfEquivOfLe hKJle).trans
    (equivMapOfInjective K I.subtype I.subtype_injective).symm
  have hNJn : (N.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNJ).mpr
      (hJI.trans ((normal_subgroupOf_iff_le_normalizer (hNJ.trans hJI)).mp hNI))
  let : X.Normal := hNJn.map q (QuotientGroup.mk'_surjective _)
  have horbit : X = conjugateSpanBy (KJ.map q) (((T : Subgroup G).subgroupOf J).map q) := by
    rw [←map_conjugateSpanBy]
    apply congrArg (map q)
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hNJ,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hKJle,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)]
  have hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map q = ⊤ := by
    rw [←Subgroup.map_sup,←subgroupOf_sup hNJ (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right)]
    change (J.subgroupOf J).map q = ⊤
    rw [subgroupOf_self,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I :=
    sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  have hLI : F.Li L 1 ≤ I := F.Li_one_le_of_mem_Hz hI
  have hLJ : F.Li L 1 ≤ J := F.Li_one_le_of_mem_Hz hJ
  have hnI := local_point_normal_of_star_normal h structural I hBI hn
  have hnJ : ((F.Li L 1).subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLJ).mpr
      (hJI.trans ((normal_subgroupOf_iff_le_normalizer hLI).mp hnI))
  let : Z.Normal := hnJ.map q (QuotientGroup.mk'_surjective _)
  have hcZ : Nat.card Z = 3 := local_point_star_card_of_normal h structural J hLJ hnJ
  have hcN : Nat.Coprime 3 (Nat.card N) := by
    let N₀ := conjugateSpanBy K ((T : Subgroup G).subgroupOf I)
    have heN : N₀.map I.subtype = N := by
      rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
    have hN₀ : N₀.map (QuotientGroup.mk' (pCore 2 I)) ≤ pPrimeCore 3 (HStar I) := by
      rw [map_conjugateSpanBy]
      exact conjugateSpanBy_le hK3 le_normalizer_of_normal
    rw [←heN,card_map_of_injective I.subtype_injective]
    exact three_free_of_twoCore_image N₀ hN₀
  have hcX : Nat.Coprime 3 (Nat.card X) := by
    apply Nat.Coprime.of_dvd_right (card_map_dvd (N.subgroupOf J) q)
    rw [Nat.card_congr (subgroupOfEquivOfLe hNJ).toEquiv]
    exact hcN
  have hcXZ : X ≤ centralizer (Z : Set (HStar J)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply (commutator_le_inf (H₁ := X) (H₂ := Z)).trans
    apply (disjoint_of_coprime_natCard (show Nat.Coprime (Nat.card X) (Nat.card Z) from ?_)).eq_bot.le
    rw [hcZ]
    exact hcX.symm
  have hmoved : ⁅F.UH J,F.Li L 1⁆ = F.UH J :=
    (conjugateSpanBy_eq_commutator_of_seed V J (F.Li L 1) (F.Li L 1)
      hLJ ((normal_subgroupOf_iff_le_normalizer hLJ).mp hnJ) le_rfl
      (seed_commutator h F)).symm
  refine ⟨K,m,hK,hm,hK3,hker,⟨eK⟩,hJI,hJ,hKJ,
    ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eK⟩,?_,
    horbit,inferInstance,hcX,hgen,hnJ,inferInstance,hcZ,hcXZ,hmoved,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hKJ.subnormal).symm
  · obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod,hfaith⟩ :=
      local_prime_supplement_quadratic_actor h hab structural previous J hJ X hgen
    let := hU
    exact ⟨hU,a,local_point_fixedSpace_eq_bot h structural J hLJ hnJ a,hq,A,
      hAR,hA,hquad,hcod,hfaith⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
