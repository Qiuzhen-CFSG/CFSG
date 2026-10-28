module
public import Theory.Representation.BinaryConjugationSection.NoTransvection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicCrossSource

/-!
# Five-core vanishing and the original local Fitting subgroup

On the same minimal five-core witness, the normal point cubic excludes
transvections on U_I/V₁. The crossed splitting gives [Cᵍ,U_I] = V₁ᵍ,
with Cᵍ contained in I and V₁ᵍ distinct from V₁. The order-two bound forces
this commutator into V₁, contradicting the two distinct point lines.
Thus the five-core vanishes. The earlier large-prime reduction then gives
F(I/O₂(I)) = O₃(I/O₂(I)) for every original member of H_z.

The solvable-local applications discharge the large-prime alternative,
retaining the actual normal two-perfect lifts and their full two-core
kernels. These three-core branches still require exclusion; the component
reductions and four-input assembly remain open.

Source: Aschbacher–Smith 14.7.6 and its use in 14.7.27–29, printed
pp.1044–1045 and 1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- Minimality recovers point normality on the specified original witness.
The four-dimensional support excludes transvections on any supplied literal
quotient-action coordinates for that same witness. -/
theorem local_minimal_five_action_no_transvections
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    ∀ t : HStar I, fixedCodim a.representation (zpowers t) ≠ 1 := by
  obtain ⟨I',X,Y,hI'I,hI',_,hXn,hXp,hcore,hcard,hminX,hYn,hYp,hYle,hYm,hYk,he,
      hout,hgen,hs,hn,hpoint,hm,hU',a',A,R,hAR,hA,hfaith,hR,hRE,hRc,hcub,hfixed,
      hcomm,hmove,hcompl,_⟩ :=
    local_minimal_five_point_normal h hab structural previous I hI hne
  have hXne : X ≠ ⊥ := by
    intro hz
    rcases hcard with hc | hc <;> rw [hz,card_bot] at hc <;> omega
  have heq : I' = I := by
    by_contra hh
    exact hXne (hcore.trans (hmin I' hI' (lt_of_le_of_ne hI'I hh)))
  subst I'
  have hdim : 2 < Module.finrank (ZMod 2)
      (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
    have hh := Submodule.finrank_le (subspaceCommutator a'.representation ⊤ ⁅X,R⁆)
    rw [hmove] at hh
    omega
  exact local_normal_point_no_transvections h structural I
    (F.Li_one_le_of_mem_Hz hI) hn a hdim

/-- The crossed opposite fixed factor excludes the remaining simultaneous
cubic case, so the five-core vanishes on every original local quotient. -/
theorem local_five_core_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    pCore 5 (HStar J) = ⊥ := by
  by_contra hne
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,houtc,hAc,hbase,hopp,hnep,hcentral,
      hcentralOpp,Y,hYn,hYp,hYm,hYk,he,hYout,hgen,hk,hIW,hIC,hsplit,hdis,
      hVW,hVWdis,hCc,hVC,hCV,hrad,hcross⟩ :=
    local_minimal_five_crossed_splitting h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
  let B := c.endpoint.conjugate C
  let Z' := c.endpoint.conjugate (F.Vi 1)
  have hb : 3 ≤ hf.b := (local_f9_critical_bounds h hab structural previous I hI).1
  have hBI : B ≤ I := (map_mono (show C ≤ F.UH I from inf_le_left)).trans
    ((map_mono (conjugateSpanBy_mono hf.plus_le le_rfl)).trans (c.endpoint.large_le hb))
  have hZcard : Nat.card Z' = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans
      (by simpa using F.card 1 (by decide))
  have hc : ⁅B,F.UH I⁆ = Z' := hcross.2.1
  have hno := local_minimal_five_action_no_transvections h hab structural previous
    I hI hneI hmin a
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  let b : BinaryConjugationSection I (F.UH I) (F.Vi 1)
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) := {
    section_le := s.le
    kernel_le := s.line_le
    normalized := s.normalizes
    coordinates := s.quotient
    onto := s.surjective
    kernel_eq := s.kernel
    equivariant := fun x v => (s.conjugates x v).symm }
  have hbn : ∀ x : I, fixedCodim
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) (zpowers x) ≠ 1 := by
    intro x
    rw [fixedCodim_zpowers_eq_displacement_rank]
    have hh := hno (QuotientGroup.mk' (pCore 2 I) x)
    rw [fixedCodim_zpowers_eq_displacement_rank] at hh
    exact hh
  have hZle : Z' ≤ F.Vi 1 := hc ▸
    b.commutator_le_kernel_of_card_two_of_no_transvections hbn B Z' hBI hZcard hc.le
  have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  exact hnep (eq_of_le_of_card_ge hZle (by rw [hZcard, hz])).symm

/-- Every prime core above three vanishes on each original local quotient. -/
theorem local_large_prime_cores_vanish
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (p : ℕ) (hp : p.Prime) (hgt : 3 < p) : pCore p (HStar J) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases he : p = 5
  · subst p
    exact local_five_core_eq_bot h hab structural previous faithful J hJ
  · exact local_largePrime_core_eq_bot h hab structural previous J hJ hgt he

/-- Source 14.7.6, with the literal Fitting subgroup and two-core quotient. -/
theorem local_fitting_eq_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    fittingSubgroup (HStar J) = pCore 3 (HStar J) := by
  apply le_antisymm _ (pCore_le_fitting (HStar J) 3)
  rw [fitting_eq_sup_pCore]
  apply iSup_le
  intro p
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.property
  by_cases hp2 : p.1.1 = 2
  · rw [hp2,pCore_quotient_pCore_eq_bot 2]
    exact bot_le
  by_cases hp3 : p.1.1 = 3
  · rw [hp3]
  rw [local_large_prime_cores_vanish h hab structural previous faithful J hJ p.1.1 hp
    (by have := hp.two_le; omega)]
  exact bot_le

/-- The Fitting subgroup in the exact source statement is a three-group. -/
theorem local_fitting_isThreeGroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    IsPGroup 3 (fittingSubgroup (HStar J)) := by
  rw [local_fitting_eq_threeCore h hab structural previous faithful J hJ]
  exact pCore_isPGroup

/-- The actual solvable-local consumer now has no large-prime branch.
Its two possible normal lifts retain their full two-core quotient kernel. -/
theorem local_solvable_threeCore_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) :=
  local_solvable_threeCore_models h hab structural J hJ hs
    (local_large_prime_cores_vanish h hab structural previous faithful J hJ)

/-- At the original point normalizer, the only remaining solvable branches
are the elementary-nine lift and a proper Heisenberg lift. This discharges
the large-prime alternative of `original_solvable_reduction`. -/
theorem original_solvable_threeCore_source
    (d : Chapter13.Section08.TransvectionRecognition.Component.ModelExtension.Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ (X : Subgroup (pCore 3 (HStar F.H))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup F.H),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 F.H ∧
      Y.map (starMap F) = X.map (pCore 3 (HStar F.H)).subtype ∧
      ((starMap F).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧ Y < pResidual 2 F.H)) := by
  apply (original_solvable_reduction d h hab structural previous faithful earlier hs).resolve_left
  rintro ⟨p,hp,hgt,hne⟩
  exact hne (local_large_prime_cores_vanish h hab structural previous faithful F.H
    (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) p hp hgt)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
