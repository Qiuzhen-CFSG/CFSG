module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.KernelSaturation
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# The exact kernel alternative in the original nonblock configuration

Apply the whole central-omega saturation theorem to the original maximum
elementary subgroup of the actual Sylow intersection. InitialFixed supplies
C_Q(K)=1 from the original configuration, chosen module, constrained fitting
hypothesis and full SL₃ quotient marking. No Hypothesis1223 is added.

Either the full action kernel vanishes, the offender lies in the component
and Ω₁(Z(Q)) equals the initial moved omega, or the surviving kernel forces
an offender of order q² and fixed codimension 2n. The original maximum
elementary image then has weight exactly dim(Ω₁(Z(Q))). This retains the
saturated branch and does not assert whole-center or upper-section models.
At field four the entire central omega now has order 64 or 4096. In the
surviving-kernel branch its actual invariant subspace and quotient are both
natural at one common full SL₃ marking. This is an exact self-extension;
no splitting or identification with the entire center is inferred.
All statements retain field four and the original quotient kernel.
Source: Aschbacher--Smith C.1.34 and original 4.3.8--10, printed
pp.136--137,616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.KernelSaturation
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- The actual source Sylow intersection has exact component containment and
central-omega exhaustion, or the precise surviving-kernel saturation case. -/
theorem source_exists_exact_or_saturated_offender :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let H := J ⧸ centralizer (E : Set J)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    let f := NoncoreOffenders.toInitial hm hn E (CentralSections.coreOmegaLayer_centralizer_le hm hn)
    ∃ A ∈ elementaryAbelianMaxSubgroups ((S c).subgroupOf J), ∃ X ≤ A.map q,
      IsMinimalBestOffender rho X ∧ IsQuadratic rho X ∧
      weight rho X = weight rho (A.map q) ∧ ⁅B,X⁆ = B ∧
      X ⊓ centralizer (B : Set H) = ⊥ ∧ Function.Injective (f.comp X.subtype) ∧
      X ≤ B ⊔ pCore 2 H ∧ X.map f ≤ centralOmegaComponent (K c) (c.I.pCoreIn 2) ∧
      (f.ker = ⊥ ∧ X ≤ B ∧
        Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c) =
          movedCoreOmega c ∨
       f.ker ≠ ⊥ ∧ rank X = 2*n ∧ fixedCodim rho X = 2*n ∧ Nat.card X = 2^(2*n) ∧
         weight rho (A.map q) = Module.finrank (ZMod 2) (Additive E)) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  simpa only [ms_commutator_eq,ms_initialMoved_eq] using
    ChapterC.LinearThreeMS.NonbinarySource.KernelSaturation.exists_exact_or_saturated_offender
      (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed ((S c).subgroupOf _)
      (comap_mono (c.core_sylow.le.trans inf_le_left))



include D hf e in
/-- In the original field-four nonblock configuration the whole central omega
has order 64 or 4096, with no extra ambient hypothesis or strict-offender premise. -/
theorem field_four_omega_card (hfour : Nat.card F = 4) :
    Nat.card (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
      (Q c)) = 64 ∨
    Nat.card (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
      (Q c)) = 4096 := by
  have hF4 : Nat.card F = 2^2 := by simpa using hfour
  let hm := msPair_of_quotient c D hf 2 (by decide) hF4 e
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf (by decide : 1 < 2) hF4 e).2.1
  have hz : center SL(3,F) ≠ ⊥ := by
    intro he
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he
    exact hh (by rw [hfour])
  obtain ⟨s,hs,hne⟩ := (center SL(3,F)).bot_or_exists_ne_one.resolve_left hz
  have hc := ChapterC.LinearThreeMS.NonbinarySource.KernelSaturation.omega_card_eq_of_scalar
    hm (by decide) hfixed e s hs hne
  norm_num only [ms_commutator_eq] at hc
  exact hc

/-- The original field-four action either has trivial comparison kernel or
has two natural sections at the same full SL₃ marking. The latter assertion
retains the entire central omega; it does not claim that the extension splits. -/
theorem field_four_exact_or_common_marking (hfour : Nat.card F = 4) :
    letI := ZMod.algebra F 2
    let hm := msPair_of_quotient c D hf 2 (by decide) (by simpa using hfour) e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm (by decide : 1 < 2)
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm (by decide : 1 < 2)
    let f := NoncoreOffenders.toInitial hm (by decide : 1 < 2) E
      (CentralSections.coreOmegaLayer_centralizer_le hm (by decide : 1 < 2))
    (f.ker = ⊥ ∧
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c) =
        movedCoreOmega c) ∨
    (f.ker ≠ ⊥ ∧ ∃ α : SL(3,F) ≃* SL(3,F),
      let σ := ((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp
        (α.toMonoidHom.comp (KernelOffenders.omegaCover hm (by decide : 1 < 2) e).toMonoidHom)
      ∃ I : Subrepresentation (rho.comp B.subtype),
        Nonempty (I.toRepresentation.Equiv σ) ∧ Nonempty (I.quotientRepresentation.Equiv σ)) := by
  let := ZMod.algebra F 2
  have hF4 : Nat.card F = 2^2 := by simpa using hfour
  let hm := msPair_of_quotient c D hf 2 (by decide) hF4 e
  let := CentralSections.coreOmegaLayer_normal hm (by decide : 1 < 2)
  let := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
  let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
  let f := NoncoreOffenders.toInitial hm (by decide : 1 < 2) E
    (CentralSections.coreOmegaLayer_centralizer_le hm (by decide : 1 < 2))
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf (by decide : 1 < 2) hF4 e).2.1
  by_cases hk : f.ker = ⊥
  · left
    refine ⟨hk,?_⟩
    simpa only [ms_commutator_eq,ms_initialMoved_eq] using
      SmallOmega.omega_eq_initial_of_kernel_bot hm (by decide) hfixed hk
  · right
    refine ⟨hk,?_⟩
    have hz : center SL(3,F) ≠ ⊥ := by
      intro he
      have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he
      exact hh (by rw [hfour])
    obtain ⟨s,hs,hne⟩ := (center SL(3,F)).bot_or_exists_ne_one.resolve_left hz
    obtain ⟨A,hA,X,hXA,hX,hquad,hw,hmove,hdisj,_⟩ :=
      ChapterC.LinearThreeMS.NonbinarySource.KernelSaturation.exists_exact_or_saturated_offender
        hm (by decide) hfixed ((S c).subgroupOf _)
        (comap_mono (c.core_sylow.le.trans inf_le_left))
    exact ChapterC.LinearThreeMS.NonbinarySource.KernelSaturation.kernel_nontrivial_common_marking
      hm (by decide) hfixed e s hs hne X hX hmove hdisj hk

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.KernelSaturation
