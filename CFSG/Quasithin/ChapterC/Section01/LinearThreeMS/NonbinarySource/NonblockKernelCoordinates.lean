module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.KernelCoordinates
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# The whole comparison kernel in the original nonblock configuration

Use the genuine MS-pair supplied by the original chosen module and
constrained configuration. Its proved fixed-factor exclusion supplies
C_Q(K)=1. The intrinsic flag calculation then embeds the entire kernel
of the central-omega comparison in the additive coefficient field whenever
the original full SL₃ quotient has a nontrivial scalar.

At field four the quotient itself supplies that scalar, so the actual
kernel is elementary of order 1, 2 or 4. The original quotient map and all
kernel elements remain present. No Hypothesis1223, complement or
whole-center model is added. Recognition of the whole core and common
upper/Frattini markings remains with the C.1.34 source assembly.
Source: Aschbacher–Smith C.1.34 and original 4.3.8–10, printed
pp.136–137,616–617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.KernelCoordinates
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- A nontrivial scalar in the original full quotient bounds the entire
comparison kernel by one additive copy of the original coefficient field. -/
theorem source_kernel_embeds_field (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hne : s ≠ 1) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    let f := NoncoreOffenders.toInitial hm hn E
      (CentralSections.coreOmegaLayer_centralizer_le hm hn)
    ∃ a : f.ker →* Multiplicative F, Function.Injective a := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  let := CentralSections.coreOmegaLayer_normal hm hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.KernelCoordinates.kernel_embeds_field_of_scalar
    hm hn hfixed e s hs hne

/-- The original field-four nonblock configuration has an elementary comparison
kernel of order one, two or four, with no added ambient or splitting premise. -/
theorem source_field_four_kernel (hfour : Nat.card F = 4) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    let f := NoncoreOffenders.toInitial hm hn E
      (CentralSections.coreOmegaLayer_centralizer_le hm hn)
    IsElementaryAbelian 2 f.ker ∧
      (Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 ∨ Nat.card f.ker = 4) := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  let := CentralSections.coreOmegaLayer_normal hm hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.KernelCoordinates.kernel_elementary_field_four
    hm hn hfixed e hfour

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.KernelCoordinates
