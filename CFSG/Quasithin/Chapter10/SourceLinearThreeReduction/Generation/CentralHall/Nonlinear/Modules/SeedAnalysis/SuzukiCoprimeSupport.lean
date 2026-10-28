module
public import Theory.Representation.Suzuki.CoprimeFieldDegree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiLinearThreeSupport

/-!
# Coprime fields in the remaining original Suzuki support

The exact quotient-action kernel has order prime to every odd prime of the
original Suzuki component. The Suzuki split factor and the SL₃ cubic
order factor therefore make the Suzuki degree coprime to three times the natural
support field degree. In particular Suzuki degrees divisible by three are
excluded. A primitive divisor then forces every faithful Suzuki action over
that field, or any binary field whose degree divides the constituent degree,
to have field dimension at least four times the Suzuki degree.

The final application retains the literal Hall subgroup, full starred actor,
component orbit, both original kernels, natural constituent and all previous
bounds. Constructing a small faithful multiplicity action in these fields,
and excluding the nonseparated even-linear seed, are still necessary for the
unconditional source contract.

Source: Aschbacher--Smith D.3.9,10.1.1--2 and10.2.3, printed
pp.200--201,741--742,745 of refs/quasithin.pdf. The primitive-divisor argument
uses the checked Suzuki order and binary degree theorems.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open ChapterB.QuasisimpleSource
universe u
variable {Γ : Type u} [Group Γ] [Finite Γ] {T : Sylow 2 Γ} {L : Subgroup Γ}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance coprimeSupportElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup Γ) :=
  source_original_full_moved_elementary D
local instance coprimeSupportFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)) := Module.Finite.of_finite

/-- The original kernel excludes every common factor of the Suzuki degree
and the full binary degree of a natural SL₃ support constituent. -/
theorem original_suzuki_linearThree_support_field_coprime
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (F : BinaryField) (j : J ≃* SL(3,F.Carrier)) :
    Nat.Coprime (2*m+1) (3*F.degree) := by
  apply Suzuki.field_degree_coprime_of_disjoint_linearThree_primes F.Carrier hm F.card_eq
  intro p hp hp2 hpK hpJ
  let : Fact p.Prime := ⟨hp⟩
  have hpc : Nat.Coprime p (Nat.card J) :=
    (original_suzuki_quotient_kernel_coprime D c m hm e p hp2
      (by simpa only [Nat.card_congr e.toEquiv] using hpK)).of_dvd_right (card_dvd_of_le hJc)
  exact hp.coprime_iff_not_dvd.mp hpc (by simpa only [Nat.card_congr j.toEquiv] using hpJ)

/-- In particular no natural SL₃ support survives when the original Suzuki
field degree is divisible by three, including the first Suzuki group. -/
theorem original_suzuki_no_linearThree_support_of_three_dvd
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (F : BinaryField) (j : J ≃* SL(3,F.Carrier)) (hthree : 3 ∣ 2*m+1) : False := by
  have hc := original_suzuki_linearThree_support_field_coprime D c m hm e J hJc F j
  have hh : Nat.Coprime 3 3 := hc.of_dvd_left hthree |>.of_dvd_right (dvd_mul_right 3 F.degree)
  norm_num at hh

/-- Every candidate scalar field whose degree divides the natural constituent
has the full Suzuki degree obstruction. This applies in particular to its
Schur field, without identifying that field with the natural field. -/
theorem original_suzuki_no_small_support_scalar_action
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (F : BinaryField) (ho : Odd F.degree) (j : J ≃* SL(3,F.Carrier))
    (E : BinaryField) (hE : E.degree ∣ 3*F.degree)
    (r : ℕ) (hr : r < 4*(2*m+1))
    (f : (L ⧸ pCore 2 L) →* Matrix.GeneralLinearGroup (Fin r) E.Carrier) :
    ¬ Function.Injective f := by
  have hc := (original_suzuki_linearThree_support_field_coprime D c m hm e J hJc F j).of_dvd_right hE
  have hodd : Odd E.degree := Odd.of_dvd_nat ((by decide : Odd 3).mul ho) hE
  intro hf
  exact Suzuki.no_small_linear_action_of_coprime_field_degree E.Carrier hm E.card_eq hodd hc hr
    (f.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)

/-- The literal Hall exponent is proved for every Suzuki field degree
divisible by three. All constituent, support and kernel premises are
constructed from the original context. -/
theorem hall_exponent_of_suzuki_three_dvd_degree
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hthree : 3 ∣ 2*m+1) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1 := by
  have hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
    rintro ⟨j⟩
    apply BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm
    rw [←Nat.card_congr e.toEquiv,Nat.card_congr j.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    norm_num
  rcases hall_exponent_or_suzuki_centralizing_component_support D c hnot m hm e with hh | hs
  · exact hh
  · obtain ⟨hcentral,A,J,hA,hJ,_hJthree,hJc,_hXc,hXn,hXA⟩ := hs
    obtain ⟨F,_ho,_R,_hJR,_hAR,⟨a⟩⟩ := original_suzuki_support_natural_linearThree D c m hm e
      A J hA (hcentral A hA) hJ hJc hXn hXA
    exact (original_suzuki_no_linearThree_support_of_three_dvd D c m hm e J hJc F
      a.groupEquiv hthree).elim

/-- The original natural support together with the field obstruction for all
its literal support markings. Keeping the restriction universal preserves
its applicability to the same constituent and actor selected earlier. -/
@[expose] def OriginalSuzukiCoprimeLinearThreeSupport
    (hn : ¬ (T : Subgroup Γ) ≤ normalizer (L : Set Γ)) : Prop :=
  OriginalSuzukiNaturalLinearThreeSupport D hn ∧
  ∀ (m : ℕ), 0 < m →
    (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m →
    ∀ J : Subgroup (actionImage (movedStabilizerAction D)),
      J ≤ (originalMovedQuotientAction D hn).ker →
      ∀ F : BinaryField, Odd F.degree → J ≃* SL(3,F.Carrier) →
        Nat.Coprime (2*m+1) (3*F.degree) ∧
        ∀ E : BinaryField, E.degree ∣ 3*F.degree →
          ∀ r : ℕ, r < 4*(2*m+1) →
            ∀ f : (L ⧸ pCore 2 L) →* Matrix.GeneralLinearGroup (Fin r) E.Carrier,
              ¬ Function.Injective f

/-- The strengthened residual alternatives for the literal Hall subgroup.
No coprimality, constituent or scalar-action premise is added to its context. -/
theorem original_hall_conclusion_or_coprime_linearThree_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨ OriginalSuzukiCoprimeLinearThreeSupport D c.nonnormal := by
  rcases original_hall_conclusion_or_natural_linearThree_support D c with hh | he | hs
  · exact Or.inl hh
  · exact Or.inr (Or.inl he)
  · refine Or.inr (Or.inr ⟨hs,?_⟩)
    intro m hm e J hJc F ho j
    exact ⟨original_suzuki_linearThree_support_field_coprime D c m hm e J hJc F j,
      original_suzuki_no_small_support_scalar_action D c m hm e J hJc F ho j⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
