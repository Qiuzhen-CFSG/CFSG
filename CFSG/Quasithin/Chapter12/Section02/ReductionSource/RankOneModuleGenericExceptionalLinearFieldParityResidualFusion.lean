module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupResidualFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityBlockExclusion

/-!
# Parity outside the self-normalizing index-three residual case

Apply the central-seed fusion theorem to the original ChosenModule.
The literal point Ω₁Z(T) ∩ V has TI under N_G(C_K H), for every odd
field degree. If C_K H is normal in N_G(K), this supplies full residual
TI, and the existing global TI, F.8, Seed, degree-three displacement and
both terminal critical-pair branches give evenness of n.

The residual quotient's outer-order bound shows that [N_G(K) : C_K H]
divides three. Thus an odd degree can remain only when this index is
three and C_K H is self-normalizing inside N_G(K). The final theorem
retains precisely the independent F.1.12 Suzuki containment premise;
no TI, marking, abelianness or Seed callback is assumed.

The index-three case and final original parity theorem remain with
qt-d-1222-linear-field-parity, while qt-f112-linear-suzuki-containment
retains discharge of its independent recognition statement.
Source: Aschbacher–Smith 5.1.17, printed pp.640–642, used in 12.2.2,
printed p.795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The unchanged chosen point is TI under N_G(C_K H), in every odd degree. -/
theorem rankOne_odd_point_ti_under_kernel_overgroup_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    {g : G} (hg : g ∈ normalizer
      (((normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
        (normalizer (residual H : Set G)).subtype ⊔ H : Subgroup G) : Set G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ V
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_point_ti_under_kernel_overgroup_normalizer hi hH hm hnf hlinear hsolv F hodd hnat hg

/-- Relative normality of C_K H now suffices for the complete parity assembly;
all point TI, F.8 and Seed clauses are discharged. -/
theorem rankOne_even_exponent_of_kernel_overgroup_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgen : 1 < ChapterE.generationParameter H)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hnormal : (((normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype ⊔ H).subgroupOf
        (normalizer (residual H : Set G))).Normal) : Even n := by
  have hJN : (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype ⊔ H ≤ normalizer (residual H : Set G) :=
    sup_le (map_subtype_le _) (le_normalizer_residual H)
  have hN := (normal_subgroupOf_iff_le_normalizer hJN).mp hnormal
  apply D.rankOne_even_exponent_of_solvable_and_residual_ti h hmany hn hpsl hH hlinear hgen hsolv
  intro A B c ho g hg
  exact D.rankOne_odd_point_ti_under_kernel_overgroup_normalizer
    h hmany hn hpsl hH hlinear ho hsolv (hN hg)

/-- The sole residual-normalizer fusion case left by the normalizer argument
is a self-normalizing C_K H of index three. No TI or Seed callback is assumed. -/
theorem rankOne_even_or_kernel_overgroup_index_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgen : 1 < ChapterE.generationParameter H)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    let J := C ⊔ H
    Even n ∨ (J.relIndex N = 3 ∧ N ⊓ normalizer (J : Set G) = J) := by
  let N := normalizer (residual H : Set G)
  let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
  let J := C ⊔ H
  have hJN : J ≤ N := sup_le (map_subtype_le _) (le_normalizer_residual H)
  by_cases he : Even n
  · exact Or.inl he
  right
  have hnot : ¬ N ≤ normalizer (J : Set G) := by
    intro hh
    exact he (D.rankOne_even_exponent_of_kernel_overgroup_normal h hmany hn hpsl hH hlinear
      hgen hsolv ((normal_subgroupOf_iff_le_normalizer hJN).mpr hh))
  have hd : J.relIndex N ∣ 3 := residual_kernel_overgroup_index_dvd_three hH.1.1.2 hlinear
  have hidx : J.relIndex N = 3 := (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left (by
    intro h1
    exact hnot ((relIndex_eq_one.mp h1).trans J.le_normalizer))
  refine ⟨hidx,?_⟩
  let R := N ⊓ normalizer (J : Set G)
  have hJR : J ≤ R := le_inf hJN J.le_normalizer
  have hmul := relIndex_mul_relIndex J R N hJR inf_le_left
  rw [hidx] at hmul
  have hp : (J.relIndex R * R.relIndex N).Prime := hmul ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hRN⟩ | ⟨_,hJR1⟩
  · exact (hnot ((relIndex_eq_one.mp hRN).trans inf_le_right)).elim
  · exact le_antisymm (relIndex_eq_one.mp hJR1) hJR

/-- Preserve the precise independent Suzuki recognition input while reducing
all remaining parity geometry to the actual index-three case. -/
theorem rankOne_even_or_kernel_overgroup_index_three_of_suzuki_containment
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgen : 1 < ChapterE.generationParameter H)
    (hrec : ∀ R : Subgroup G,
      HypothesisF11 ![L,R] (T : Subgroup G) →
      IsQuasithin (generated ![L,R] (T : Subgroup G)) →
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal →
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ≤ R) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    let J := C ⊔ H
    Even n ∨ (J.relIndex N = 3 ∧ N ⊓ normalizer (J : Set G) = J) := by
  rcases Nat.even_or_odd n with he | ho
  · exact Or.inl he
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h.toHypothesis1221 hn hpsl hH hgen
  have hs := D.rankOne_odd_quotientCentralizerKernel_solvable_of_suzuki_containment
    h hmany hn hpsl hH hlinear c ho hrec
  exact D.rankOne_even_or_kernel_overgroup_index_three h hmany hn hpsl hH hlinear hgen hs
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
