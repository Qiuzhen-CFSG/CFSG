module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalLifts

/-!
# Original-source applications of the classical residual data

Both literal parabolic residuals lie in the original K, are nonshort,
have characteristic-two generalized Fitting structure and PSL₂(2ⁿ)
core quotients, and generate K. These facts are proved for every eligible
member of the original local family and applied to both original primes
and the later exchanged source, with the original model marking retained.

Source: Aschbacher--Smith 15.1.20(2), printed p.1095. The remaining
classical exclusion requires choosing a compatible Sylow/parabolic marking
and proving local-family membership of these residuals. The general
nonblock placement theorem is already proved in LocalSeparation; once
membership is established it applies to this data. General Borel placement
and the remaining catalogue clauses stay with this task. Original 15.1.14
remains with its existing producer and the pre-exclusion assembly owner.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Intrinsic data for the two literal parabolic residuals. Local-family
membership is separate: it requires a compatible Sylow/parabolic marking. -/
structure ClassicalResidualPair (d : CaseIComponentData T M Mc V) (K : Subgroup G)
    (P Q : Subgroup (d.normalizerImage K)) (q : ℕ) : Prop where
  contained : ∀ R ∈ ({P,Q} : Set (Subgroup (d.normalizerImage K))),
    d.normalizerParabolicResidual K R ≤ K
  not_short : ∀ R ∈ ({P,Q} : Set (Subgroup (d.normalizerImage K))),
    ¬ ChapterC.IsShort (d.normalizerParabolicResidual K R)
  fitting : ∀ R ∈ ({P,Q} : Set (Subgroup (d.normalizerImage K))),
    generalizedFitting (d.normalizerParabolicResidual K R) =
      pCore 2 (d.normalizerParabolicResidual K R)
  quotient : ∀ R ∈ ({P,Q} : Set (Subgroup (d.normalizerImage K))),
    ClassicalGroup.IsPSL (d.normalizerParabolicResidual K R ⧸
      pCore 2 (d.normalizerParabolicResidual K R)) 2 q
  generated : d.normalizerParabolicResidual K P ⊔ d.normalizerParabolicResidual K Q = K

/-- The actual linear-three pair, on every original model marking. -/
theorem NormalizerAction.linear_three_residual_pair
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} [Group.IsPerfect K]
    (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : d.normalizerImage K ≃* SL(3,F)) :
    d.ClassicalResidualPair K
      ((Matrix.PSL3.LinearThree.pointParabolicSL F).map e.symm.toMonoidHom)
      ((Matrix.PSL3.LinearThree.lineParabolicSL F).map e.symm.toMonoidHom) (2^n) := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  have hs := a.linear_three_residuals_not_short e hfour
  have hd := a.linear_three_residual_data hG h hK hq hfour e
  have hpoint := hd (Matrix.PSL3.LinearThree.pointParabolicSL F) (Or.inl rfl)
  have hline := hd (Matrix.PSL3.LinearThree.lineParabolicSL F) (Or.inr rfl)
  refine ⟨fun R _ => d.normalizerParabolicResidual_le K R,?_,?_,?_,
    a.linear_three_residuals_generate hq e hF hn⟩
  · intro R hR
    rcases hR with rfl | hR
    · exact hs.1
    · have he : R = _ := hR
      subst R
      exact hs.2
  · intro R hR
    rcases hR with rfl | hR
    · exact hpoint.1
    · have he : R = _ := hR
      subst R
      exact hline.1
  · intro R hR
    have heq : Nonempty ((d.normalizerParabolicResidual K R ⧸
        pCore 2 (d.normalizerParabolicResidual K R)) ≃* SL(2,F)) := by
      rcases hR with rfl | hR
      · exact hpoint.2
      · have he : R = _ := hR
        subst R
        exact hline.2
    obtain ⟨j⟩ := heq
    exact ⟨F,inferInstance,inferInstance,hF,⟨j.trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩

/-- The actual symplectic-four pair, on every original model marking. -/
theorem NormalizerAction.symplectic_four_residual_pair
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} [Group.IsPerfect K]
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : d.normalizerImage K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    d.ClassicalResidualPair K
      (Theory.SpecificGroups.SymplecticFour.pointParabolic.map e.symm.toMonoidHom)
      (Theory.SpecificGroups.SymplecticFour.planeParabolic.map e.symm.toMonoidHom) (2^n) := by
  have hs := a.symplectic_four_residuals_not_short e hF hn
  have hd := a.symplectic_four_residual_data hq hF hn e
  have hpoint := hd Theory.SpecificGroups.SymplecticFour.pointParabolic (Or.inl rfl)
  have hline := hd Theory.SpecificGroups.SymplecticFour.planeParabolic (Or.inr rfl)
  refine ⟨fun R _ => d.normalizerParabolicResidual_le K R,?_,?_,?_,
    a.symplectic_four_residuals_generate hq e hF hn⟩
  · intro R hR
    rcases hR with rfl | hR
    · exact hs.1
    · have he : R = _ := hR
      subst R
      exact hs.2
  · intro R hR
    rcases hR with rfl | hR
    · exact hpoint.1
    · have he : R = _ := hR
      subst R
      exact hline.1
  · intro R hR
    have heq : Nonempty ((d.normalizerParabolicResidual K R ⧸
        pCore 2 (d.normalizerParabolicResidual K R)) ≃* SL(2,F)) := by
      rcases hR with rfl | hR
      · exact hpoint.2
      · have he : R = _ := hR
        subst R
        exact hline.2
    obtain ⟨j⟩ := heq
    exact ⟨F,inferInstance,inferInstance,hF,⟨j.trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩

/-- Both classical pairs, preserving their literal preimage constructions. -/
@[expose] def ClassicalResidualData (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Prop :=
  (∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* SL(3,F)) (n : ℕ), Nat.card F = 2^n → 1 < n →
      d.ClassicalResidualPair K
        ((Matrix.PSL3.LinearThree.pointParabolicSL F).map e.symm.toMonoidHom)
        ((Matrix.PSL3.LinearThree.lineParabolicSL F).map e.symm.toMonoidHom) (2^n)) ∧
  (∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (n : ℕ), Nat.card F = 2^n → 1 < n → d.ClassicalResidualPair K
      (Theory.SpecificGroups.SymplecticFour.pointParabolic.map e.symm.toMonoidHom)
      (Theory.SpecificGroups.SymplecticFour.planeParabolic.map e.symm.toMonoidHom) (2^n))

/-- Every constrained escaping member has these actual residuals. No ambient
componenthood or S-normality of K is added to the original local family. -/
theorem localFamily_classical_residual_data (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) : d.ClassicalResidualData K := by
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  exact ⟨fun _ _ _ _ e _ hF hn => a.linear_three_residual_pair hG h hK.1 hq hF hn e,
    fun _ _ _ _ e _ hF hn => a.symplectic_four_residual_pair hq hF hn e⟩

/-- The original selected component retains either original pre-exclusion prime. -/
theorem PreExclusionSource.constrained_classical_residual_data
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ClassicalResidualData d.L :=
  d.localFamily_classical_residual_data hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

/-- The later exchanged source retains the same original maps on both plane sizes. -/
theorem ExchangedSource.constrained_classical_residual_data
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ClassicalResidualData d.L :=
  d.localFamily_classical_residual_data hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Actual original-marker application, preserving Z₁, row and prime.
Original 15.1.14 remains explicit for the pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_classical_residual_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L → d.ClassicalResidualData d.L) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf =>
    s.constrained_classical_residual_data (h := h) hG hempty hM hJ hu hf⟩
end CFSG.Quasithin.Chapter15.Section01
