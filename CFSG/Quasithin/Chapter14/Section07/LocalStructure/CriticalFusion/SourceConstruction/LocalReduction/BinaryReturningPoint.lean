module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryCorePair
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.EarlierWeakClosure.Geometry
public import Theory.GroupAction.KleinFourReturningPoint

/-!
# Returning points in the original exchanged reciprocal plane

The actual Y₀ action is transitive on the three points of
P = V₁ ∨ Zα. For any V₁ᵍ ≤ P, an element of Y₀ has the same effect on
V₁. Their difference lies in H = N_G(V₁), which normalizes U. Thus the
whole returning Uᵍ is a Y₀-conjugate of U, contains P, and lies in
C_{Y₀}(P) = O₂(Y₀). This retains an actual conjugator and both original
subgroups, without any later source Data.

Every overgroup of Y₀ in N_G(P) still induces the full plane action,
so P is reduced there. The final theorem applies the proved second
clause of 14.7.31 with these two premises discharged and constructs its
S₃ quotient from the literal action. The flag-plane centralizer bound,
the choice of Y and its relative Sylow, and C_Y(P) = O₂(Y) remain
explicit source obligations for the subsequent construction of T_Y.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058, and
14.7.31(2), printed p.1055, refs/quasithin.pdf. The later weak-closure
contradiction and the remaining classification through 14.7.52 are not
asserted by this conditional application.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every returning point in the original reciprocal plane carries its
whole U-conjugate into O₂(Y₀); the plane is reduced in every normalizing
overgroup containing Y₀, with its full conjugation action retained. -/
theorem local_nonnormal_component_returning_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧
      P ≤ F.U ⊓ c.Uα ∧
      Y₀ ≤ normalizer (P : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (Y₀ : Set G) ∧
      Y₀.pCoreIn 2 = Y₀ ⊓ centralizer (P : Set G) ∧
      (∀ g : G, conjugate (F.Vi 1) g ≤ P →
        ∃ y ∈ Y₀, conjugate F.U g = conjugate F.U y ∧
          P ≤ conjugate F.U g ∧ conjugate F.U g ≤ Y₀.pCoreIn 2) ∧
      (∀ Y : Subgroup G, Y₀ ≤ Y → Y ≤ normalizer (P : Set G) →
        IsPReduced 2 (P.subgroupOf Y) ∧
        ∃ σ : Y →* MulAut P, Function.Surjective σ ∧
          ∀ (y : Y) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹) := by
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,hprod,hbound,
      σ,hσ,hker,hconj,he⟩ :=
    local_nonnormal_component_core_pair_action d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let P := F.Vi 1 ⊔ c.Zα
  let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : IsElementaryAbelian 2 P := hE
  have hcardP : Nat.card P = 4 := hfour
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr (by intro hz; simp [hz] at hcardP)
  let : IsKleinFour P := ⟨hfour,IsElementaryAbelian.exponent_eq_prime⟩
  have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 F.U) F.U_le_H (le_normalizer_conjugateSpanBy V F.H)
  have hUY : F.U ≤ Y₀ := hUQ.trans le_sup_left
  have hPU : P ≤ F.U := hplane.trans inf_le_left
  refine ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,?_,?_⟩
  · intro g hg
    obtain ⟨y,hy,he,hret⟩ := full_four_action_returning Y₀ P (F.Vi 1) F.U
      (by simpa using F.card 1 (by decide)) le_sup_left hPU hUY hYn
      (le_normalizer_conjugateSpanBy V F.H) σ hσ hconj g⁻¹ hg
    have he' : conjugate F.U g = conjugate F.U y⁻¹ := by
      simpa only [conjugate,inv_inv] using he
    refine ⟨y⁻¹,Y₀.inv_mem hy,he',?_,hret.trans_eq hkernel.symm⟩
    rw [he']
    have hp : conjugate P y⁻¹ = P :=
      (conjugate_eq_iff _ _).mpr (hYn (Y₀.inv_mem hy))
    exact hp.symm.le.trans (map_mono (f := (MulAut.conj (y⁻¹)⁻¹).toMonoidHom) hPU)
  · intro Y hY hN
    let τ := P.normalizerMonoidHom.comp (inclusion hN)
    have hτ : Function.Surjective τ :=
      full_conjugation_surjective_overgroup Y₀ Y P hY hN σ hσ hconj
    have hτconj : ∀ (y : Y) (v : P), (τ y v : G) = (y : G) * v * (y : G)⁻¹ :=
      fun _ _ => rfl
    exact ⟨full_four_action_reduced Y P (hPU.trans (hUY.trans hY)) hN τ hτ hτconj,
      τ,hτ,hτconj⟩

/-- Actual application of 14.7.31(2): full-action reducedness, the S₃
quotient, and the returning-point premise are discharged for the original
selected plane. The source plane bound and construction of Y,T_Y remain. -/
theorem local_nonnormal_component_weakClosure_of_plane_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧
      P ≤ F.U ⊓ c.Uα ∧
      ∀ (Y R : Subgroup G), Y₀ ≤ Y → Y ≤ normalizer (P : Set G) →
        Chapter1.IsSylowIn 2 R Y →
        Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 →
        centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) →
        ChapterE.indexedWeakClosure V R 0 ≤ Y ∧
          Y ≤ normalizer (ChapterE.indexedWeakClosure V R 0 : Set G) := by
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,hreturn,hact⟩ :=
    local_nonnormal_component_returning_point d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let P := F.Vi 1 ⊔ c.Zα
  let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
  let : IsElementaryAbelian 2 P := hE
  have hcardP : Nat.card P = 4 := hfour
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr (by intro hz; simp [hz] at hcardP)
  let : IsKleinFour P := ⟨hfour,IsElementaryAbelian.exponent_eq_prime⟩
  refine ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,?_⟩
  intro Y R hY hN hSylow hcore hcentral
  obtain ⟨hred,σ,hσ,hconj⟩ := hact Y hY hN
  obtain ⟨e⟩ := full_four_action_core_quotient Y P σ hσ hconj hcore
  have hPY : P ≤ Y := by
    let := h.chosen.elementary
    let := hab
    let := elementary_U F
    have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
      (IsElementaryAbelian.isPGroup 2 F.U) F.U_le_H (le_normalizer_conjugateSpanBy V F.H)
    exact (hplane.trans inf_le_left).trans (hUQ.trans (le_sup_left.trans hY))
  apply EarlierWeakClosure.clause_two h structural F hcentral Y R P hSylow hPY hred e hcore
  intro g hg
  obtain ⟨y,hy,he,hP,hret⟩ := hreturn g hg
  exact hret.trans (hkernel.le.trans (inf_le_inf_right _ hY))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
