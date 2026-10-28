module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.LocalSetup
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Global
public import Theory.GroupTheory.FrattiniConjugatorAdjustment

/-!
# The normal-residual section centralizer in 12.1.1

When the point residual is normal in its ambient point centralizer, the
proved Sylow promotion and A.4.2 identify the original Q = O₂(LT) as a
Sylow subgroup of Y = C_{G_w}(L_w/O₂(L_w)). Frattini adjustment and the
original bound N_G(Q) ≤ M give the literal product G_w = Y M_w.
Thus an escaping G_w forces Y to escape as well. The next module applies
C.1.29 inside this exact Y. Normality throughout is relative to G_w.

Source: Aschbacher--Smith, 12.1.1, printed p.788, using A.4.2, p.57.
The block-type exclusions and the other source branches remain with
qt-d-double-natural-centralizers; qt-d-1222-double-natural owns final assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterA.Section04 Chapter4 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original Q is Sylow in the literal residual-section centralizer. -/
theorem doubleNatural_adapted_normal_sectionCentralizer_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      IsSylowIn 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hn
  have hRH := (B.pointResidual_le w).trans inf_le_right
  have hHR := (normal_subgroupOf_iff_le_normalizer hRH).mp hn
  obtain ⟨P,hP⟩ := D.doubleNatural_adapted_ambientSylow_of_residual_normal h B S w hw hn
  have hm := normal_sylow_core_isMaximal (B.pointResidual w) (B.pointCentralizer w)
    hRH hHR (B.pointResidual_isPPerfect w) P
  rw [hP,D.doubleNatural_adapted_pointJoin_twoCore h B S w hw] at hm
  rw [sectionCentralizerIn_eq_twoSectionCentralizer]
  exact (maximal_signalizer_iff_sylow _ _ _ hRH hn.isSubnormal
    (B.pointResidual_isPPerfect w)).mp hm

/-- Frattini adjustment gives the source factorization with the original local centralizer. -/
theorem doubleNatural_adapted_normal_sectionCentralizer_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      (B.pointCentralizer w : Set G) =
        (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) : Set G) *
          (B.localPointCentralizer w : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hn
  let H := B.pointCentralizer w
  let Y := sectionCentralizerIn H (B.pointResidual w)
  have hHY : H ≤ normalizer (Y : Set G) := sectionCentralizerIn_normalized
    ((normal_subgroupOf_iff_le_normalizer ((B.pointResidual_le w).trans inf_le_right)).mp hn)
  obtain ⟨P,hP⟩ := D.doubleNatural_adapted_normal_sectionCentralizer_sylow h B S w hw hn
  have hQM : normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
    (normalizer_le_characteristicNormalizerClosure_self _ h.maximal_faithful.1.1.2.2).trans
      (D.doubleNatural_core_characteristicNormalizerClosure h)
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨y,hy⟩ := exists_frattini_adjustment Y P x (hHY hx)
    rw [hP] at hy
    refine ⟨(y : G)⁻¹,Y.inv_mem y.property,(y : G)*x,?_,inv_mul_cancel_left _ _⟩
    exact ⟨hQM hy,H.mul_mem y.property.1 hx⟩
  · rintro x ⟨y,hy,m,hm,rfl⟩
    exact H.mul_mem hy.1 hm.2

/-- Escape of the point centralizer forces escape of its residual-section centralizer. -/
theorem doubleNatural_adapted_normal_sectionCentralizer_outside
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      ¬ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) ≤
        normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hn hout hy
  apply hout
  intro x hx
  change x ∈ (B.pointCentralizer w : Set G) at hx
  rw [D.doubleNatural_adapted_normal_sectionCentralizer_product h B S w hw hn] at hx
  obtain ⟨y,hy',m,hm,rfl⟩ := hx
  exact (normalizer (L : Set G)).mul_mem (hy hy') hm.1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
