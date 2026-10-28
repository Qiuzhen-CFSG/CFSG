module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.Local
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognitionComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SmallSylow

/-!
# Line centralization from the two mixed zero-core inputs

The preceding local reduction prepares the original F.1.1 pair (K,U,T).
A mixed A₅/S₃ recognition bound gives |T| at most 256. The actual tensor
module has order 256 and is proper in T, so this excludes the moving
zero-core branch. The completed nonzero-core argument then centralizes
the literal tensor line.

The final application obtains the original Hall cubic, order-nine Cartan,
and A₅ residual quotient from the checked source theorems. Only the
construction of U = Dσ T₂ and the mixed F.1.12 size theorem remain explicit.
Thus this is conditional source assembly, not a completed proof of 9.3.1.

Source: Aschbacher–Smith, original 9.3.1, printed pp.732–733, and
F.1.12(I), printed pp.262–264 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4 ChapterE MixedZeroCore
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The source construction of Dσ T₂, restricted to the moving zero-core branch.
All Cartan, quotient, Hall and original ambient hypotheses are retained. -/
@[expose] def MixedCubicFactorInput : Prop :=
  ∀ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal →
    1 < generationParameter H →
    (((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) →
    ∀ (A B : Subgroup G), A ≤ sourceOrbitBorel T L →
      Nat.card A = 9 → IsElementaryAbelian 3 A →
      B ≤ A → B ≤ (pResidual 2 H).map H.subtype → Nat.card B = 3 →
      IsHallSubgroup oddPrimes (B.subgroupOf (H ⊓ D.maximalLocal)) →
      B = A ⊓ centralizer (m.tensorLine : Set G) →
      pCore 2 (H ⊔ A : Subgroup G) = ⊥ →
      ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) →
      ∃ U : Subgroup G, CubicFactor T A B U

/-- Apply the mixed F.1.12 bound to the literal pair prepared above. -/
theorem mixed_zero_core_sylow_bound
    (size : MixedSizeInput G)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    Nat.card T ≤ 256 := by
  obtain ⟨hf,hqt,hSyl,hb,_,_,_⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  exact size _ U (T : Subgroup G) hf hqt hSyl ⟨eK⟩ hU.2.2.2.2
    ((hb ▸ inf_le_left).trans (T : Subgroup G).le_normalizer)

/-- Original 9.3.1 line centralization after the two independent mixed inputs.
The nonzero-core branch and the original A₅ recognition are discharged. -/
theorem old_residual_centralizes_tensorLine_of_mixed_inputs
    (size : MixedSizeInput G) (factor : m.MixedCubicFactorInput)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  obtain ⟨_,B,A,_,hBK,hBA,hAB,hA9,hAe,hB3,_,hHall,hBC⟩ := m.hstar_cartan hH hlarge
  by_contra hmove
  by_cases hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥
  · obtain ⟨U,hU⟩ := factor H hH hlarge eK A B hAB hA9 hAe hBA hBK hB3 hHall hBC hzero hmove
    exact (not_lt_of_ge (mixed_zero_core_sylow_bound size hH eK A B U hAB hBA hBK hB3 hU hzero))
      (m.sylow_card_gt_256 m.sylow_not_normalizes_component)
  · exact hmove (m.old_residual_centralizes_tensorLine_of_nonzero_cartan_core hH eK A B
      hAB hA9 hAe hB3 hBC hzero)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
