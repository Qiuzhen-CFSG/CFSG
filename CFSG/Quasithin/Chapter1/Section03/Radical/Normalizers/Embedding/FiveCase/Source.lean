module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.Kernel
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape

/-!
# The source setup for the conditional case-(10) deduction

The inputs below stop after selection of the containing component and case
(10). All groups are the actual normalizer residuals and their quotient
images. The residual, radical-structure and nonnormality premises are the
outputs of the preceding independent reductions; no prime identification,
marked kernel, residual equality or parabolic recognition is included.

The prime r is tied to L/O₂,F(L), expressed as the iterated quotient of
L/O₂(L) by its Fitting subgroup. Its value five follows here from the
nilpotent alternative and the orders of the two actual SL₂ models.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 1.3.8, printed pp.512–513, and A.3.12(10), printed p.47.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source quotient L/O₂,F(L), as an iterated quotient. -/
abbrev fittingQuotient (L : Subgroup G) :=
  XiQuotient L ⧸ fittingSubgroup (XiQuotient L)

/-- The actual image of D in N/O₂(N). -/
abbrev quotientImage (D N : Subgroup G) : Subgroup (XiQuotient N) :=
  (D.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))

/-- Inputs available before the case-(10) deduction. Relative normality of K
is inside N_G(C); C is characteristic inside R. -/
structure SourceData (𝒦 : GroupClass.{u}) (p r : ℕ) (L : Subgroup G)
    (T : Sylow 2 G) (C : Subgroup (radicalCore p L T)) (K : Subgroup G) : Prop where
  ambient : IsSimpleQTKE 𝒦 G
  prime : p.Prime
  large : 3 < p
  prime_r : r.Prime
  maximal : L ∈ Chapter1.LStar G T
  invariant : (T : Subgroup G) ≤ normalizer (L : Set G)
  xi : XiMember T (XiP p L)
  xi_shape : XiOddQuotient p (XiQuotient (XiP p L))
  fitting_prime : p ∣ Nat.card (fittingSubgroup (XiQuotient L))
  nilpotent : A36Nilpotent (XiQuotient L)
  quotient_r : IsSL (fittingQuotient L) 2 r
  second_prime : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧
    q ∣ Nat.card (fittingSubgroup (XiQuotient L))
  characteristic : C.Characteristic
  nontrivial : C ≠ ⊥
  normalizers : normalizer (L : Set G) = normalizer (XiP p L : Set G)
  escape : ¬ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
    normalizer (L : Set G)
  contains_xi : XiP p L ≤ normalizerResidual L (radicalCore p L T)
  local_Y : normalizerResidual L (radicalCore p L T) ∈ Chapter1.L G T
  nonsimple_Y : ¬ IsQuasisimple (XiQuotient (normalizerResidual L (radicalCore p L T)))
  local_LC : normalizerResidual L (C.map (radicalCore p L T).subtype) ∈ Chapter1.L G T
  commutator : ⁅normalizerResidual L (C.map (radicalCore p L T).subtype),
    normalizerResidual L (radicalCore p L T)⁆ =
      normalizerResidual L (C.map (radicalCore p L T).subtype)
  component : K ∈ cComponentsIn (normalizer (C.map (radicalCore p L T).subtype : Set G))
  contains_Y : normalizerResidual L (radicalCore p L T) ≤ K
  normal : (K.subgroupOf
    (normalizer (C.map (radicalCore p L T).subtype : Set G))).Normal
  nonnormal_xi : ¬ ((XiP p L).subgroupOf K).Normal
  radical_exclusion : ¬ XiP p L ≤ (solvableRadical K).map K.subtype

/-- Precisely the two actual model assertions of A.3.12(10). -/
structure CaseTen (B Kbar : Subgroup G) (s : ℕ) : Prop where
  prime : s.Prime
  large : 3 < s
  small : HasExtension B (ElementaryModel s 2) (fun X _ => IsSL X 2 s)
  large_model : ClassicalGroup.IsPSL Kbar 3 s ∨ IsSL Kbar 3 s

/-- The actual quotient parameter is already forced by the nilpotent branch. -/
theorem parameter_eq_five {r : ℕ} (hr : r.Prime) (L : Subgroup G)
    (hnil : A36Nilpotent (XiQuotient L))
    (hrmodel : IsSL (fittingQuotient L) 2 r) : r = 5 := by
  have hfive : IsSL (fittingQuotient L) 2 5 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hnil.2.2.1
    exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq hnil.1).symm.trans e⟩⟩
  exact isSL_two_parameter_five hr hrmodel hfive

/-- The prescribed L_C lies in the actual containing component. -/
theorem SourceData.residual_le {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K) :
    normalizerResidual L (C.map (radicalCore p L T).subtype) ≤ K :=
  residual_le_component L (radicalCore p L T) K C h.component.1 h.normal
    h.contains_Y h.commutator

omit [Finite G] in
/-- Normality of Ξ_p(L) in any intermediate subgroup of L, including L_C. -/
theorem xi_normal_in_intermediate (p : ℕ) {L D : Subgroup G}
    (hDL : D ≤ L) : ((XiP p L).subgroupOf D).Normal :=
  normal_subgroupOf_of_le_normalizer
    (hDL.trans (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L)))

/-- Transfer both possibilities for the large model to the intrinsic quotient.
This equivalence is composed with the inclusion-induced quotient equivalence. -/
theorem component_model_five {K N : Subgroup G} (hKN : K ≤ N)
    (hK : (K.subgroupOf N).IsCComponent)
    (hmodel : ClassicalGroup.IsPSL (quotientImage K N) 3 5 ∨
      IsSL (quotientImage K N) 3 5) :
    Nonempty (XiQuotient K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5)) := by
  obtain ⟨e⟩ := large_five_model hmodel
  exact ⟨(componentQuotientEquiv hKN hK).trans e⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
