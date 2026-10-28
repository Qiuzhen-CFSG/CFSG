module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.MovingApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs

/-!
# Corrected 5.12 with faithful moving linear and Suzuki quotients

The original moving-neighbor module supplies the actual actor, quotient
Sylow, quadraticity, Sylow-fixed generation, residual fixed-space vanishing
and core-index formula. The kernel argument now proves faithfulness on the
whole linear or Suzuki quotient. The resulting lower bound and conditional
natural coordinates use that same action, with no faithfulness callback.
The Suzuki square bound includes the solvable Sz(2) endpoint.

Source: DGS, *Groups and Graphs* (1985), 8.2--8.7, pp.134--140,
and corrected 5.12, pp.113--115. `ReducedModuleEstimates` applies these
results to the literal reduced F1.11 configuration. Strict comparisons,
quotient-center action and the final distance and field conclusions remain.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- The moving neighbor's actual linear quotient acts faithfully. Corrected
5.12 has no remaining faithfulness, generation or residual-fixed premise. -/
theorem source_moving_linear_recognition
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* SL(2,K)) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
    let Aq := (A.subgroupOf (d.localGroup w.val)).map q
    ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z F w.val))) (S : Sylow 2 SL(2,K)),
      (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) ∧
      Aq ≤ S ∧ Aq ≠ ⊥ ∧ IsQuadratic ρ Aq ∧ Function.Injective ρ ∧
      GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 SL(2,K)) = ⊥ ∧
      Nat.card Aq = (Q F w.val).relIndex A ∧
      (Q F w.val).relIndex A ≤ Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) ∧
      (Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) < (Q F w.val).relIndex A ^ 2 →
        NaturalRealization ρ S) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  dsimp only
  obtain ⟨ρ, S, hact, hAS, hne, hq, _, hgen, hfix, hcard, hbound⟩ :=
    source_moving_center_bound_and_recognition h d hc hab hd hb hcomm w hm
      (.sl2 K n hn hK (MulEquiv.refl _)) e
  have hf := linear_quotient_action_faithful hn hK e ρ hfix
  exact ⟨ρ, S, hact, hAS, hne, hq, hf, hgen, hfix, hcard, hbound hf⟩

/-- The actual moving Suzuki module satisfies the square bound at every
parameter, including Sz(2). Whole-action faithfulness is proved here. -/
theorem source_moving_suzuki_square_bound
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    (m : ℕ) (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
    let Aq := (A.subgroupOf (d.localGroup w.val)).map q
    ∃ (ρ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
        (Additive (Z F w.val))) (S : Sylow 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)),
      (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) ∧
      Aq ≤ S ∧ Aq ≠ ⊥ ∧ IsQuadratic ρ Aq ∧ Function.Injective ρ ∧
      GeneratedByFixedSpace ρ S ∧ fixedSpace ρ
        (pResidual 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) = ⊥ ∧
      Nat.card Aq = (Q F w.val).relIndex A ∧
      (Q F w.val).relIndex A ^ 2 ≤ Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  let : Finite (Z (family P) w.val) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) w.val)) (inclusion_injective _)
  dsimp only
  obtain ⟨ρ, S, hact, hAS, hne, hq, hgen, hfix, hcard⟩ :=
    source_moving_center_module h d hc hab hd hb hcomm w hm e
  have hf := suzuki_quotient_action_faithful m e ρ hfix
  refine ⟨ρ, S, hact, hAS, hne, hq, hf, hgen, hfix, hcard, ?_⟩
  simpa only [hcard] using suzuki_all_square_bound m ρ hf S _ hAS hq

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
