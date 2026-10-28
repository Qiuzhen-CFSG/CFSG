module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedMovement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalBinaryDerivedRadical

/-!
# Original derived-core movement and bounds, including the binary row

The source derived Frattini action is faithful for all Suzuki parameters.
Transport through the same original endpoint preserves its representation,
its q⁴ lower bound and the weighted bound for the next Frattini subgroup.
The original F.1.1 hypothesis supplies self-centralization for the latter.

In the binary row the corrected order-five mover changes a class represented
by an element of the actual original derived two-core. The last theorem
retains right conjugation by any original lift and the literal quotient Q.q;
it proves inequality in the same effective derived quotient, not merely
movement on the larger Frattini subgroup. No ambient finiteness, synchronized
fields, unknown-group simplicity or assumed movement witness is used.

Source: Fong--Seitz I (1973), effective sections preceding (6.1), p.52.
The positive-parameter (6.1), nonzero mixed-commutator cases, pairing and odd
degree, remaining (6H), Section 10 and final full-model comparison remain
with this source construction; the earlier conditional APIs are preserved.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include e ν hC μ hB in
/-- Faithful derived action and its original two-core quotient bound, for all m ≥ 0. -/
theorem original_source_derived_radical_effective (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
    (derivedRadicalSection Q split i hVi).IsEffective ∧
      Function.Injective (derivedRadicalSection Q split i hVi).effectiveRepresentation ∧
      Function.Injective (suzukiDerivedRepresentation Q split i hVi m μ hB) ∧
      (2^(2*m+1))^4 ≤ Nat.card
        (commutator (pCore 2 (parabolic L S i)) ⧸
          frattini (commutator (pCore 2 (parabolic L S i)))) := by
  dsimp only
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  let d := derivedRadicalSection Q split i hVi
  have hf := source_derivedRadical_effective Q split i j ν T hC m μ hB hm hij
  have hrep := d.effectiveRepresentation_injective hf
  refine ⟨?_,hrep,?_,?_⟩
  · unfold RootSection.IsEffective
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hf]
    exact bot_le
  · exact hrep.comp (suzukiActorEquiv Q split i m μ hB).symm.injective
  · rw [Nat.card_congr (originalDerivedFrattiniEquiv Q e split i hVi).toEquiv]
    exact source_derivedRadical_frattini_card_ge Q split i j ν T hC m μ hB hm hij

include e split ν hC μ hB in
/-- The actual original derived core satisfies the weighted bound, including Sz(2). -/
theorem original_source_derived_frattini_weighted_card_le
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (frattini (commutator (pCore 2 (parabolic L S i)))) * (2^(2*m+1))^2 ≤
      (Nat.card F)^4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  let a := originalDerivedRadicalEquiv Q e split i hVi
  rw [←card_map_of_injective (f := a.toMonoidHom) a.injective,frattini_map_equiv]
  exact source_derived_frattini_weighted_card_le Q split i j ν T hC m μ hB
    (parabolic_core_selfCentralizing Q e h i) hm hij

variable (μ₀ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB₀ : (quotientBorel Q i).map μ₀.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include e ν hC μ₀ hB₀ in
/-- The binary mover moves an actual original derived-core representative modulo its Frattini subgroup. -/
theorem original_binary_derived_effective_moves (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    let hVi := marked_suzuki_remainder_le_kernel Q split i 0 μ₀ hB₀
    let d := derivedRadicalSection Q split i hVi
    ∃ v : commutator (pCore 2 (parabolic L S i)),
      d.effectiveAction (frattiniMover Q split i 0 μ₀ hB₀)⁻¹
          (QuotientGroup.mk (originalDerivedRadicalEquiv Q e split i hVi v)) ≠
        QuotientGroup.mk (originalDerivedRadicalEquiv Q e split i hVi v) := by
  dsimp only
  let hVi := marked_suzuki_remainder_le_kernel Q split i 0 μ₀ hB₀
  let d := derivedRadicalSection Q split i hVi
  let c := frattiniMover Q split i 0 μ₀ hB₀
  let a := originalDerivedRadicalEquiv Q e split i hVi
  have hf := source_derivedRadical_effective Q split i j ν T hC 0 μ₀ hB₀ hm hij
  by_contra! hz
  have he : d.effectiveAction c⁻¹ = 1 := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective d.effectiveDenominator z
    obtain ⟨v,rfl⟩ := a.surjective x
    exact hz v
  have hc : c⁻¹ = 1 := hf (he.trans (map_one _).symm)
  have ho := (source_binary_derived_movement Q split i j ν T hC μ₀ hB₀ hm hij).1
  change orderOf c = 5 at ho
  have hc1 : c = 1 := inv_eq_one.mp hc
  rw [hc1,orderOf_one] at ho
  omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include ν hC μ hB in
/-- Genuine binary derived-section movement on literal Q.q representatives and right conjugation. -/
theorem original_binary_derived_effective_moves_quotient
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (g : generated L S) (hg : Q.q g = (frattiniMover Q split i 0 μ hB : (generated L S) ⧸ Q.D)) :
    let hVi := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
    let d := derivedRadicalSection Q split i hVi
    ∃ v : commutator (pCore 2 (parabolic L S i)), ∃ w : d.numerator,
      (w : (generated L S) ⧸ Q.D) =
        Q.q (g⁻¹*⟨v.val.val,parabolic_le_generated i v.val.val.property⟩*g) ∧
      QuotientGroup.mk' d.effectiveDenominator w ≠
        QuotientGroup.mk' d.effectiveDenominator
          (originalDerivedRadicalEquiv Q (originalMarkedIso Q) split i hVi v) := by
  dsimp only
  let hVi := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  let d := derivedRadicalSection Q split i hVi
  let c := frattiniMover Q split i 0 μ hB
  obtain ⟨v,hv⟩ := original_binary_derived_effective_moves Q (originalMarkedIso Q) split i j
    ν T hC μ hB hm hij
  let x : d.numerator := originalDerivedRadicalEquiv Q (originalMarkedIso Q) split i hVi v
  let w := d.numeratorAction c⁻¹ x
  refine ⟨v,w,?_,?_⟩
  · dsimp only [w]
    rw [d.numeratorAction_apply,coe_inv,inv_inv,←hg]
    dsimp only [x]
    rw [originalDerivedRadicalEquiv_quotient]
    simp only [map_mul,map_inv]
  · intro he
    apply hv
    exact (d.effectiveAction_mk c⁻¹ x).trans he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
