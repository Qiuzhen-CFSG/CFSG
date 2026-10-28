module

public import Theory.Representation.SL2OrthogonalCover.Universal
public import Theory.Representation.BinaryOffender.DualQuotientBound
public import Theory.Representation.BinaryGroupAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Dual bounds for central SL₂ natural covers

The upper root group has binary rank equal to the field degree and moves
the two-dimensional fixed plane of the orthogonal cover. Duality bounds
its ratio by two. The universal covering map carries that bound to every
binary central cover of the marked natural plane. The field of order two
is excluded explicitly.

Source: Aschbacher–Smith B.5.13 and I.2.3, printed pp.111 and 413.
-/

public section

open Representation Representation.OneCohomology Representation.BinaryOffender
open Matrix.SpecialLinearGroup
namespace Representation.SL2OrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in
private theorem upper_elementary : IsElementaryTwo (upperUnipotent F) := by
  let : IsElementaryAbelian 2 (Multiplicative F) := BinaryGroupAction.elementary
  refine ⟨?_, IsElementaryAbelian.of_surjective (upperUnipotentHom F).rangeRestrict
    (upperUnipotentHom F).rangeRestrict_surjective⟩
  intro hb
  have hc := card_upperUnipotent F
  rw [hb, Subgroup.card_bot] at hc
  exact (Finite.one_lt_card (α := F)).ne hc

omit [CharP F 2] in
private theorem upper_rank : rank (upperUnipotent F) = Module.finrank (ZMod 2) F := by
  rw [rank, card_upperUnipotent, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, Nat.log_pow (by decide)]

private def planeEquiv : fixedPlane (F := F) ≃ₗ[F] (Fin 2 → F) where
  toFun v := ![v.val 0, v.val 1]
  invFun v := ⟨![v 0, v 1, 0], rfl⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [show v.val 2 = 0 from v.property]
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

/-- The literal universal cover has dual quadratic ratio at most two. -/
theorem model_dual_ratio (hF : 2 < Nat.card F) :
    quadraticRatio (binaryAction (F := F)).dual ≤ 2 := by
  let A := upperUnipotent F
  have hc : Coinvariants.ker ((binaryAction (F := F)).comp A.subtype) =
      (fixedPlane (F := F)).restrictScalars (ZMod 2) := by
    change Coinvariants.ker (restrictScalars (k := ZMod 2) (action.comp A.subtype)) = _
    rw [coinvariants_restrictScalars, root_commutator hF]
  have hq : Coinvariants.ker ((binaryAction (F := F)).comp A.subtype) ≤
      Representation.invariants ((binaryAction (F := F)).comp A.subtype) := by
    rw [hc]
    exact (root_fixed (F := F)).symm.le
  have hqd := (commutator_le_invariants_iff_dual
    ((binaryAction (F := F)).comp A.subtype)).mp hq
  refine (quadraticRatio_le_two_iff _).mpr ⟨A, upper_elementary, ?_, ?_⟩
  · exact fun a ha b hb v =>
      (commutator_le_invariants_iff _).mp hqd ⟨a,ha⟩ ⟨b,hb⟩ v
  · change Module.finrank (ZMod 2) (_ ⧸ _) ≤ _
    change Module.finrank (ZMod 2) (_ ⧸ Representation.invariants (Representation.dual ((binaryAction (F := F)).comp A.subtype))) ≤ _
    rw [finrank_dual_quotient_invariants, hc]
    rw [((Submodule.restrictScalarsEquiv (ZMod 2) F (Space F) fixedPlane).restrictScalars (ZMod 2)).finrank_eq,
      ← Module.finrank_mul_finrank (ZMod 2) F (fixedPlane (F := F)),
      (planeEquiv (F := F)).finrank_eq, Module.finrank_pi, Fintype.card_fin]
    simp only [A, upper_rank]
    omega

/-- Every binary central cover retains the same dual bound. -/
theorem cover_dual_quadraticRatio_le_two (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (SL F) W}
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p) :
    quadraticRatio σ.dual ≤ 2 := by
  obtain ⟨f,hf,_⟩ := exists_quotient_of_finrank_ker_eq (binaryProjection (F := F))
    (binaryProjection_isCover (card_gt_two n hn hF))
    (by rw [binary_kernel_finrank n hF, binary_dual_H1_finrank n hn hF]) p hp
  exact dual_quadraticRatio_le_two_of_surjective f hf (model_dual_ratio (card_gt_two n hn hF))
end Representation.SL2OrthogonalCover
