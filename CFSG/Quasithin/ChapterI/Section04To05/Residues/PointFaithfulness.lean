module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreActions
public import Theory.SpecificGroups.SymmetricSix.Parabolics.CosetKernels

/-!
# Faithfulness on original points after unique lines

The original point group acts on its incident lines with kernel its
two-core, by the actual A₆/S₆ quotient marking. An element fixing every
point fixes every three-point line once lines through distinct points are
unique. Thus the global point kernel lies in the point two-core and hence
in the common chamber. D4 makes that normal kernel trivial.

This proves I.5.8(2) from the earlier unique-line conclusion; the final
consumer reduces both parts of I.5.8 to the I.5.7 line-kernel separation.
Source: Aschbacher–Smith I.5.8, printed p.421.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_line_parabolic_normalCore :
    (localParabolic S.family 0 1).normalCore = pCore 2 (S.family 0) := by
  have hker {K : Type} [Group K]
      (e : (S.family 0 ⧸ pCore 2 (S.family 0)) ≃* K) :
      (S.localQuotientMap 0 e).ker ≤ localParabolic S.family 0 1 :=
    (S.localQuotientMap_ker_le 0 e).trans (S.point_parabolics.borel_eq ▸ inf_le_left)
  rcases S.point_standard_quotientMark with ⟨e, he⟩ | ⟨e, he⟩
  · rw [← S.localQuotientMap_ker 0 e]
    apply Subgroup.normalCore_eq_ker_of_map_core_free
      _ _ (S.localQuotientMap_surjective 0 e) (hker e)
    rcases he with h | h
    · rw [h.1]; exact Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer_normalCore
    · rw [h.1]; exact Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer_normalCore
  · rw [← S.localQuotientMap_ker 0 e]
    apply Subgroup.normalCore_eq_ker_of_map_core_free
      _ _ (S.localQuotientMap_surjective 0 e) (hker e)
    rcases he with h | h
    · rw [h.1]; exact Theory.SpecificGroups.SymmetricSix.duadStabilizer_normalCore
    · rw [h.1]; exact Theory.SpecificGroups.SymmetricSix.synthemeStabilizer_normalCore

theorem point_fixer_fixes_lines
    (hunique : ∀ {x y : S.Point}, x ≠ y → ∀ {l m : S.Line},
      S.Inc x l → S.Inc y l → S.Inc x m → S.Inc y m → l = m)
    {g : G} (hg : ∀ x : S.Point, g • x = x) (l : S.Line) : g • l = l := by
  have hc := S.line_points_card l
  let : Finite {x : S.Point // S.Inc x l} := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  let : Nontrivial {x : S.Point // S.Inc x l} := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne {x : S.Point // S.Inc x l}
  apply hunique (x := x.val) (y := y.val) (fun he => hxy (Subtype.ext he))
  · simpa only [hg] using x.property.smul S g
  · simpa only [hg] using y.property.smul S g
  · exact x.property
  · exact y.property

theorem faithful_points_of_unique_lines
    (hunique : ∀ {x y : S.Point}, x ≠ y → ∀ {l m : S.Line},
      S.Inc x l → S.Inc y l → S.Inc x m → S.Inc y m → l = m) :
    FaithfulSMul G S.Point := by
  let N := (MulAction.toPermHom G S.Point).ker
  have hNQ : N ≤ S.Q 0 := by
    intro g hg
    have hfix (x : S.Point) : g • x = x := Equiv.congr_fun hg x
    have hg0 : g ∈ S.family 0 := by
      rw [← S.stabilizer_basePoint]
      exact hfix S.basePoint
    let a : S.family 0 := ⟨g, hg0⟩
    have ha : a ∈ pCore 2 (S.family 0) := by
      rw [← S.point_line_parabolic_normalCore, Subgroup.normalCore_eq_ker]
      apply Equiv.Perm.ext
      intro q
      apply (S.pointedCosetEquiv 0 1 (by decide)).injective
      apply Subtype.ext
      change (S.pointedCosetEquiv 0 1 (by decide) (a • q)).val = _
      rw [S.pointedCosetEquiv_smul]
      exact S.point_fixer_fixes_lines hunique hfix _
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hbot : N = ⊥ := S.normal_eq_bot N (hNQ.trans (S.Q_le_T 0))
  have hinj := (MulAction.toPermHom G S.Point).ker_eq_bot_iff.mp hbot
  constructor
  intro g h he
  exact hinj (Equiv.ext he)

theorem faithful_points_of_kernel_separation
    (hsep : ∀ l m : S.Line, S.Inc S.basePoint l → S.Inc S.basePoint m →
      S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z l} =
        S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z m} → l = m) :
    FaithfulSMul G S.Point :=
  S.faithful_points_of_unique_lines (S.unique_line_of_kernel_separation hsep)

end Quasithin.I5.DSystem
