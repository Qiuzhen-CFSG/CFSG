module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianPointWhole
public import Theory.Representation.BinaryFixedLineTransvections
public import Theory.Representation.ExtraspecialSmallFixedSpace

/-!
# Exact geometry of the remaining fixed-line action

In the remaining nonabelian branch, an actor fixing the original E-hat has
rank at most two: its displacement on the marked hyperplane lies in the
common fixed line. The previously proved displacement bound excludes that
kernel. Full centered transvections therefore identify the actor rank with
dim(E-hat) minus one. The G.10 dimension identity and isotropy force E-hat
to be Lagrangian. The modular fixed-space bound then gives actor rank at
least three and ambient degree at least eight.

The final application computes the orders of the original actor, E and U,
using Z(U) = V₁ and the literal quotient kernels. Both source degrees, the
original flag, escaping element and earlier inputs are retained. Excluding
this remaining fixed-line geometry is still required for point-span abelianity.

Source: Aschbacher--Smith G.10.1--2, G.11.1(3i) and 12.9.4,
printed pp.357,364,859--860.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic

private theorem marked_action_faithful
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
    {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hf : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hr : ∀ x ∈ X, x ≠ 1 → 2 < finrank (ZMod 2) (RankTwo.movedSpace ρ x)) :
    ∀ x y : X, (∀ w : W, ρ x w = ρ y w) → x = y := by
  have hcod : finrank (ZMod 2) (A ⧸ (B v).ker) ≤ 1 := by
    have hnull := (B v).finrank_range_add_finrank_ker
    have hquot := (B v).ker.finrank_quotient_add_finrank
    have hle : finrank (ZMod 2) (B v).range ≤ 1 := by
      simpa using (B v).range.finrank_le
    omega
  have hker (a : X) (ha : ∀ w ∈ W, ρ a w = w) : a = 1 := by
    by_contra hne
    have hlo := hr a a.property (fun he => hne (Subtype.ext he))
    have hup := BinaryFixedLine.rank_le_two_of_fixes_marked ρ X v h.point_ne_zero W
      (B v).ker hcod h.displacement hf a ha
    exact (not_lt_of_ge hup) hlo
  intro x y he
  have hdiff : y⁻¹ * x = 1 := hker (y⁻¹*x) (by
    intro w hw
    have hh := congrArg (ρ (y : D)⁻¹) (he ⟨w,hw⟩)
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,←Module.End.mul_apply,
      ←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh)
  exact (inv_mul_eq_one.mp hdiff).symm

private theorem marked_dimension
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
    {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hfaith : ∀ x y : X, (∀ w : W, ρ x w = ρ y w) → x = y) :
    finrank (ZMod 2) (Additive X) + 1 = finrank (ZMod 2) W ∧
      finrank (ZMod 2) A = 2 * (finrank (ZMod 2) (Additive X) + 1) ∧
      W = B.orthogonal W := by
  have hr := BinaryFixedLine.actor_rank_of_faithful_full_transvections ρ X v
    h.point_ne_zero W h.point_mem h.transvections h.full_transvections hfaith
  have hi := B.twice_finrank_le_of_isotropic h.nondegenerate W h.isotropic
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
  have hd := h.dimension
  have hp := h.two_le_dimension
  have he : finrank (ZMod 2) A = 2 * (finrank (ZMod 2) (Additive X) + 1) := by omega
  refine ⟨hr,he,Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · exact fun _ hw _ hu => h.isotropic _ hu _ hw
  · rw [B.finrank_orthogonal h.nondegenerate]
    omega

private theorem actor_rank_three_le
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) D A) (v : A) (hv : v ≠ 0) (X : Subgroup D)
    [IsElementaryAbelian 2 X]
    (hf : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hd : 6 ≤ finrank (ZMod 2) A) :
    3 ≤ finrank (ZMod 2) (Additive X) := by
  have hb := ExtraspecialSmallFixedSpace.finrank_le_card_mul_invariants (ρ.comp X.subtype)
    (by simp [ZMod.ringChar_zmod_n])
    (by simpa only [ZMod.ringChar_zmod_n] using IsElementaryAbelian.isPGroup 2 X)
  change finrank (ZMod 2) A ≤ Nat.card X * finrank (ZMod 2) (fixedSpace ρ X) at hb
  rw [hf,finrank_span_singleton hv,mul_one,Nat.card_congr Additive.ofMul,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X),Nat.card_zmod] at hb
  by_contra hlt
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show finrank (ZMod 2) (Additive X) ≤ 2 by omega)
  have hh : 2 ^ finrank (ZMod 2) (Additive X) ≤ 4 := hp
  omega

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The remaining nonabelian action is faithful on the original E-hat.
This marked space is Lagrangian, of dimension one more than the actor rank.
The actual fixed-line bound forces actor rank at least three and degree at least eight. -/
theorem nonabelian_fixed_line_lagrangian
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        (∀ x y : F.terminalDot (F.X g),
          (∀ w : hatSpace F (F.E g), F.terminalRepresentation x w = F.terminalRepresentation y w) →
          x = y) ∧
        hatSpace F (F.E g) = B.orthogonal (hatSpace F (F.E g)) ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) + 1 =
          finrank (ZMod 2) (hatSpace F (F.E g)) ∧
        finrank (ZMod 2) (Additive F.Uhat) =
          2 * (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) + 1) ∧
        3 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ∧
        8 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
  obtain ⟨hX,B,v,hg10,hline,_⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  obtain ⟨hfix,hrank⟩ := nonabelian_fixed_line_and_moved_rank modules h hn preferred earlier four
    F hne g hgP hgH
  have hfixed := hfix.trans hline
  have hfaith := marked_action_faithful hg10 hfixed hrank
  obtain ⟨hr,hd,horth⟩ := marked_dimension hg10 hfaith
  have hlow : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
    have hh := nonabelian_hat_rank h earlier F hne
    omega
  have hthree := actor_rank_three_le F.terminalRepresentation v hg10.point_ne_zero
    (F.terminalDot (F.X g)) hfixed hlow
  exact ⟨hX,B,v,hg10,hline,hfaith,horth,hr,hd,hthree,by omega⟩

/-- Exact orders of the original actor, intersection and extraspecial span.
The center kernel is the original point of order two. -/
theorem nonabelian_fixed_line_orders
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ r : ℕ, 3 ≤ r ∧ Nat.card (F.terminalDot (F.X g)) = 2 ^ r ∧
      Nat.card (F.E g) = 2 ^ (r + 2) ∧ Nat.card F.U = 2 ^ (2 * r + 3) := by
  let := h.chosen.elementary
  obtain ⟨hX,B,v,_,_,_,_,hr,hd,hthree,_⟩ := nonabelian_fixed_line_lagrangian
    modules h hn preferred earlier four F hne g hgP hgH
  let := hX
  let r := finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))
  have hZ := nonabelian_center_eq_point modules h hn preferred earlier four F hne g hgP hgH
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  have hZcard : Nat.card F.ZU = 2 := by simpa only [hZ] using hp
  have hcenter : Nat.card (center F.U) = 2 := by
    have he := card_map_of_injective (K := center F.U) F.U.subtype_injective
    exact he.symm.trans hZcard
  have hE : F.E g ≤ F.U := inf_le_left.trans inf_le_left
  have hZE : F.ZU ≤ F.E g := by
    rw [hZ]
    exact (F.monotone (by omega : 1 ≤ 2)).trans
      (plane_le_E F g (F.P_le_G₂ (by omega) L h.chosen.normalizes hgP))
  have hEcard := card_hatImage_mul_card_inf F (F.E g) hE
  rw [inf_eq_right.mpr hZE,hZcard,←card_hatSpace] at hEcard
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F (F.E g)),
    Nat.card_zmod,←hr] at hEcard
  have hUhat : Nat.card F.Uhat = 2 ^ (2 * (r+1)) := by
    rw [Nat.card_congr Additive.ofMul,
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat),Nat.card_zmod,hd]
  have hUcard := (center F.U).card_mul_index
  rw [index_eq_card,hcenter,hUhat] at hUcard
  refine ⟨r,hthree,?_,?_,?_⟩
  · rw [Nat.card_congr Additive.ofMul,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  · change Nat.card (F.E g) = 2 ^ (r + 1 + 1)
    rw [pow_succ]
    exact hEcard.symm
  · rw [show 2*r+3 = 2*(r+1)+1 by omega,pow_succ]
    exact hUcard.symm.trans (Nat.mul_comm _ _)
end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
