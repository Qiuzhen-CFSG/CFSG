module
public import Theory.Representation.BinaryIndexThreeDisplacement
public import Theory.Representation.BinaryConjugationCoordinates.SupplementSpaces

/-!
# The group commutator of an index-three fixed line

Transport a binary line and its actual conjugation action to additive
coordinates. The index-three displacement theorem computes a plane there;
the subgroup/subspace identification gives order four for the original
group commutator, with the same normal supplement and fixed subgroup.

The product amalgam in Aschbacher–Smith 13.4.15 uses this calculation for
the fixed-line orbit under its original parabolic (printed p.912).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryConjugationCoordinates
open scoped IsMulCommutative
namespace Representation.BinaryConjugationCoordinates
variable {G : Type*} [Group G] [Finite G]

/-- A normal supplement moving a binary line fixed by an index-three subgroup
has a literal group commutator of order four. -/
theorem line_displacement_card_of_index_three
    (A U F R : Subgroup G) [IsElementaryAbelian 2 U]
    (hAU : A ≤ normalizer (U : Set G)) (hFU : F ≤ U)
    (hF : Nat.card F = 2) (hRA : R ≤ A)
    [(R.subgroupOf A).Normal]
    (S : Subgroup A) (hS : S.index = 3) (hgen : R.subgroupOf A ⊔ S = ⊤)
    (hSF : S.map A.subtype ≤ centralizer (F : Set G))
    (hm : ¬ R ≤ centralizer (F : Set G)) :
    Nat.card (⁅F,R⁆ : Subgroup G) = 4 := by
  let ρ := elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion hAU))
  let e : Representation.Equiv (ρ.comp (MonoidHom.id A)) ρ := .refl _
  let space := modelSpace U A hAU (MonoidHom.id A) ρ e
  obtain ⟨v,hv,huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  let w : Additive U := Additive.ofMul ⟨v.val,hFU v.property⟩
  have hspace : space F = Submodule.span (ZMod 2) {w} := by
    apply le_antisymm
    · intro x hx
      have hxF : x.toMul.val ∈ F := hx
      by_cases hx1 : (⟨x.toMul.val,hxF⟩ : F) = 1
      · have hx0 : x = 0 := by
          apply Additive.toMul.injective
          exact Subtype.ext (congrArg (fun t : F => t.val) hx1)
        rw [hx0]
        exact Submodule.zero_mem _
      · have hxv : x = w := by
          apply Additive.toMul.injective
          exact Subtype.ext (congrArg (fun t : F => t.val) (huniq _ hx1))
        rw [hxv]
        exact Submodule.mem_span_singleton_self _
    · apply Submodule.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact v.property
  have hfixed (s : A) (hs : s ∈ S) : ρ s w = w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change s.val * v.val * s.val⁻¹ = v.val
    exact mul_inv_eq_iff_eq_mul.mpr
      ((hSF (mem_map_of_mem A.subtype hs)) v.val v.property).symm
  have hmove : ∃ a ∈ R.subgroupOf A, ρ a w ≠ w := by
    by_contra hn
    push Not at hn
    apply hm
    intro a ha x hx
    by_cases hx1 : (⟨x,hx⟩ : F) = 1
    · have hx1' : x = 1 := congrArg Subtype.val hx1
      simp [hx1']
    · have hxv : x = v.val := congrArg Subtype.val (huniq _ hx1)
      rw [hxv]
      have hh := congrArg (fun y : Additive U => y.toMul.val) (hn ⟨a,hRA ha⟩ ha)
      change a * v.val * a⁻¹ = v.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hc := index_three_displacement_card ρ S (R.subgroupOf A) hgen hS w hfixed hmove
  have heq := modelSpace_commutator U A hAU (MonoidHom.id A) ρ e F R hFU (hRA.trans hAU)
    (fun a ha => ⟨⟨a,hRA ha⟩,ha,fun _ => rfl⟩)
  change space ⁅F,R⁆ = subspaceCommutator ρ (space F)
    ((R.subgroupOf A).map (MonoidHom.id A)) at heq
  rw [map_id,hspace] at heq
  rw [←heq] at hc
  have hDU : ⁅F,R⁆ ≤ U :=
    (commutator_mono hFU le_rfl).trans (le_normalizer_iff_commutator_le_left.mp (hRA.trans hAU))
  let j : space ⁅F,R⁆ ≃ (⁅F,R⁆ : Subgroup G) := {
    toFun x := ⟨x.val.toMul.val,x.property⟩
    invFun x := ⟨Additive.ofMul ⟨x.val,hDU x.property⟩,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr j).symm.trans hc
end Representation.BinaryConjugationCoordinates
