module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Coordinates

/-!
# The two marked displacement centers in the actual coordinates

Each constituent displacement has binary dimension one. Its unique nonzero
vector gives one coordinate center. The earlier identity [U/Z,v] = (V∩U)/Z
then places every V∩U vector in the product of those two coordinate lines.
This is the exact marking used in the final orthogonal local geometry.
Source: Aschbacher–Smith 15.3.53(2), 15.3.57(2b), and 15.3.58(3).
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}
  {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}

private theorem binary_line_generator {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (P : Submodule (ZMod 2) W)
    (hP : Module.finrank (ZMod 2) P = 1) :
    ∃ c : W, c ≠ 0 ∧ c ∈ P ∧ ∀ w ∈ P, w = 0 ∨ w = c := by
  have hc : Nat.card P = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hP, pow_one]
  obtain ⟨c, hc, hu⟩ := (Nat.card_eq_two_iff' (0 : P)).mp hc
  refine ⟨c, fun he => hc (Subtype.ext he), c.property, fun w hw => ?_⟩
  by_cases h : w = 0
  · exact Or.inl h
  · exact Or.inr (congrArg Subtype.val (hu ⟨w, hw⟩ (fun he => h (congrArg Subtype.val he))))

namespace NaturalPair
variable (p : NaturalPair d a)

/-- The literal V∩U image has two nonzero binary coordinate centers. -/
theorem displacement_centers :
    ∃ c : BinaryLinearThree.Vector, c ≠ 0 ∧
    ∃ f : Module.Dual (ZMod 2) BinaryLinearThree.Vector, f ≠ 0 ∧
      ∀ x : closureU Z ZS, (x : G) ∈ V →
        (p.coordinates (QuotientGroup.mk' _ x)).toAdd.1 ∈ ({0, c} : Set _) ∧
        (p.coordinates (QuotientGroup.mk' _ x)).toAdd.2 ∈ ({0, f} : Set _) := by
  let D := actorRepresentation Z ZS d.kernel v - LinearMap.id
  let D₁ := LinearMap.range (D.comp p.pair.first.toSubmodule.subtype)
  let D₂ := LinearMap.range (D.comp p.pair.second.toSubmodule.subtype)
  have h₁ : D₁ ≤ p.pair.first.toSubmodule := by
    rintro w ⟨x, rfl⟩
    exact p.pair.first.toSubmodule.sub_mem
      ((Submodule.map_le_iff_le_comap.mp (le_of_eq p.pair.first_invariant)) x.property) x.property
  have h₂ : D₂ ≤ p.pair.second.toSubmodule := by
    rintro w ⟨x, rfl⟩
    exact p.pair.second.toSubmodule.sub_mem
      ((Submodule.map_le_iff_le_comap.mp (le_of_eq p.pair.second_invariant)) x.property) x.property
  obtain ⟨c, hc, hcD, hcu⟩ := binary_line_generator D₁ p.pair.first_displacement
  obtain ⟨f, hf, hfD, hfu⟩ := binary_line_generator D₂ p.pair.second_displacement
  have hc₂ : (p.linearCoordinates c).2 = 0 := (p.mem_first_iff c).mp (h₁ hcD)
  have hf₁ : (p.linearCoordinates f).1 = 0 := (p.mem_second_iff f).mp (h₂ hfD)
  refine ⟨(p.linearCoordinates c).1, ?_, (p.linearCoordinates f).2, ?_, ?_⟩
  · intro he
    exact hc (p.linearCoordinates.map_eq_zero_iff.mp (Prod.ext he hc₂))
  · intro he
    exact hf (p.linearCoordinates.map_eq_zero_iff.mp (Prod.ext hf₁ he))
  · intro x hx
    have hm : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x) ∈
        LinearMap.range D := by
      rw [d.displacement]
      change QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x ∈
        vectorImage Z ZS (V ⊓ closureU Z ZS)
      exact ⟨x, ⟨hx, x.property⟩, rfl⟩
    obtain ⟨w, hw⟩ := hm
    have hw' : w ∈ p.pair.first.toSubmodule ⊔ p.pair.second.toSubmodule := by
      rw [p.pair.complement.sup_eq_top]
      trivial
    obtain ⟨w₁, hw₁, w₂, hw₂, hsum⟩ := Submodule.mem_sup.mp hw'
    have hw₁D : D w₁ ∈ D₁ := ⟨⟨w₁, hw₁⟩, rfl⟩
    have hw₂D : D w₂ ∈ D₂ := ⟨⟨w₂, hw₂⟩, rfl⟩
    have he : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x) =
        D w₁ + D w₂ := by rw [← hw, ← map_add, hsum]
    change (p.linearCoordinates (Additive.ofMul (QuotientGroup.mk' _ x))).1 ∈ _ ∧
      (p.linearCoordinates (Additive.ofMul (QuotientGroup.mk' _ x))).2 ∈ _
    rw [he, map_add]
    rcases hcu (D w₁) hw₁D with hz | hz <;>
      rcases hfu (D w₂) hw₂D with hzz | hzz <;>
      simp only [hz, hzz, map_zero, Prod.fst_add, Prod.snd_add, Prod.fst_zero,
        Prod.snd_zero, hc₂, hf₁, zero_add, add_zero, Set.mem_insert_iff, Set.mem_singleton_iff,
        true_or, or_true, and_self]

end NaturalPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
