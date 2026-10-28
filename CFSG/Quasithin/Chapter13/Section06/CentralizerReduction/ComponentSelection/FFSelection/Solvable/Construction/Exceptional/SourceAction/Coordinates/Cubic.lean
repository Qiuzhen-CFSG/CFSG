module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Six
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Plane

/-!
# The full ambient action on the original cubic plane

Every binary plane action has three-point coordinates. Faithfulness of the
original cubic on its moved plane identifies the action kernel: a kernel
element centralizes that cubic, hence lies in A₆C₃; crossed fixation and cubic
faithfulness reduce it to A₆. The six-point quotient gives the ambient order,
so the image is all of S₃. The cubic has odd order, and therefore the even
fiber is exactly the original product A₆C₃.

Source: Aschbacher–Smith, B.5.7, printed p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
open ChapterB.SourceInduction
universe u v
variable {G : Type u} [Group G] [Finite G]
variable (c : ChapterB.OuterSixThreeShape G)
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The original cubic plane supplies a full S₃ projection. Its kernel is
exactly the original A₆, and its even fiber is the product of the two factors. -/
theorem cubic_coordinates (hyp : FFHypothesis K ρ) (d : Recovered c ρ) :
    Nonempty (CubicCoordinates c ρ) := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  let : c.second.Normal := second_normal c
  let U := secondMoved c ρ
  let τ := U.toRepresentation
  obtain ⟨f, b, hb, hf⟩ := plane_permutation_coordinates τ d.plane
  have hfaith : Function.Injective (τ.comp c.second.subtype) := second_moved_faithful c ρ hyp
  have hfirst (l : G) (hl : l ∈ c.first) : τ l = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact d.second_fixed w.property ⟨l, hl⟩
  have hker : f.ker = c.first := by
    apply le_antisymm
    · intro g hg
      have hτg : τ g = 1 := (hf g).mp hg
      have hc : g ∈ centralizer (c.second : Set G) := by
        intro x hx
        have hconj := (inferInstance : c.second.Normal).conj_mem x hx g
        have he : (⟨g * x * g⁻¹, hconj⟩ : c.second) = ⟨x, hx⟩ := by
          apply hfaith
          change τ (g * x * g⁻¹) = τ x
          have hi : τ g⁻¹ = 1 := by
            have hh := τ.map_mul g g⁻¹
            simpa [hτg] using hh.symm
          rw [map_mul, map_mul, hτg, hi, one_mul, mul_one]
        have he' := congrArg (fun y : c.second => (y : G) * g) he
        simpa [mul_assoc] using he'.symm
      rw [d.cubic_centralizer] at hc
      obtain ⟨l, hl, x, hx, rfl⟩ := mem_sup_of_normal_right.mp hc
      have hτx : τ x = 1 := by simpa [map_mul, hfirst l hl] using hτg
      have hx1 : (⟨x, hx⟩ : c.second) = 1 := by
        apply hfaith
        change τ x = τ 1
        rw [map_one]
        exact hτx
      have hx' : x = 1 := congrArg Subtype.val hx1
      simpa [hx'] using hl
    · intro l hl
      exact (hf l).mpr (hfirst l hl)
  obtain ⟨s⟩ := six_coordinates c ρ d
  have hG : Nat.card G = 2160 := by
    have hh := s.projection.ker.card_mul_index
    rw [index_ker, s.kernel, second_card c,
      MonoidHom.range_eq_top.mpr s.surjective, card_top, Nat.card_perm] at hh
    norm_num [Nat.factorial] at hh
    exact hh.symm
  have hL : Nat.card c.first = 360 := by
    rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hsurj : Function.Surjective f := by
    apply f.surjective_of_card_ker_le_div
    rw [hker, hL, hG, Nat.card_perm]
    norm_num [Nat.factorial]
  have hfle : c.first ≤ (alternatingGroup (Fin 3)).comap f := by
    intro l hl
    change f l ∈ alternatingGroup (Fin 3)
    rw [show f l = 1 from (show l ∈ f.ker from hker.symm ▸ hl)]
    exact one_mem _
  have hxle : c.second ≤ (alternatingGroup (Fin 3)).comap f := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : c.second))
      rw [second_card c] at hh
      exact congrArg Subtype.val hh
    have hs3 : (Equiv.Perm.sign (f x)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hx3, map_one, map_one]
    change Equiv.Perm.sign (f x) = 1
    rcases Int.units_eq_one_or (Equiv.Perm.sign (f x)) with h | h
    · exact h
    · rw [h] at hs3
      norm_num at hs3
  have heven : (alternatingGroup (Fin 3)).comap f = c.first ⊔ c.second := by
    apply (eq_of_le_of_card_ge (sup_le hfle hxle) ?_).symm
    have hcard := ((alternatingGroup (Fin 3)).comap f).card_mul_index
    rw [index_comap_of_surjective _ hsurj, alternatingGroup.index_eq_two, hG] at hcard
    have hprod : Nat.card (c.first ⊔ c.second : Subgroup G) = 1080 := by
      rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod, hL, second_card c]
    rw [hprod]
    omega
  exact ⟨⟨f, hsurj, hker, heven, b, hb⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
