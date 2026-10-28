module
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.CubicRatio
/-!
# Quadratic ratios in binary dimension at most four

For a non-FF action, an involution displaces at least two dimensions.
A quadratic actor fixes that displacement space, so its fixed codimension
is at most two. The non-offender inequality therefore forces actor rank one
and fixed codimension two. A finite cubic ratio supplies an involution and
hence attains the quadratic ratio two.

Source application: Aschbacher--Smith15.1.8, printed p.1088, the natural
four-dimensional Ω alternative. The argument uses no model enumeration.
-/
public section
open Subgroup
open scoped ENNReal
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
theorem quadratic_actor_four_of_no_ff (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V ≤ 4) (hn : ¬ IsFFModule ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A) :
    rank A = 1 ∧ fixedCodim ρ A = 2 := by
  let := hA.2
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
  have ho : orderOf (a : G) = 2 := orderOf_eq_prime (show (a : G)^2=1 from
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a)) (fun h => ha (Subtype.ext h))
  obtain ⟨hC,hCr,hCq,hbound⟩ := involution_actor_rank_and_fixedCodim ρ a ho
  have hlo : 2 ≤ fixedCodim ρ (zpowers (a : G)) := by
    by_contra! hh
    apply hn
    exact ⟨zpowers (a : G),hC,by omega⟩
  have hle : LinearMap.range (ρ (a : G) - LinearMap.id) ≤ fixedSpace ρ A := by
    rintro v ⟨w,rfl⟩ b
    exact hq b b.property a a.property w
  have hf := Submodule.finrank_mono hle
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hf
  have hsum := fixedCodim_add_finrank ρ A
  have hlow : rank A < fixedCodim ρ A := by
    by_contra! hh
    exact hn ⟨A,hA,hh⟩
  have hr := hA.rank_pos
  omega

theorem two_le_quadraticRatio_of_four_no_ff (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V ≤ 4) (hn : ¬ IsFFModule ρ) :
    2 ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  obtain ⟨hr,hc⟩ := quadratic_actor_four_of_no_ff ρ hdim hn hA hq
  simp only [actionRatio,hr,hc,Nat.cast_one,div_one,Nat.cast_ofNat,le_refl]

theorem quadraticRatio_eq_two_of_four_cubic
    (ρ : Representation (ZMod 2) G V) (hdim : Module.finrank (ZMod 2) V ≤ 4)
    (hlo : 1 < cubicRatio ρ) (hhi : cubicRatio ρ ≤ 2) : quadraticRatio ρ = 2 := by
  apply le_antisymm
  · obtain ⟨A,hA,_,_⟩ := (cubicRatio_le_nat_iff ρ 2).mp hhi
    let := hA.2
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
    have ho : orderOf (a : G) = 2 := orderOf_eq_prime (show (a : G)^2=1 from
      congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a)) (fun h => ha (Subtype.ext h))
    exact quadraticRatio_le_two_of_finrank_le_four ρ a ho hdim
  · exact two_le_quadraticRatio_of_four_no_ff ρ hdim
      (fun h => not_le_of_gt hlo ((isFFModule_iff_cubicRatio_le_one ρ).mp h))
end Representation.BinaryOffender
