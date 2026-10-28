module
public import Theory.Representation.BinaryOffender.QuadraticPairPermutation

/-!
# Large exchanged supports exceed a quadratic actor's budget

A faithful pair of disjoint supports, together with a fixed supplement, is
enough to apply the quadratic swapping-actor theorem. A swapping actor then
has rank one, while its fixed codimension is at least the dimension of either
support. Thus supports of dimension greater than two must be preserved.

Source: Aschbacher--Smith 14.6.24(3), first paragraph after (b), p.1039.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- A quadratic actor within the source budget fixes both large supports;
the ambient module may also have a fixed supplement. -/
theorem quadratic_preserves_large_pair
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (I J : Submodule (ZMod 2) V) (hd : Disjoint I J)
    (hspan : I ⊔ J ⊔ fixedSpace ρ ⊤ = ⊤)
    (hlarge : 2 < Module.finrank (ZMod 2) I)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hq : IsQuadratic ρ A)
    (hbudget : fixedCodim ρ A ≤ 2 * rank A)
    (hperm : ∀ a ∈ A,
      (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I)) :
    ∀ a ∈ A, I.map (ρ a) = I ∧ J.map (ρ a) = J := by
  have hfaith (b : G) (hb : ∀ v ∈ I ⊔ J, ρ b v = v) : b = 1 := by
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ I ⊔ J ⊔ fixedSpace ρ ⊤ := by rw [hspan]; trivial
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    have hz' : ρ b z = z := hz ⟨b,mem_top b⟩
    rw [map_add,hb w hw,hz',map_one,Module.End.one_apply]
  have hI : I ≠ ⊥ := by
    intro he
    rw [he] at hlarge
    simp at hlarge
  intro a ha
  rcases hperm a ha with hs | hs
  · exact hs
  · have hr := (quadratic_swapping_actor_rank ρ I J hfaith A hq hd hI
        (fun b hb => (hperm b hb).imp And.left And.left) a ha hs).2
    have hl := finrank_le_fixedCodim_of_disjoint_map ρ I ha (by rwa [hs.1])
    rw [hr] at hbudget
    omega

end Representation.BinaryOffender
