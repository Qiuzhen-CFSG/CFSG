module

public import Theory.Representation.ElementaryCentralQuotient
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Lifting binary involution generation through a perfect central cover

Let a finite perfect group act faithfully and irreducibly in characteristic
two. A nonidentity involution remains nonidentity in the central quotient:
a central involution would belong to the representation kernel. Lift a
family of generating conjugates from that quotient. The generated subgroup
surjects onto the quotient, hence equals the perfect covering group.

This preserves the number of conjugates and does not require a trivial
center or absolute irreducibility. The application is the degree estimate
(2.6) in Guralnick--Malle, Classification of 2F-modules I, manuscript p.4.
-/

public section
namespace Representation.BinaryOffender
open Subgroup PerfectCentralCovering

/-- Generation by a fixed number of involution conjugates lifts from the
specified central quotient of a faithful irreducible binary perfect actor. -/
theorem conjugate_generation_of_central_quotient
    {G S V : Type*} [Group G] [Finite G] [Group.IsPerfect G] [Group S]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (e : G ⧸ center G ≃* S) {n : ℕ}
    (hgen : ∀ t : S, t ≠ 1 → t ^ 2 = 1 →
      ∃ c : Fin n → S, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤)
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ c : Fin n → G, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker ≤ center G := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact hx.trans e.map_one.symm
  have hqt : q t ≠ 1 := fun h => ht (central_eq_one_of_pow_prime ρ hf (hker h) ht2)
  obtain ⟨c, hc⟩ := hgen (q t) hqt (by rw [← map_pow, ht2, map_one])
  choose d hd using fun i => hq (c i)
  refine ⟨d, ?_⟩
  let H := closure (Set.range fun i => d i * t * (d i)⁻¹)
  have hmap : H.map q = ⊤ := by
    change (Subgroup.closure _).map q = ⊤
    rw [MonoidHom.map_closure]
    have he : q '' Set.range (fun i => d i * t * (d i)⁻¹) =
        Set.range (fun i => c i * q t * (c i)⁻¹) := by
      rw [← Set.range_comp]
      simp only [Function.comp_def, map_mul, map_inv, hd]
    rw [he, hc]
  have hcomp : Function.Surjective (q.comp H.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, hmap]
  have hs := surjective_of_comp_surjective_of_ker_le_center_of_isPerfect q H.subtype hcomp hker
  simpa only [← MonoidHom.range_eq_top, range_subtype] using hs

end Representation.BinaryOffender
