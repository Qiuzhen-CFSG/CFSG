module

public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Mathlib.GroupTheory.IsPerfect

/-!
# Involutions in quotients of degree-two linear groups

Let G embed in GL₂ over a field of characteristic different from two, and
let G surject onto H with kernel of exponent dividing three. An involution
in H′ lifts inside G′: cube any derived lift to remove its square in the
kernel. The determinant of that lift is one, so its matrix is -I. Consequently
H′ has at most one involution, as does every perfect subgroup of H.

This retains the central involution of the SL₂ block through the odd scalar
quotient in the centralizers of PSL₃ and PSU₃ involutions. Source:
Aschbacher--Smith, A.3.21(a), p.55, used in 15.3.38, p.1137.
-/

public section
open Subgroup Matrix
namespace Matrix.GeneralLinearGroup.CubeKernel

/-- The derived subgroup of a quotient through a kernel of exponent three
has at most one involution when the covering group embeds in odd-characteristic GL₂. -/
theorem derived_involutions_eq {G H F : Type*} [Group G] [Group H] [Field F]
    (hF : (2 : F) ≠ 0) (f : G →* H) (hf : Function.Surjective f)
    (hker : ∀ g ∈ f.ker, g ^ 3 = 1)
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    {x y : H} (hx : x ∈ commutator H) (hy : y ∈ commutator H)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) : x = y := by
  have hmap : (commutator G).map f = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    rfl
  have lift (z : H) (hz : z ∈ commutator H) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
      ∃ u : G, f u = z ∧ ρ u = -1 := by
    obtain ⟨v, hv, hvz⟩ := show z ∈ (commutator G).map f by rwa [hmap]
    have hv6 : (v ^ 3) ^ 2 = 1 := by
      have hh := hker (v ^ 2) (by simp only [MonoidHom.mem_ker, map_pow, hvz, hz2])
      simpa only [← pow_mul] using hh
    have he : f (v ^ 3) = z := by rw [map_pow, pow_succ, hvz, hz2, one_mul]
    have hd : (ρ (v ^ 3)).det = 1 :=
      Abelianization.commutator_subset_ker (GeneralLinearGroup.det.comp ρ)
        ((commutator G).pow_mem hv 3)
    have hs : ρ (v ^ 3) ^ 2 = 1 := by rw [← map_pow, hv6, map_one]
    refine ⟨v ^ 3, he, ?_⟩
    apply (GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF _ hs hd).resolve_left
    intro hh
    have hh' : v ^ 3 = 1 := hρ (hh.trans ρ.map_one.symm)
    exact hz1 (by rw [← he, hh', map_one])
  obtain ⟨u, hu, hur⟩ := lift x hx hx2 hx1
  obtain ⟨v, hv, hvr⟩ := lift y hy hy2 hy1
  exact hu.symm.trans ((congrArg f (hρ (hur.trans hvr.symm))).trans hv)


/-- Every perfect subgroup of the same quotient has at most one involution. -/
theorem perfect_involutions_eq {G H K F : Type*} [Group G] [Group H] [Group K]
    [Group.IsPerfect K] [Field F]
    (hF : (2 : F) ≠ 0) (f : G →* H) (hf : Function.Surjective f)
    (hker : ∀ g ∈ f.ker, g ^ 3 = 1)
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (j : K →* H) (hj : Function.Injective j)
    {x y : K} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) : x = y := by
  have hcomm (z : K) : j z ∈ commutator H := by
    have hm : (commutator K).map j ≤ commutator H := by
      rw [map_commutator_eq]
      exact commutator_mono le_top le_top
    exact hm ⟨z, Group.IsPerfect.mem_commutator, rfl⟩
  apply hj
  exact derived_involutions_eq hF f hf hker ρ hρ (hcomm x) (hcomm y)
    (by rw [← map_pow, hx2, map_one]) (fun h => hx1 (hj (h.trans j.map_one.symm)))
    (by rw [← map_pow, hy2, map_one]) (fun h => hy1 (hj (h.trans j.map_one.symm)))

end Matrix.GeneralLinearGroup.CubeKernel
