module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreE8Orbit
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedConjugateTypes

/-!
# An elementary sixteen contains no original seed eight

An elementary subgroup containing the original seed centralizes that seed.
It therefore lies in the whole cyclic-four normalizer core; its square-one
elements lie in that core's first omega subgroup, the seed itself. The same
argument applies to every actual conjugate seed, excluding the seed orbit
for the point-core eights inside the constructed sixteen.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The original seed is maximal among elementary subgroups containing it. -/
theorem TypeAt.elementary_subgroup_eq_of_seed_le (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hVA : V ≤ A) : A = V := by
  apply le_antisymm ?_ hVA
  intro x hx
  have hxC : x ∈ centralizer (V : Set G) := by
    intro v hv
    exact setLike_mul_comm (hVA hv) hx
  rw [h.seed_centralizer] at hxC
  obtain ⟨r, hr, he⟩ := hxC
  change (r : G) = x at he
  have hr2 : (⟨r, hr⟩ : pCore 2 (normalizer (V : Set G))) ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (r : G) ^ 2 = 1
    rw [he]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hw : r ∈ V.subgroupOf (normalizer (V : Set G)) := by
    rw [h.seed_eq_omega_normalizer_core]
    exact ⟨⟨r, hr⟩, subset_closure hr2, rfl⟩
  exact he ▸ (show (r : G) ∈ V from hw)

/-- Every actual point-core eight contained in an elementary sixteen lies
outside the full original seed orbit. -/
theorem TypeAt.eight_in_sixteen_not_seed (h : TypeAt z V)
    (E : pointCoreEights z) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hEA : E.val ≤ A) :
    E.val ∉ pointCoreSeedOrbit z V := by
  rintro ⟨g, hg⟩
  change V.map (MulAut.conj (g : G)).toMonoidHom = E.val at hg
  let hT := h.conj (g : G)
  have he := hT.elementary_subgroup_eq_of_seed_le A (by rw [hg]; exact hEA)
  have hh := congrArg (fun S : Subgroup G => Nat.card S) he
  rw [hA, hT.seed_card] at hh
  omega

end CFSG.Quasithin.HigmanSims
