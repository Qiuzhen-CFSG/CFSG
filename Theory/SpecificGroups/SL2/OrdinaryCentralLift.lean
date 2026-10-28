module
public import Theory.GroupTheory.CentralExtensionSections
public import Theory.GroupTheory.PerfectCentralizerLift
public import GorensteinWalter.PSL2SchurMultiplier

/-!
# Lifting ordinary SL₂ subgroups and their full centralizers

Outside field orders three and nine, the actual odd SL₂ projection is a
universal cover. Apply its central-extension section theorem to the literal
preimage of a prescribed faithful SL₂ subgroup. The section gives a faithful
lift with the prescribed projection. Since SL₂ is perfect, the kernel's
centrality gives equality of full centralizer preimages and hence images.

There is no restriction on the primes dividing the central kernel.
Source: Aschbacher–Smith A.2.17, printed p.39, and I.1.3, printed p.407.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Field F] [Finite F]

/-- The universal odd SL₂ cover lifts any prescribed embedding through a
finite central extension, outside field orders three and nine. -/
public theorem exists_ordinary_central_lift
    (hF : Odd (Nat.card F)) (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (π : G →* H) (hπ : Function.Surjective π) (hc : π.ker ≤ center G)
    (j : SL(2,F) →* H) (hj : Function.Injective j) :
    ∃ k : SL(2,F) →* G, Function.Injective k ∧ π.comp k = j := by
  let : Fact (3 < Nat.card F) := ⟨hgt⟩
  let P := j.range.comap π
  let e := MonoidHom.ofInjective hj
  let q₀ : P →* j.range := π.subgroupComap j.range
  let q : P →* SL(2,F) := e.symm.toMonoidHom.comp q₀
  have hq (x : P) : j (q x) = π x := congrArg Subtype.val (e.apply_symm_apply (q₀ x))
  have hqs : Function.Surjective q :=
    e.symm.surjective.comp (π.subgroupComap_surjective_of_surjective j.range hπ)
  have hqc : q.ker ≤ center P := by
    intro x hx
    have hh : (x : G) ∈ π.ker := by
      change π x = 1
      rw [← hq, MonoidHom.mem_ker.mp hx, map_one]
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp (hc hh) y)
  obtain ⟨s,hs⟩ := CentralExtension.exists_section_of_universal_cover
    (GorensteinWalter.PSL2Cover.cover F)
    (GorensteinWalter.PSL2Cover.isUniversal_of_odd F hF h9) q hqs hqc
  have hqs' (x) : q (s x) = x := DFunLike.congr_fun hs x
  have hsi : Function.Injective s := by
    intro x y h
    simpa only [hqs'] using congrArg q h
  refine ⟨P.subtype.comp s, P.subtype_injective.comp hsi, ?_⟩
  ext x
  change π (s x) = j x
  rw [← hq,hqs']

/-- Perfectness gives the exact image of the full centralizer of the lifted
SL₂. No defining-prime condition on the central kernel is necessary. -/
public theorem exists_ordinary_lift_centralizer_image
    (hF : Odd (Nat.card F)) (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (π : G →* H) (hπ : Function.Surjective π) (hc : π.ker ≤ center G)
    (j : SL(2,F) →* H) (hj : Function.Injective j) :
    ∃ k : SL(2,F) →* G, Function.Injective k ∧ π.comp k = j ∧
      (centralizer (k.range : Set G)).map π = centralizer (j.range : Set H) := by
  obtain ⟨k,hk,hfac⟩ := exists_ordinary_central_lift hF hgt h9 π hπ hc j hj
  let : Fact (3 < Nat.card F) := ⟨hgt⟩
  let : Group.IsPerfect k.range := Group.IsPerfect.ofSurjective k.rangeRestrict_surjective
  have hm : k.range.map π = j.range := by
    rw [MonoidHom.map_range,hfac]
  have hp := Subgroup.comap_centralizer_map_eq_of_perfect π k.range
    (hc.trans (center_le_centralizer _))
  rw [hm] at hp
  refine ⟨k,hk,hfac,?_⟩
  rw [← hp,Subgroup.map_comap_eq_self_of_surjective hπ]
end Matrix.SpecialLinearGroup
