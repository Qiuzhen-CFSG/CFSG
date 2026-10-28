module

public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.PGroupCore

/-!
# Transport of solvability of proper Sylow overgroups

The property transports along an actual isomorphism and lifts through the
two-core quotient. For the latter, the kernel lies in the given full Sylow,
so a proper Sylow overgroup still has proper image. Solvability then lifts
through the two-group kernel.

Source application: Aschbacher–Smith A.3.12 and 2.4.6, printed pp.47–48,528.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Transport the proper Sylow-overgroup calculation through a concrete model. -/
theorem isSolvable_proper_sylow_overgroup_of_equiv
    (e : G ≃* H)
    (hproper : ∀ (S : Sylow 2 H) (P : Subgroup H),
      (S : Subgroup H) ≤ P → P ≠ ⊤ → Group.IsSolvable P)
    (S : Sylow 2 G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hne : P ≠ ⊤) : Group.IsSolvable P := by
  have him : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hne
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [he, map_top_of_surjective _ e.surjective]
  let := hproper (S.mapSurjective e.surjective) (P.map e.toMonoidHom)
    (map_mono hSP) him
  exact Group.isSolvable_of_isSolvable_injective
    (f := (P.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
    (P.equivMapOfInjective e.toMonoidHom e.injective).injective

/-- Proper Sylow overgroups remain proper modulo the actual two-core. -/
theorem isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    (hproper : ∀ (S : Sylow 2 (G ⧸ pCore 2 G)) (P : Subgroup (G ⧸ pCore 2 G)),
      (S : Subgroup _) ≤ P → P ≠ ⊤ → Group.IsSolvable P)
    (S : Sylow 2 G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hne : P ≠ ⊤) : Group.IsSolvable P := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hNP : pCore 2 G ≤ P := (pCore_isPGroup.le_sylow_of_normal S).trans hSP
  have hpre : (P.map q).comap q = P := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNP]
  have him : P.map q ≠ ⊤ := by
    intro he
    rw [he, comap_top] at hpre
    exact hne hpre.symm
  let := pCore_isNilpotent (p := 2) (G := G)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let := hproper (S.mapSurjective (QuotientGroup.mk'_surjective _)) (P.map q)
    (map_mono hSP) him
  have hs := isSolvable_comap_of_solvable_ker q (P.map q)
  rwa [hpre] at hs

end Subgroup
