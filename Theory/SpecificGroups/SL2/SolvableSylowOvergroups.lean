module

public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Solvable proper Sylow overgroups in characteristic-two rank one

A proper subgroup of SL₂ containing a full Sylow two-subgroup lies in a
conjugate of the triangular Borel and is solvable. The same obstruction
forces a nonsolvable Sylow overgroup in a C-component cover to be the whole
cover when its quotient by the two-core is quasisimple. The kernel of the
actual map is solvable by C-component minimality; the radical supplement
argument then recovers the original subgroup, including its two-core.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, the rank-one case, and
the corresponding rank-one rigidity argument in 13.6.18, printed p.931.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup

/-- Every proper overgroup of a full Sylow two-subgroup of characteristic-two
SL₂ is solvable. No field-size or simplicity assumption is needed. -/
theorem isSolvable_of_proper_sylow_overgroup
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (S : Sylow 2 (SL(2, F))) (M : Subgroup (SL(2, F)))
    (hSM : (S : Subgroup _) ≤ M) (hne : M ≠ ⊤) : Group.IsSolvable M := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, F)) (upperUnipotentSylow F 2) S
  let e := MulAut.conj g
  let D := M.comap e.toMonoidHom
  have hUD : upperUnipotent F ≤ D := by
    intro u hu
    apply hSM
    rw [← hg]
    exact mem_map.mpr ⟨u, hu, rfl⟩
  have hD : D ≠ ⊤ := by
    intro ht
    apply hne
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    simpa only [D, map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
  have hDB := overgroup_le_rankOneBorel hUD hD
  let : Group.IsSolvable (rankOneBorel F) :=
    Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sylow_normalizer
      2 F (by decide) (upperUnipotentSylow F 2)
  let : Group.IsSolvable D :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hDB)
  exact Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupComap_surjective_of_surjective M e.surjective)

private theorem component_kernel_solvable {A X : Type*} [Group A] [Finite A]
    [Group X] [Nontrivial X] (hA : (⊤ : Subgroup A).IsCComponent)
    (f : A →* X) (hf : Function.Surjective f) : Group.IsSolvable f.ker := by
  let e : (⊤ : Subgroup A) ≃* A := topEquiv
  have hp : f.ker ≠ ⊤ := by
    intro ht
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    obtain ⟨a, rfl⟩ := hf x
    exact hx (show a ∈ f.ker from ht.symm ▸ mem_top a)
  have hp' : f.ker.comap e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hp
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
  let := hA.isSolvable_of_subnormal_lt_top
    ((inferInstance : f.ker.Normal).isSubnormal.comap e.toMonoidHom) hp'
  exact Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupComap_surjective_of_surjective f.ker e.surjective)

/-- In a C-component cover with quasisimple quotient by its actual two-core,
a nonsolvable overgroup of the full Sylow is the whole group. The map to
SL₂ is literal and its kernel is proved solvable internally. -/
theorem sylow_overgroup_eq_top_of_component_cover
    {A F : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [Field F] [Finite F] [CharP F 2]
    [IsQuasisimple (A ⧸ pCore 2 A)]
    (hA : (⊤ : Subgroup A).IsCComponent)
    (f : A →* SL(2, F)) (hf : Function.Surjective f)
    (S : Sylow 2 A) (H : Subgroup A) (hSH : (S : Subgroup A) ≤ H)
    (hH : ¬ Group.IsSolvable H) : H = ⊤ := by
  let : Nontrivial (SL(2, F)) := ⟨⟨transvection
    (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F), 1, by
      intro he
      have hh := congrArg (fun g : SL(2, F) => g.val 0 1) he
      simp [transvection_coe] at hh⟩⟩
  let := component_kernel_solvable hA f hf
  have him : H.map f = ⊤ := by
    by_contra hne
    let := isSolvable_of_proper_sylow_overgroup (S.mapSurjective hf) (H.map f)
      (map_mono hSH) hne
    let := isSolvable_comap_of_solvable_ker f (H.map f)
    exact hH (Group.isSolvable_of_isSolvable_injective
      (f := inclusion (le_comap_map f H)) (inclusion_injective _))
  have hgen : solvableRadical A ⊔ H = ⊤ := by
    have hcover : H ⊔ f.ker = ⊤ := by
      have hm := congrArg (comap f) him
      simpa only [comap_map_eq, comap_top] using hm
    apply top_unique
    rw [← hcover]
    exact sup_le le_sup_right
      ((le_solvableRadical f.ker inferInstance inferInstance).trans le_sup_left)
  have hQH : pCore 2 A ≤ H := (pCore_isPGroup.le_sylow_of_normal S).trans hSH
  exact eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 A) H (hQH.trans H.le_normalizer) hgen

end Matrix.SpecialLinearGroup
