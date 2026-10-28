module
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.GroupTheory.PRadicalSylowNormalizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Sylow-normalized radical intersections in an alternating-five extension

A nontrivial two-radical of A₅ normalized by a Sylow two-subgroup contains
that Sylow subgroup. In a faithful symmetric extension, the centralizer
of an alternating Sylow four-group lies in A₅. Consequently, a nontrivial
subgroup normalized by that Sylow cannot have trivial intersection with
A₅ when the intersection is the two-core of its normalizer.

The application to the original C.2.7 star quotient is in Chapter15's
ComponentModels/Catalogue/AlternatingFive. This gives the five-letter
exclusion in original 15.2.23 (Aschbacher--Smith, pp.1116--1117).
-/

public section
open Subgroup Theory.GroupTheory
namespace alternatingGroup

/-- A nontrivial two-radical of A5 normalized by a full Sylow contains it. -/
theorem sylow_le_radical_of_normalized_five
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (U : Subgroup (alternatingGroup (Fin 5)))
    (hU : IsPRadical 2 U)
    (hP : (P : Subgroup _) ≤ normalizer (U : Set (alternatingGroup (Fin 5)))) :
    (P : Subgroup _) ≤ U := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hproper : normalizer (U : Set (alternatingGroup (Fin 5))) ≠ ⊤ := by
    intro ht
    rcases (normalizer_eq_top_iff.mp ht).eq_bot_or_eq_top with hb | hb
    · exact hU.1 hb
    · have hp : IsPGroup 2 (alternatingGroup (Fin 5)) := by
        have hh : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) := hb ▸ hU.isPGroup
        exact hh.of_surjective topEquiv.toMonoidHom topEquiv.surjective
      let : Group.IsNilpotent (alternatingGroup (Fin 5)) := hp.isNilpotent
      let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance
  rw [←hU.2]
  exact le_pCoreIn_of_normalizes P.isPGroup' hP
    (proper_sylow_overgroup_le_normalizer P _ hproper hP)

variable {D : Type*} [Group D] [Finite D]
/-- In a faithfully marked symmetric extension of A5, the centralizer of
an alternating Sylow four-group is inside the component. -/
theorem sylow_centralizer_le_component_five
    (C : Subgroup D) (e : C ≃* alternatingGroup (Fin 5))
    (f : D →* Equiv.Perm (Fin 5)) (hf : Function.Injective f)
    (hmark : ∀ c : C, f c = (e c : Equiv.Perm (Fin 5)))
    (P : Sylow 2 C) :
    centralizer ((P : Subgroup C).map C.subtype : Set D) ≤ C := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  intro x hx
  let β : MulAut (alternatingGroup (Fin 5)) := MulAut.conjNormal (f x)
  have hfix : ∀ a ∈ Q, β a = a := by
    rintro _ ⟨c,hc,rfl⟩
    apply Subtype.ext
    change f x * (e c : Equiv.Perm (Fin 5)) * (f x)⁻¹ = (e c : Equiv.Perm (Fin 5))
    rw [←hmark c,←map_inv,←map_mul,←map_mul]
    congr 1
    rw [←mem_centralizer_iff.mp hx (c : D) (mem_map_of_mem C.subtype hc),mul_inv_cancel_right]
  obtain ⟨a,_,ha⟩ := Theory.PSL2.SylowFixedQuotients.alternating_sylow_fixed_inner Q β hfix
  have he : f x = (a : Equiv.Perm (Fin 5)) := by
    apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide)).1
    exact ha
  have hxc : x = (e.symm a : C) := hf (by rw [hmark,e.apply_symm_apply,he])
  rw [hxc]
  exact (e.symm a).property

/-- A nontrivial subgroup normalized by an alternating Sylow contains that
Sylow whenever its intersection with the component has radical core. -/
theorem sylow_le_intersection_of_normalized_radical_five
    (C R : Subgroup D) [C.Normal] (e : C ≃* alternatingGroup (Fin 5))
    (f : D →* Equiv.Perm (Fin 5)) (hf : Function.Injective f)
    (hmark : ∀ c : C, f c = (e c : Equiv.Perm (Fin 5)))
    (P : Sylow 2 C) (hne : R ≠ ⊥)
    (hP : (P : Subgroup C).map C.subtype ≤ normalizer (R : Set D))
    (hcore : (normalizer (R.subgroupOf C : Set C)).pCoreIn 2 = R.subgroupOf C) :
    (P : Subgroup C) ≤ R.subgroupOf C := by
  let U := R.subgroupOf C
  have hn : (P : Subgroup C) ≤ normalizer (U : Set C) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hP (mem_map_of_mem C.subtype hx)) (y : D)
  have hU : U ≠ ⊥ := by
    intro he
    have hRC : R ⊓ C = ⊥ := by
      have hh := congrArg (map C.subtype) he
      rwa [subgroupOf_map_subtype,Subgroup.map_bot] at hh
    have hcomm : ⁅R,(P : Subgroup C).map C.subtype⁆ = ⊥ := by
      apply bot_unique
      apply le_trans (le_inf (le_normalizer_iff_commutator_le_left.mp hP)
        ((commutator_mono le_rfl (map_subtype_le _)).trans (commutator_le_right R C))) hRC.le
    have hRC' : R ≤ C := (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (sylow_centralizer_le_component_five C e f hf hmark P)
    exact hne (bot_unique ((le_inf le_rfl hRC').trans hRC.le))
  have hu : IsPRadical 2 U := ⟨hU,hcore⟩
  have hm := sylow_le_radical_of_normalized_five
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) (U.map e.toMonoidHom)
    (hu.map_equiv e) (by rw [←map_equiv_normalizer_eq]; exact map_mono hn)
  exact (map_le_map_iff_of_injective e.injective).mp hm

end alternatingGroup
