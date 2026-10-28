module
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions

/-!
# Sylow-overgroup uniqueness from a top C-component

A group whose top subgroup is a C-component has only that C-component.
Consequently the uniqueness test reduces to proper Sylow overgroups, including
when the whole group is a central cover rather than simple. Conjugate parabolic
coverage then reduces it to the same test in each parabolic.
Source application: Aschbacher--Smith A.3.12 and C.2.7, pp.47--48,145--147.
-/
public section
open Subgroup
namespace Theory.GroupTheory.SylowOvergroupComponentUnique
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- With a top C-component, only proper Sylow overgroups need inspection. -/
theorem of_top_component_and_proper
    (htop : (⊤ : Subgroup G).IsCComponent)
    (h : ∀ (S : Sylow 2 G) (P : Subgroup G), (S : Subgroup G) ≤ P → P ≠ ⊤ →
      ∀ B C : Subgroup P, B.IsCComponent → C.IsCComponent → B = C) :
    SylowOvergroupComponentUnique G := by
  intro S P hSP B C hB hC
  by_cases ht : P = ⊤
  · subst P
    exact (htop.eq_top_of_isCComponent hB).trans (htop.eq_top_of_isCComponent hC).symm
  · exact h S P hSP ht B C hB hC

omit [Finite G] in
/-- Solvable proper Sylow overgroups give uniqueness in a group with a top component. -/
theorem of_top_component_and_solvable_proper
    (htop : (⊤ : Subgroup G).IsCComponent)
    (h : ∀ (S : Sylow 2 G) (P : Subgroup G), (S : Subgroup G) ≤ P → P ≠ ⊤ →
      Group.IsSolvable P) : SylowOvergroupComponentUnique G := by
  apply of_top_component_and_proper htop
  intro S P hSP hP B _ hB _
  let := h S P hSP hP
  exact (hB.not_isSolvable inferInstance).elim

/-- Exhaustive conjugate parabolic placement supplies the proper-overgroup test. -/
theorem of_top_component_and_conjugate_cover
    (htop : (⊤ : Subgroup G).IsCComponent)
    (h : ∀ (S : Sylow 2 G) (P : Subgroup G), (S : Subgroup G) ≤ P → P ≠ ⊤ →
      ∃ (g : G) (J : Subgroup G), P.map (MulAut.conj g).toMonoidHom ≤ J ∧
        SylowOvergroupComponentUnique J) : SylowOvergroupComponentUnique G := by
  apply of_top_component_and_proper htop
  intro S P hSP hP B C hB hC
  obtain ⟨g,J,hPJ,hJ⟩ := h S P hSP hP
  let e := (MulAut.conj g).subgroupMap P
  apply map_injective (f := e.toMonoidHom) e.injective
  exact eq_of_le_overgroup (S.mapSurjective (MulAut.conj g).surjective)
    (map_mono hSP) hPJ hJ (hB.map_equiv e) (hC.map_equiv e)

end Theory.GroupTheory.SylowOvergroupComponentUnique
