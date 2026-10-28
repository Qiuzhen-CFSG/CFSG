module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Certificates
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PGroup.GeneratorSeries
import Mathlib.Tactic.FinCases

/-!
# The elementary subgroup and its two marked normalizing elements

Four commuting involutions generate the translation two-subgroup. The two
marked cubic elements commute, and their conjugation of each translation
generator is a short translation word. The scalar also commutes with both
generators of the right support. Each permutation equation is checked on all
6156 letters; membership and normalization follow from subgroup closure.

Source: GLS, Number 3, Table 5.3h, printed p.269, the affine local on F₄²;
Aschbacher--Smith A.2.19, printed p.41. No local identification or covering
assertion is assumed here.
-/

namespace Sporadic.Janko3.ThreeCoverConfig
open Theory.GroupTheory OrderCertificate TwoLocal
open Subgroup
set_option maxRecDepth 40000
set_option Elab.async false

public theorem qWord_mem (w : List (Fin 4)) :
    evalWord elementaryGenerator w ∈ twoSubgroup := by
  induction w with
  | nil => exact twoSubgroup.one_mem
  | cons i w ih => exact twoSubgroup.mul_mem (elementaryGenerator_mem i) ih

/-- The actual marked translation subgroup is elementary abelian. -/
public instance two_elementary : IsElementaryAbelian 2 twoSubgroup := by
  let : IsMulCommutative (closure (Set.range elementaryGenerator)) :=
    isMulCommutative_closure (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (elementary_commute i j).eq)
  exact IsElementaryAbelian.closure_of_isMulCommutative _ (by
    rintro _ ⟨i, rfl⟩
    exact elementary_square i)

public theorem two_isPGroup : IsPGroup 2 twoSubgroup :=
  IsElementaryAbelian.isPGroup 2 twoSubgroup

public theorem two_nontrivial : twoSubgroup ≠ ⊥ := by
  intro h
  have he : elementaryGenerator 0 = 1 := mem_bot.mp (h ▸ elementaryGenerator_mem 0)
  have hv := congrArg (fun g : Model => (g : Equiv.Perm (Fin 6156)) 0) he
  change (elementaryGenerator 0 : Equiv.Perm (Fin 6156)) 0 = 0 at hv
  have hn : qPerm 0 0 ≠ 0 := by decide +kernel
  apply hn
  simpa only [qPerm_eq] using hv

public theorem x_centralizes_right : x ∈ centralizer (rightSupport : Set Model) := by
  rw [rightSupport, centralizer_closure]
  intro z hz
  rcases hz with rfl | hz
  · exact xd0.symm.eq
  · have he : z = d1 := hz
    subst z
    exact xd1.symm.eq

public theorem x_normalizes : x ∈ normalizer (twoSubgroup : Set Model) := by
  apply mem_normalizer_closure_of_conjugates
  rintro _ ⟨i, rfl⟩
  rw [x_conj_elementary]
  exact qWord_mem _

public theorem y_normalizes : y ∈ normalizer (twoSubgroup : Set Model) := by
  apply mem_normalizer_closure_of_conjugates
  rintro _ ⟨i, rfl⟩
  rw [y_conj_elementary]
  exact qWord_mem _

end Sporadic.Janko3.ThreeCoverConfig
