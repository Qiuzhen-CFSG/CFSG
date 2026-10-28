module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Assembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.ExceptionalComponent

/-!
# The prime PSL2 component from the actual exceptional-vertex branch

For the oriented component of the original SQTK quotient, the source local
argument constructs the small elementary Sylow subgroup and excludes J1
and PSL2(8). Theorems A and C provide the literal central quotient model
from the original cover. The complete catalogue sieve therefore supplies
an actual prime-field PSL2 model, with the required congruence modulo eight.
No component recognition or model-output hypothesis is assumed.

Source: Aschbacher--Smith F.6.17--18, printed pp.309--310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

/-- The earlier A/C source inputs give the odd prime model on the original
oriented component in every branch with an exceptional vertex. -/
theorem SingleResidualComponent.prime_psl2_of_either_exceptional
    (d : SingleResidualComponent G₁ G₂)
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (d.component ⧸ center d.component))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨ generalizedFitting G₂ ≠ pCore 2 G₂) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p := by
  obtain ⟨_, _, _, hs, ⟨P, he, hP⟩, hnJ, hn8⟩ :=
    d.exceptional_component_data e h hcore hbad
  let : IsSimpleGroup (d.component ⧸ center d.component) := hs
  let : IsElementaryAbelian 2 P := he
  let : IsQuasisimple d.component := d.isComponent.2
  let : Group.IsPerfect (d.component ⧸ center d.component) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center d.component))
  have hm := component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) d.isComponent
  rcases theoremC_model_of_small_elementary_sylow P hP
    (Group.IsPerfect.not_isSolvable _) hm with hm | hm | hm
  · exact hm
  · exact (hn8 hm).elim
  · exact (hnJ hm).elim

end CFSG.Quasithin.ChapterF.SourceAssembly
