module

public import Theory.GroupTheory.WreathedThirtyTwoResidual
public import Theory.GroupTheory.QuasisimpleOddCenterSylow
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.Covers
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.AbelianSixteenSource
public import FeitThompson.FinalTheorem

/-!
# The wreathed source component is the whole group

The proved ABG wreathed fusion theorem leaves four possibilities for the
actual two-residual. Quasisimplicity excludes odd order; its odd center
excludes quaternion Sylow subgroups by Brauer--Suzuki. The remaining proper
case has Sylow C4 times C4, which the complete earlier Chapter C catalogue
excludes on the literal central quotient. Thus Fstar is the whole group.

Source: Aschbacher--Smith F.6.18(10), printed pp.309--310; ABG II.1
Proposition 2. No component-model, local-action, or outer-index hypothesis
is added to the original source quotient and residual inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
private theorem component_top_or_abelian_sixteen (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G)
    (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo) :
    generalizedFitting G = ⊤ ∨
      ∃ P : Sylow 2 (generalizedFitting G ⧸ center (generalizedFitting G)),
        Nonempty (P ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let K := generalizedFitting G
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hZ := component_center_odd_of_primeToThree_quotient eG hK
  have hc := wreathedThirtyTwo_twoResidual_cases S eS
  rw [hres] at hc
  rcases hc with ht | ho | hq | ⟨R, ⟨a⟩⟩
  · exact Or.inl ht
  · exact (Group.IsPerfect.not_isSolvable K (odd_order_theorem K ho)).elim
  · exact (not_quaternion_sylow_of_quasisimple_odd_center hZ hq).elim
  · let P : Sylow 2 (K ⧸ center K) := default
    let b := Sylow.equivOfSurjectiveCoprime (QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']; exact Nat.coprime_two_left.mpr hZ) R P
    exact Or.inr ⟨P, ⟨b.symm.trans a⟩⟩

universe u
/-- The genuine wreathed source branch has no proper quasisimple residual. -/
theorem component_top_of_wreathed_source
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H] {κ : GroupClass.{u}}
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hH : IsSQTK κ H) (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G)
    (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo) : generalizedFitting G = ⊤ := by
  rcases component_top_or_abelian_sixteen eG hK hres S eS with ht | ⟨P, ⟨a⟩⟩
  · exact ht
  · exact (ComponentSieve.AbelianSixteen.not_component_central_quotient_sylow
      hA hC hH eG hK P a).elim

end CFSG.Quasithin.ChapterF.SourceAssembly
