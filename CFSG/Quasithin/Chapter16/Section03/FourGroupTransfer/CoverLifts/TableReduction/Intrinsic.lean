module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.Inputs
public import Theory.GroupAction.PerfectCentralQuotient
/-!
# Restricting the actual enlargement action to its component

Every nonidentity actor has L as a component of its ambient centralizer.
Restriction to the fixed subgroup inside the enlargement preserves
subnormality and quasisimplicity. The homomorphism used in this restriction
is the actual inclusion into the ambient centralizer, not an assumed
normal embedding. Faithfulness and elementary abelianness give order two
for every nonidentity induced automorphism.

Source: Aschbacher–Smith 16.3.5(2) and 16.3.6, printed pp.1178–1179 /
PDF pp.1195–1196.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
variable {G : Type*} [Group G] {E L : Subgroup G} {i : G}

/-- Every actor fixes the component pointwise. -/
theorem actor_fixes_component (h : ExceptionalEnlargement E L i)
    (hc : CentralizesAsComponent E L) (e : E) (l : ComponentInside L i) :
    inducedAction E (Enlargement L i) h.normalizes e l = l := by
  by_cases he : e = 1
  · simp [he]
  · have hcomp := hc e e.property (fun hh => he (Subtype.ext hh))
    have hl := hcomp.1 l.property
    have hm := mem_centralizer_singleton_iff.mp hl
    change (l : G) * (e : G) = (e : G) * (l : G) at hm
    apply Subtype.ext
    change (e : G) * (l : G) * (e : G)⁻¹ = (l : G)
    rw [← hm]
    group

/-- Restriction retains the component in the actual intrinsic fixed subgroup. -/
theorem actor_component (h : ExceptionalEnlargement E L i)
    (hc : CentralizesAsComponent E L) (e : E) (he : e ≠ 1) :
    IsComponentIn (ComponentInside L i)
      (inducedAction E (Enlargement L i) h.normalizes e).fixedSubgroup := by
  let α := inducedAction E (Enlargement L i) h.normalizes
  have hcomp := hc e e.property (fun hh => he (Subtype.ext hh))
  have hle : ComponentInside L i ≤ (α e).fixedSubgroup := by
    intro l hl
    exact (MulAut.mem_fixedSubgroup _ _).mpr (actor_fixes_component h hc e ⟨l, hl⟩)
  let φ : (α e).fixedSubgroup →* involutionCentralizer (e : G) :=
    { toFun := fun x => ⟨(x : Enlargement L i), by
        apply mem_centralizer_singleton_iff.mpr
        have hx := congrArg (fun y : Enlargement L i => (y : G))
          ((MulAut.mem_fixedSubgroup _ _).mp x.property)
        change (e : G) * (x : G) * (e : G)⁻¹ = (x : G) at hx
        exact ((mul_inv_eq_iff_eq_mul).mp hx).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨hle, ?_, ?_⟩
  · exact hcomp.2.1.comap φ
  · let := hcomp.quasisimple
    let : IsQuasisimple (ComponentInside L i) := IsQuasisimple.of_mulEquiv
      (subgroupOfEquivOfLe (ComponentTransfer.le_layerClosure _ _)).symm
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm

/-- Nonidentity actors induce involutions, using the supplied faithful action. -/
theorem actor_order_two (h : ExceptionalEnlargement E L i)
    (e : E) (he : e ≠ 1) : orderOf (inducedAction E (Enlargement L i) h.normalizes e) = 2 := by
  let := h.elementary
  rw [orderOf_injective _ h.faithful]
  apply orderOf_eq_prime _ he
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) e
end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
