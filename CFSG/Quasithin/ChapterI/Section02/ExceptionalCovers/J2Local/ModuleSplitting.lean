module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.ModuleSplitting.ElementaryQuotient
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.ModuleSplitting.ModuleIdentification
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.ModuleSplitting.ProjectiveTransport
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.Restriction
public import GorensteinWalter.AlternatingFiveDoubleCover

/-!
# The J₂ local cover's projective radical splitting and SL₂(5) quotient

`ElementaryQuotient` constructs the distinguished square and proves that the
literal two-core modulo this square is elementary abelian. `ModuleIdentification`
identifies the original radical quotient with the projective binary A₅
augmentation module, retaining the five-point action and every quotient map.
`ProjectiveTransport` uses this concrete map to construct the central complement
to the intrinsic commutator subgroup. The resulting perfect central double
cover of A₅ is SL₂(5), compatibly with the original action, which excludes
involutions outside the two-core.

The assembly below discharges the module and splitting premises of the retained
conditional recognition theorem.
Perfection and the nonempty quotient square-root orbit are supplied by the
independent square-orbit branch of the local-cover proof.

Source: Aschbacher--Smith I.2.2(5), printed pp.411--412 / PDF pp.422--423,
combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
open Sporadic.LeechRelated.J2
open ExceptionalParabolics.Seed
variable {K : Type*} [Group K] [Finite K]
variable (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)

/-- The source's commutator is intrinsic to the actual local preimage. -/
noncomputable abbrev coreCommutator : Subgroup (preimage e) :=
  ⁅pCore 2 (preimage e), (⊤ : Subgroup (preimage e))⁆

include hZ in
/-- The projective-module branch has precisely two group-theoretic outputs
to discharge: the central supplement and its trivial intersection. Those
outputs imply the source recognition and involution exclusion. -/
theorem commutator_quotient_of_central_complement [Group.IsPerfect (preimage e)]
    (hsup : pCore 2 (preimage e) =
      coreCommutator e ⊔ (center K).subgroupOf (preimage e))
    (hdis : Disjoint (coreCommutator e) ((center K).subgroupOf (preimage e))) :
    (∃ d : ((preimage e) ⧸ coreCommutator e) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5),
      (GorensteinWalter.AlternatingFiveDoubleCover.projection.comp d.toMonoidHom).comp
        (QuotientGroup.mk' (coreCommutator e)) = a5Action e) ∧
    (∀ x : preimage e, orderOf x = 2 → x ∈ pCore 2 (preimage e)) := by
  have hc : (center K).subgroupOf (preimage e) ≤ center (preimage e) := by
    rw [← restriction_ker]
    exact restriction_ker_central e
  have hcard : Nat.card ((center K).subgroupOf (preimage e)) = 2 := by
    rw [← restriction_ker, restriction_kernel_card, hZ]
  obtain ⟨hd, hi⟩ := GorensteinWalter.AlternatingFiveDoubleCover.quotient_of_central_supplement
    (a5Action e) (a5Action_surjective e) (coreCommutator e)
    ((center K).subgroupOf (preimage e)) hc hcard
    ((a5Action_ker e hZ).trans hsup) hdis
  refine ⟨hd, ?_⟩
  intro x hx
  rw [← a5Action_ker e hZ]
  apply MonoidHom.mem_ker.mpr
  apply hi x
  simpa only [hx] using pow_orderOf_eq_one x

variable [Group.IsPerfect (preimage e)]
variable (hex : ∃ r ∈ pCore 2 l₁, r ^ 2 = marked)
variable (horbit : ∀ r ∈ pCore 2 l₁, ∀ s ∈ pCore 2 l₁,
  r ^ 2 = marked → s ^ 2 = marked → IsConj r s)

include hZ hex horbit

/-- The actual projective radical module splits off the original covering
center. No module map or complement is an additional hypothesis. -/
theorem core_central_complement :
    pCore 2 (preimage e) =
      coreCommutator e ⊔ (center K).subgroupOf (preimage e) ∧
    Disjoint (coreCommutator e) ((center K).subgroupOf (preimage e)) := by
  obtain ⟨hb, hbker, hbe⟩ := coreModuleMap_spec e hZ hex horbit
  exact core_central_complement_of_module_map e hZ hex horbit
    (coreModuleMap e hZ) hb hbker hbe

/-- The projective-module branch of I.2.2(5): the literal quotient by `[R,H]`
is SL₂(5) over the checked A₅ action, and every involution lies in `R`.
Only perfection and the nonempty square-root orbit remain for the independent
local-cover assembly; elementary structure, projectivity and splitting have
all been proved. -/
theorem commutator_quotient_of_quotient_orbit :
    (∃ d : ((preimage e) ⧸ coreCommutator e) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5),
      (GorensteinWalter.AlternatingFiveDoubleCover.projection.comp d.toMonoidHom).comp
        (QuotientGroup.mk' (coreCommutator e)) = a5Action e) ∧
    (∀ x : preimage e, orderOf x = 2 → x ∈ pCore 2 (preimage e)) := by
  obtain ⟨hsup, hdis⟩ := core_central_complement e hZ hex horbit
  exact commutator_quotient_of_central_complement e hZ hsup hdis

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
