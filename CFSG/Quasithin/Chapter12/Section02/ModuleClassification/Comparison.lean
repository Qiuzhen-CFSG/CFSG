module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Irreducibility
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!
# Literal comparison with a B.5 moved section

A surjective action map from the original L/O2(L) makes the B.5 moved space
all of the chosen Irr+ space. The subtype equivalence carries its fixed
space onto the original fixed subspace, yielding an equivalence of the
literal central quotients with a formula on every quotient representative.
This common comparison is instantiated for the seed and offender supplement.
Source: Aschbacher--Smith B.5.1 and 12.2.2, printed pp.99--103 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- An actual image of the original two-core action, with the projection retained. -/
structure LiteralComparison {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H D.space) (K : Subgroup H) where
  projection : (L ⧸ pCore 2 L) →* K
  surjective : Function.Surjective projection
  faithful : Function.Injective (ρ.comp K.subtype)
  action : ∀ q, ρ (projection q) = D.quotientAction q

namespace LiteralComparison
variable {D} {H : Type*} [Group H] {ρ : Representation (ZMod 2) H D.space}
    {K : Subgroup H} (c : D.LiteralComparison ρ K)
include c

theorem irrPlus : IsIrrPlus ρ K ⊤ := by
  apply D.quotientAction_irrPlus.of_intertwining D.quotientAction ρ
    (c.projection.comp (topEquiv (G := L ⧸ pCore 2 L)).toMonoidHom)
    (c.surjective.comp (topEquiv (G := L ⧸ pCore 2 L)).surjective)
    LinearMap.id (fun _ _ he => he)
  · intro q v
    exact LinearMap.congr_fun (c.action q) v
  · exact Submodule.map_id _

theorem moved_eq_top : moved ρ K = ⊤ := c.irrPlus.choose_spec.1

theorem space_eq_top (s : MovedSection ρ K) : s.space.toSubmodule = ⊤ :=
  s.space_eq.trans c.moved_eq_top

@[expose] noncomputable def spaceEquiv (s : MovedSection ρ K) :
    s.space.toSubmodule ≃ₗ[ZMod 2] D.space :=
  LinearEquiv.ofTop _ (c.space_eq_top s)

@[simp] theorem spaceEquiv_apply (s : MovedSection ρ K) (v : s.space.toSubmodule) :
    c.spaceEquiv s v = v.val := rfl

private theorem fixed_iff (v : D.space) : v ∈ fixedSpace ρ K ↔
    v ∈ (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
      (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype := by
  constructor
  · intro hv x
    let l : L := ⟨x.val.val,x.property⟩
    have hh := hv (c.projection (QuotientGroup.mk' (pCore 2 L) l))
    change ρ (c.projection (QuotientGroup.mk' (pCore 2 L) l)) v = v at hh
    rw [c.action] at hh
    exact congrArg Subtype.val hh
  · intro hv k
    obtain ⟨q,rfl⟩ := c.surjective k
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    change ρ (c.projection (QuotientGroup.mk' (pCore 2 L) l)) v = v
    rw [c.action]
    apply Subtype.ext
    exact hv ((subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l)

theorem central_map (s : MovedSection ρ K) :
    s.central.toSubmodule.map (c.spaceEquiv s).toLinearMap =
      (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
        (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    rw [s.central_eq] at hw
    exact (c.fixed_iff _).mp (fun k => congrArg Subtype.val (hw k))
  · intro hv
    refine ⟨(c.spaceEquiv s).symm v, ?_, (c.spaceEquiv s).apply_symm_apply v⟩
    rw [s.central_eq]
    intro k
    apply Subtype.ext
    have he : ((c.spaceEquiv s).symm v).val = v := (c.spaceEquiv s).apply_symm_apply v
    change ρ k ((c.spaceEquiv s).symm v).val = ((c.spaceEquiv s).symm v).val
    rw [he]
    exact (c.fixed_iff v).mpr hv k

@[expose] noncomputable def centralEquiv (s : MovedSection ρ K) :
    (s.space.toSubmodule ⧸ s.central.toSubmodule) ≃ₗ[ZMod 2] D.chosenCentralQuotient :=
  Submodule.Quotient.equiv _ _ (c.spaceEquiv s) (c.central_map s)

@[simp] theorem centralEquiv_mk (s : MovedSection ρ K) (v : s.space.toSubmodule) :
    c.centralEquiv s (Submodule.Quotient.mk v) = Submodule.Quotient.mk v.val := rfl

end LiteralComparison
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
