module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import Theory.SpecificGroups.Triality.RootParabolics

/-!
# Transport of genuine triality parabolics to a component

An actual isomorphism from L to the standard graph-field carrier pulls each
root-defined parabolic back to L and then embeds it in G. Its overgroup is
the join with the entire supplied Sylow subgroup S. Generation of the two
finite model parabolics therefore gives generation of ⟨L,S⟩ by these
overgroups, without assuming S normalizes L.

For a local setup, membership of an overgroup in Hₑ implies membership in
Hₑ(S): it contains the involution z, so its self-centralizing two-core
cannot be trivial. The self-centralizing-core assertion itself, and the
N_S(L)-invariance of the transported parabolics, remain model calculations.

Source: Aschbacher–Smith 2.3.9(7), printed p.526. The finite parabolic
generation premise below is not inferred from generation in the split
group, since taking graph-field fixed points does not preserve joins.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

open Subgroup
open _root_.Triality.Standard

variable {G : Type*} [Group G] {L : Subgroup G} {P : Parameters}

/-- The whole root-defined parabolic transported through the genuine model
equivalence. This is separate from its prime-to-characteristic residual. -/
def componentParabolic (e : L ≃* Carrier P) (a : Parabolics.Node) : Subgroup G :=
  ((Parabolics.parabolic P a).comap e.toMonoidHom).map L.subtype

/-- The source overgroup ⟨Kᵢ,S⟩, even when S permutes components. -/
def parabolicOvergroup (e : L ≃* Carrier P) (S : Subgroup G)
    (a : Parabolics.Node) : Subgroup G := componentParabolic e a ⊔ S

theorem componentParabolic_le (e : L ≃* Carrier P) (a : Parabolics.Node) :
    componentParabolic e a ≤ L := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Restriction to L recovers precisely the pulled-back parabolic. -/
theorem componentParabolic_subgroupOf (e : L ≃* Carrier P) (a : Parabolics.Node) :
    (componentParabolic e a).subgroupOf L =
      (Parabolics.parabolic P a).comap e.toMonoidHom :=
  Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem le_parabolicOvergroup (e : L ≃* Carrier P) (S : Subgroup G)
    (a : Parabolics.Node) : S ≤ parabolicOvergroup e S a := le_sup_right

theorem parabolicOvergroup_le (e : L ≃* Carrier P) (S : Subgroup G)
    (a : Parabolics.Node) : parabolicOvergroup e S a ≤ L ⊔ S :=
  sup_le_sup_right (componentParabolic_le e a) S

/-- Transport preserves generation of the finite carrier. -/
theorem componentParabolic_sup (e : L ≃* Carrier P)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤) :
    componentParabolic e .arms ⊔ componentParabolic e .central = L := by
  simp only [componentParabolic, Subgroup.comap_equiv_eq_map_symm']
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, hgen,
    Subgroup.map_top_of_surjective _ e.symm.surjective,
    ← MonoidHom.range_eq_map, L.range_subtype]

/-- Adjoining S commutes with the generation step; no normality is used. -/
theorem parabolicOvergroup_sup (e : L ≃* Carrier P) (S : Subgroup G)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤) :
    parabolicOvergroup e S .arms ⊔ parabolicOvergroup e S .central = L ⊔ S := by
  change (componentParabolic e .arms ⊔ S) ⊔ (componentParabolic e .central ⊔ S) = _
  rw [sup_sup_sup_comm, sup_idem, componentParabolic_sup e hgen]

/-- The source involution supplies nontriviality of the self-centralizing
two-core; containment of S follows from the actual join construction. -/
theorem parabolicOvergroup_mem_HeOver {H M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* Carrier P) (a : Parabolics.Node)
    (he : parabolicOvergroup e ((S : Subgroup H).map H.subtype) a ∈ Chapter1.He G) :
    parabolicOvergroup e ((S : Subgroup H).map H.subtype) a ∈
      Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  refine ⟨he, ?_, le_parabolicOvergroup e _ a⟩
  change (parabolicOvergroup e ((S : Subgroup H).map H.subtype) a).pCoreIn 2 ≠ ⊥
  intro hbot
  change _ ⊓ centralizer _ ≤ _ at he
  rw [hbot] at he
  have hz := le_parabolicOvergroup e ((S : Subgroup H).map H.subtype) a h.mem_sylow
  have hzbot := he ⟨hz, by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]⟩
  have hz1 : z = 1 := hzbot
  simpa [hz1] using h.involution

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

end
