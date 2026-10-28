module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceTransport
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import Theory.GroupTheory.GeneralizedFitting.Solvable
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.ElementaryAbelian.Injective

/-!
# Restriction to the original starred-generated actor

Restricting the acting group to an overgroup of one original minimum actor
preserves the cubic minimum and exactly its starred subgroups. In particular,
Jhat acts on the unchanged module with its own Jhat equal to the full group.
In the solvable cyclic-starred case, normality also passes the trivial two-core
to Jhat, giving the original cyclic source hypotheses before any moved-space
restriction.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084, and D.2.17.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem elementary_subtype_map_iff {H : Subgroup G} (B : Subgroup H) :
    IsElementaryTwo B ↔ IsElementaryTwo (B.map H.subtype) := by
  constructor
  · intro h
    let := h.2
    refine ⟨?_, IsElementaryAbelian.map H.subtype⟩
    intro hb
    apply h.1
    exact (Subgroup.map_injective H.subtype_injective) (by simpa only [Subgroup.map_bot] using hb)
  · intro h
    let := h.2
    refine ⟨?_, IsElementaryAbelian.of_injective
      (B.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
      (B.equivMapOfInjective H.subtype H.subtype_injective).injective⟩
    intro hb
    exact h.1 (by rw [hb,Subgroup.map_bot])

/-- Restricting the acting group to an overgroup of a minimum actor preserves
its cubic minimum and exactly the original starred subgroups lying there. -/
theorem subgroup_starred_transport (H : Subgroup G)
    (hwit : ∃ A ∈ QhatStar ρ, A ≤ H) :
    cubicRatio (ρ.comp H.subtype) = cubicRatio ρ ∧
    ∀ B : Subgroup H, B ∈ QhatStar (ρ.comp H.subtype) ↔ B.map H.subtype ∈ QhatStar ρ := by
  have hr (B : Subgroup H) : actionRatio (ρ.comp H.subtype) B =
      actionRatio ρ (B.map H.subtype) := by
    rw [actionRatio,actionRatio,rank_map_injective H.subtype H.subtype_injective]
    congr 1
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have hc (B : Subgroup H) : IsCubic (ρ.comp H.subtype) B ↔ IsCubic ρ (B.map H.subtype) := by
    constructor
    · intro hc
      exact hc.map_equivariant (ρ.comp H.subtype) ρ H.subtype
        (LinearEquiv.refl _ _) (fun _ _ => rfl)
    · intro hc a ha b hb c hc' v
      exact hc a (mem_map_of_mem H.subtype ha) b (mem_map_of_mem H.subtype hb)
        c (mem_map_of_mem H.subtype hc') v
  obtain ⟨A,hA,hAH⟩ := hwit
  have hA' := SourceReduction.starred_subgroupOf ρ hA hAH
  have he : cubicRatio (ρ.comp H.subtype) = cubicRatio ρ := by
    rw [←hA'.1.2.2.2,hr,map_subgroupOf_eq_of_le hAH,hA.1.2.2.2]
  have hmin (B : Subgroup H) : B ∈ QhatMin (ρ.comp H.subtype) ↔
      B.map H.subtype ∈ QhatMin ρ := by
    simp only [QhatMin,Set.mem_ofPred_eq,he,elementary_subtype_map_iff,hr,hc]
  refine ⟨he,fun B => ⟨?_,?_⟩⟩
  · intro hB
    refine ⟨(hmin B).mp hB.1,?_⟩
    intro C hC hCB
    have hCH : C ≤ H := hCB.trans (map_subtype_le B)
    have hC' : C.subgroupOf H ∈ QhatMin (ρ.comp H.subtype) :=
      (hmin _).mpr (by rwa [map_subgroupOf_eq_of_le hCH])
    have hle : C.subgroupOf H ≤ B := by
      intro c hc
      obtain ⟨b,hb,he⟩ := hCB hc
      exact (show b = c from Subtype.ext he) ▸ hb
    have heq := hB.2 _ hC' hle
    simpa only [map_subgroupOf_eq_of_le hCH] using congrArg (Subgroup.map H.subtype) heq
  · intro hB
    refine ⟨(hmin B).mpr hB.1,?_⟩
    intro C hC hCB
    apply Subgroup.map_injective H.subtype_injective
    exact hB.2 _ ((hmin C).mp hC) (Subgroup.map_mono hCB)

/-- The original starred-generated subgroup is still starred-generated on V. -/
theorem Jhat_restricted_generated (H : Subgroup G) (hH : H = Jhat ρ) :
    Jhat (ρ.comp H.subtype) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  apply le_antisymm (map_subtype_le _)
  apply hH.le.trans
  apply sSup_le
  intro A hA
  have hAH : A ≤ H := hH.symm ▸ le_sSup hA
  have hstar := SourceReduction.starred_subgroupOf ρ hA hAH
  have hm := Subgroup.map_mono (le_sSup hstar) (f := H.subtype)
  simpa only [Jhat,map_subgroupOf_eq_of_le hAH] using hm
end CFSG.Quasithin.ChapterD
namespace CFSG.Quasithin.ChapterD
open Theory.GroupTheory CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The actual cyclic-starred case on Jhat, before removing any fixed vectors. -/
theorem cyclic_Jhat_core [Group.IsSolvable G] (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2)
    (hrank : ∀ A ∈ QhatStar ρ, rank A = 1) :
    CoreHypotheses (ρ.comp (Jhat ρ).subtype) := by
  let H := Jhat ρ
  let : H.Normal := Jhat_normal ρ
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hq
  have hwit : ∃ A ∈ QhatStar ρ, A ≤ H := ⟨A,hA,le_sSup hA⟩
  have ht := subgroup_starred_transport ρ H hwit
  refine ⟨hf.comp H.subtype_injective,ht.1 ▸ hq,
    Jhat_restricted_generated ρ H rfl,generalizedFitting_eq_fitting_of_solvable H,?_,?_⟩
  · rw [pCore_subnormal_eq_comap 2 (inferInstance : H.Normal).isSubnormal,hcore,
      MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
  · intro B hB
    rw [←rank_map_injective H.subtype H.subtype_injective]
    exact hrank _ ((ht.2 B).mp hB)

end CFSG.Quasithin.ChapterD
