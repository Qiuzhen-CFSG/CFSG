module
public import CFSG.Quasithin.ChapterG.Section11.Multiplicity
public import CFSG.Quasithin.ChapterG.Section09.ConstituentAction
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting

/-!
# G.6.4 on the proper marked G.11 constituent

The low-rank multiplicity theorem gives a witness acting as a transvection
on the selected proper constituent. Its literal HX-action is irreducible;
quotienting by that action kernel makes it faithful and gives trivial
two-core. The original SQTK cover restricts to the preimage of HX and then
surjects onto this same kernel quotient. The nonzero transvection orbit
spans by irreducibility, discharging every input to the proved G.6.4.

The resulting finite model list concerns the actual constituent action,
not the original whole-module action. Its reconstruction as a G.11.2 row
remains with the Section 11 classification assembly.
Source: Aschbacher--Smith G.6.1--4, G.10.16(4), G.11.8,
printed pp.345--346,363--364,368.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem rankOne_classification (ρ : Representation (ZMod 2) G V)
    [IsIrreducible ρ] (hf : Function.Injective ρ)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (a : G) (ha : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Section06.Conclusion ρ a := by
  obtain ⟨c⟩ := cover
  have hne : a ≠ 1 := by
    intro he
    rw [he,map_one,Module.End.one_eq_id,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  have hcore : pCore 2 G = ⊥ := by
    exact le_bot_iff.mp ((normal_p_subgroup_le_ker ρ (pCore 2 G) pCore_isPGroup).trans
      ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le)
  have hN : normalClosure ({a} : Set G) ≠ ⊥ := by
    intro he
    have haN := subset_normalClosure (Set.mem_singleton a)
    exact hne (mem_bot.mp (he ▸ haN))
  have hgen : conjugateDisplacementSpan ρ a ⊤ = ⊤ := by
    rw [← commutator_conjugateSpanBy_zpowers,conjugateSpanBy_zpowers_top]
    exact subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf inferInstance _ hN
  have hs : Section06.Hypotheses KnownSimple.IsKnownSimple ρ a c.projection := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := c.sqtk
    quotient_surjective := c.surjective
    twoCore := hcore
    faithful := hf
    involution := ha
    nonidentity := hne
    displacement_rank := by omega
    generated := hgen }
  exact Section06.lemma_G_6_4 hs hr

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem constituentAction_irreducible
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G)
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation) :
    IsIrreducible (Section09.constituentAction ρ H X I hH hX) := by
  let P := H ⊔ X
  let e := subgroupOfEquivOfLe (show H ≤ P from le_sup_left)
  have he : (Section09.constituentAction ρ H X I hH hX).comp (H.subgroupOf P).subtype =
      (invariantSubspace ρ H I hH).toRepresentation.comp e.toMonoidHom := rfl
  apply irreducible_of_subgroup_restriction _ (H.subgroupOf P)
  rw [he]
  exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr hi

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem constituentAction_rank
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G)
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I) (a : X) :
    let σ := Section09.constituentAction ρ H X I hH hX
    let aP : (H ⊔ X : Subgroup G) := ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩
    finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) =
      finrank (ZMod 2) (I.map (ρ a - LinearMap.id)) := by
  dsimp only
  have heq : (LinearMap.range
      (Section09.constituentAction ρ H X I hH hX
        ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩ - LinearMap.id)).map I.subtype =
      I.map (ρ a - LinearMap.id) := by
    rw [← LinearMap.range_comp]
    have he : I.subtype.comp
        (Section09.constituentAction ρ H X I hH hX
          ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩ - LinearMap.id) =
        (ρ a - LinearMap.id).comp I.subtype := by
      ext u
      rfl
    rw [he,LinearMap.range_comp,Submodule.range_subtype]
  have he := Submodule.finrank_map_subtype_eq I (LinearMap.range
    (Section09.constituentAction ρ H X I hH hX
      ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩ - LinearMap.id))
  rw [heq] at he
  exact he.symm

/-- The actual action quotient on a proper marked constituent satisfies the
complete rank-one classification G.6.4. The witness is from the original X. -/
theorem proper_marked_constituent_rankOne_classification
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) (hp : I ≠ ⊤) :
    let H := componentOrbit L ⊤
    letI := componentOrbit_top_normal L
    let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
    let σ := Section09.constituentAction ρ H X I hI.choose hXI
    ∃ a : X, orderOf (a : G) = 2 ∧ v ∈ RankTwo.movedSpace ρ a ∧
      finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2 ∧
      let aP : (H ⊔ X : Subgroup G) := ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩
      finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) = 1 ∧
      Section06.Conclusion (kerRepresentation σ) (QuotientGroup.mk' σ.ker aP) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
  let σ := Section09.constituentAction ρ H X I hI.choose hXI
  have hh := marked_constituent_alternative h cover hw hS hn hL hm hI hv
  obtain ⟨_,_,_,a,ha,ha2,hav,_,hr,hrI⟩ := hh.2.2.2.resolve_left (fun he => hp he.1)
  let aX : X := ⟨a,ha⟩
  let aP : (H ⊔ X : Subgroup G) := ⟨a,(le_sup_right : X ≤ H ⊔ X) ha⟩
  have hrσ : finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) = 1 :=
    (constituentAction_rank ρ H X I hI.choose hXI aX).trans hrI
  refine ⟨aX,ha2,hav,hr,hrσ,?_⟩
  have hR := hI.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H
  let : IsIrreducible σ := constituentAction_irreducible ρ H X I hI.choose hXI hR
  apply rankOne_classification (kerRepresentation σ) (kerRepresentation_faithful σ)
    (cover.map (fun c => (c.subgroup (H ⊔ X)).map (QuotientGroup.mk' σ.ker)
      (QuotientGroup.mk'_surjective σ.ker))) (QuotientGroup.mk' σ.ker aP)
  · rw [← map_pow]
    have hp2 : aP ^ 2 = 1 := by
      apply Subtype.ext
      change a ^ 2 = 1
      rw [← ha2]
      exact pow_orderOf_eq_one a
    rw [hp2,map_one]
  · exact hrσ

end CFSG.Quasithin.ChapterG.Section11
