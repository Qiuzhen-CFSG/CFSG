module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.Residuals
public import CFSG.Quasithin.Chapter10.SourceA5BaumannDisplacement

/-!
# Displacement lines for the original A₅ block

The paired residual displacement theorem applies to the original block after
its literal residual identification. Its moved module is the original block
layer. Transport through the local subgroup inclusion places the line and
all Baumann-center commutators in the original ambient group.

Source: Aschbacher–Smith 10.2.1, printed p.743, using E.2.3(3).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_original_baumann_displacement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ v ∈ (blockU L).map L.subtype, v ≠ 1 ∧
      ∀ g ∈ (T : Subgroup G) ⊓ L,
        ∀ x ∈ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)),
          ⁅g,x⁆=1 ∨ ⁅g,x⁆=v := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  obtain ⟨d,c,hex,_,haxes⟩ := source_a5_original_residual_axes D e hn hout
  obtain ⟨v₁,v₂,hv₁,hn₁,hv₂,hn₂,h₁,h₂⟩ :=
    paired_symmetric_baumann_center_displacement S (source_a5_minimal_parabolic D e hn)
      U (source_parabolic_module_reduced D) (source_local_thompson_not_centralizes D hout)
      q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) d c hex
  have hv : ∃ v : H, v ∈ ⁅U,A⁆ ∧ v ≠ 1 ∧
      ∀ g ∈ (S : Subgroup H) ⊓ A,
        ∀ x ∈ omegaOneCenterAmbient (ChapterB.baumann (S : Subgroup H)),
          ⁅g,x⁆=1 ∨ ⁅g,x⁆=v := by
    rcases haxes with ha | ha
    · change A = factorResidual q Y d.first at ha
      exact ⟨v₁,by simpa only [ha] using hv₁,hn₁,by simpa only [ha] using h₁⟩
    · change A = factorResidual q Y d.second at ha
      exact ⟨v₂,by simpa only [ha] using hv₂,hn₂,by simpa only [ha] using h₂⟩
  obtain ⟨v,hv,hvn,hline⟩ := hv
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  let b : A ≃* L := subgroupOfEquivOfLe hLH
  have hb : ((blockU A).map A.subtype).map H.subtype = (blockU L).map L.subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv b,map_map,map_map]
    rfl
  refine ⟨(v:G),?_,(fun he => hvn (Subtype.ext he)),?_⟩
  · rw [←hb]
    apply mem_map_of_mem H.subtype
    rw [←source_a5_original_block_moved D e hn hout]
    exact hv
  · intro g hg x hx
    rw [←source_local_baumann_center_map (L := L)] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact (hline ⟨g,hLH hg.2⟩ hg y hy).imp (congrArg Subtype.val) (congrArg Subtype.val)

end CFSG.Quasithin.Chapter10
