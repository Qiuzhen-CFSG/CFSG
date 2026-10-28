module
public import Stellmacher.SectionEight.EightFourInitialFixedCommutator
public import Stellmacher.SectionFiveToSeven.NeighborModuleNormalClosure
public import Theory.GroupTheory.Commutator.NormalClosure
/-!
# The full fixed-closure commutator identities

In the exact nontrivial-closure branch of Stellmacher (8.4), the commutator
of the first neighbor module with the opposite-center closure S1 equals
the actual fixed-center normal closure Cstar, and Cstar centralizes S1.
These are the two identities immediately preceding source (4), printed p.39
of Stellmacher, Journal of Algebra 190 (1997).

The initial commutator [Za,S1] is the original J-fixed subgroup F. Local
transitivity identifies the neighbor module with the first-stabilizer normal
closure of Za. Inside that stabilizer, S1 is normal, so taking its commutator
commutes with taking normal closure. This gives [Vfirst,S1]=Cstar. Finally F
centralizes S1 by its fixed-space description; the same normal-closure
identity gives [Cstar,S1]=1. Native subgroup maps retain the original
witness, centers and closures throughout.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem commutator_normalClosure_eq
    {G : Type*} [Group G] (A K : Subgroup G) [K.Normal] :
    ⁅Subgroup.normalClosure (A : Set G),K⁆ =
      Subgroup.normalClosure ((⁅A,K⁆ : Subgroup G) : Set G) := by
  apply le_antisymm
  · rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_normalClosure_le_of_normal K A _
      (by rw [Subgroup.commutator_comm]; exact Subgroup.le_normalClosure)
  · apply Subgroup.normalClosure_le_normal
    exact Subgroup.commutator_mono Subgroup.le_normalClosure le_rfl

public theorem eight_four_full_closure_commutator
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    let C := (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,oppositeClosure ctx⁆ = C ∧
      ⁅C,oppositeClosure ctx⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Z := ZAt Γ cp.a
  let F := w.oneJFixedPoints S
  let K := oppositeClosure ctx
  let A := Z.subgroupOf P
  let KP := K.subgroupOf P
  let FP := F.subgroupOf P
  let N := Subgroup.normalClosure (A : Set P)
  let C0 := Subgroup.normalClosure (FP : Set P)
  let C := C0.map P.subtype
  have hK : NormalIn K P := opposite_closure_normal_next ctx
  let _ : KP.Normal := hK.2
  have hV : VAt Γ cp.firstStep = N.map P.subtype :=
    neighbor_module_eq_normalClosure_center
      (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated) Γ cp.a cp.firstStep cp.firstStep_adj
  have hZV : Z ≤ VAt Γ cp.firstStep :=
    (lemma_seven_four (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated) Γ cp).first_containment.1
  have hZP : Z ≤ P := hZV.trans (hV ▸ Subgroup.map_subtype_le _)
  have hFP : F ≤ P := (Subgroup.map_subtype_le _).trans hZP
  have hFPK : ⁅FP,KP⁆ = ⊥ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hFP,
      Subgroup.map_subgroupOf_eq_of_le hK.1,Subgroup.map_bot]
    have hfixed := fixed_center_eq_opposite_closure_centralizer_of_image ctx w
      (eight_four_opposite_closure_image ctx hcenter w hbranch)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hfixed.le.trans inf_le_right)
  have hAK : ⁅A,KP⁆ = FP := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hZP,
      Subgroup.map_subgroupOf_eq_of_le hK.1,Subgroup.map_subgroupOf_eq_of_le hFP]
    exact eight_four_initial_fixed_commutator ctx hcenter w hbranch
  have hNK : ⁅N,KP⁆ = C0 := by
    change ⁅Subgroup.normalClosure (A : Set P),KP⁆ = C0
    rw [commutator_normalClosure_eq,hAK]
  have hCK : ⁅C0,KP⁆ = ⊥ := by
    change ⁅Subgroup.normalClosure (FP : Set P),KP⁆ = ⊥
    rw [commutator_normalClosure_eq,hFPK]
    simp
  constructor
  · change ⁅VAt Γ cp.firstStep,K⁆ = C
    rw [hV,← Subgroup.map_subgroupOf_eq_of_le hK.1,← Subgroup.map_commutator,hNK]
  · change ⁅C0.map P.subtype,K⁆ = ⊥
    rw [← Subgroup.map_subgroupOf_eq_of_le hK.1,← Subgroup.map_commutator,hCK,Subgroup.map_bot]
end Stellmacher.SectionEight
