module
public import Stellmacher.SectionEight.EightFourEdgeFixedNormal
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# The Sylow centralizer of the actual star lies in the first core

In the central-first-step, nontrivial-closure branch of Stellmacher (8.4),
any subgroup D of the distinguished edge Sylow centralizing the actual
first fixed-center normal closure lies in the first-step two-core. No
critical-length-two hypothesis is needed, and the initial fixed subgroup
and its closure are the original witness constructions.

The closure C is normal in the first-step stabilizer P, so its centralizer
restricted to S is normal in S. Apply (3.4) to this exact Sylow intersection.
The core alternative gives the result. In the other alternative the residual
O²(P) lies in C_H(C), since P normalizes that centralizer. It therefore
centralizes the fixed subgroup F contained in C. The proved edge normality
of F gives S-normality, and O²(P) together with S generates P. Thus F is
normal in P and its normal closure equals F, contrary to the branch assumption.
The edge-normality input is essential; no generic centralizer-core assertion
is used.

This supplies the inference that a commuting neighboring star lies in Q_(a+1)
in source (8) of Stellmacher (8.4), Journal of Algebra190 (1997), printed p39,
`refs/files/stellmacher-n-group.pdf`.

The exact local context suffices for this argument. The original canonical
API is retained as a wrapper through the same graph and quotient witness.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
/-- A subgroup of the edge Sylow centralizing the actual initial star lies in the first core. -/
public theorem eight_four_star_centralizer_core_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
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
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (D : Subgroup H) (hDS : D ≤ S)
    (hDC : ⁅D,(Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype⁆ = ⊥) :
    D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let F := w.oneJFixedPoints S
  let C0 := Subgroup.normalClosure (F.subgroupOf P : Set P)
  let C := C0.map P.subtype
  let K := Subgroup.centralizer (C : Set H)
  let T := S ⊓ K
  let h := ctx.sectionSeven
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_right
  have hFn := eight_four_edge_fixed_normal_local ctx hcenter w hbranch
  have hFP : F ≤ P := hFn.1.trans inf_le_right
  have hFC : F ≤ C := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hFP]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hCn : (C.subgroupOf P).Normal := by
    change ((C0.map P.subtype).comap P.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance
  have hPC : P ≤ Subgroup.normalizer (C : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le C0)).mp hCn
  have hnormK : Subgroup.normalizer (C : Set H) ≤ Subgroup.normalizer (K : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (C : Set H))).mp inferInstance
  have hTn : (T.subgroupOf S).Normal := by
    have hn := (Subgroup.normal_subgroupOf_centralizer_normalizer (C : Set H)).comap
      (Subgroup.inclusion (hSP.trans hPC))
    convert hn using 1
    ext s
    exact and_iff_right s.property
  have hlocal := (SevenSix.edge_local_data h Γ cp).2
  have halt := SectionThree.lemma_three_four S (SevenSix.sectionThreeHypotheses h) P
    ((pFamily_iff_pSet (⊤ : Subgroup H) S P).mp hlocal.1) T
    ⟨inf_le_left,hTn⟩ hlocal.2
  have hDT : D ≤ T := le_inf hDS (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDC)
  rcases halt with hTcore | hcomm
  · exact (hDT.trans hTcore).trans_eq (Γ.twoCoreAt_def cp.firstStep).symm
  · have hRK : twoResidualAmbient P ≤ K := by
      rw [← hcomm]
      exact (Subgroup.commutator_mono le_rfl inf_le_right).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((Subgroup.map_subtype_le _).trans (hPC.trans hnormK)))
    have hRF : twoResidualAmbient P ≤ Subgroup.normalizer (F : Set H) :=
      hRK.trans ((Subgroup.centralizer_le hFC).trans (Subgroup.centralizer_le_normalizer _))
    have hSF : S ≤ Subgroup.normalizer (F : Set H) :=
      cp.S_le_edge_stabilizers.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hFn.1).mp hFn.2)
    have hgen : twoResidualAmbient P ⊔ S = P :=
      SectionThree.twoResidual_sup_sylowImage hlocal.1.1.2.1.2
    have hPF : P ≤ Subgroup.normalizer (F : Set H) := hgen ▸ sup_le hRF hSF
    let _ : (F.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFP).mpr hPF
    have hCF : C = F := by
      change (Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype = F
      rw [Subgroup.normalClosure_eq_self,Subgroup.map_subgroupOf_eq_of_le hFP]
    exact (hbranch hCF).elim

/-- Canonical specialization with the same fixed seed and strict closure. -/
public theorem eight_four_star_centralizer_core
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
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (D : Subgroup H) (hDS : D ≤ S)
    (hDC : ⁅D,(Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype⁆ = ⊥) :
    D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  exact eight_four_star_centralizer_core_local ctx.toLocalContext hcenter w hbranch D hDS hDC

end Stellmacher.SectionEight
