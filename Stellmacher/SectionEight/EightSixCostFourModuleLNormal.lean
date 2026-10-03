module
public import Stellmacher.SectionEight.EightSixCostFourInitialResidualModule
/-!
# The canonical cost-four module is normal in the prescribed L

For the actual selected cost-four configuration, the canonical elementary
sixteen subgroup W=[U,Ea] is normal in L. This supplies the normal-in-L
field of Stellmacher (8.6)(b3), without any action classification assumption.

The subgroup U is normal in Vnext because its commutator with Vnext lies
in the next central line contained in U. Also Vnext lies in Ga and hence
normalizes its two-residual Ea. It therefore normalizes their commutator W.
The canonical module theorem supplies Q- and Ea-normalization. Finally,
the actual Sylow intersection and residual supplement give
L=Ea(Vnext Q), so all of L normalizes W. Its containment in L follows from
W lying in the initial pair, which lies in Q=O2(L).

Source: Stellmacher (8.6)(b3), printed p.44. The proof uses only the native
equation-one Sylow supplement and the proved canonical subgroup structure.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_module_l_normal
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    NormalIn ⁅conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E,
      EAt ctx.Γ ctx.criticalPath.a⁆ L := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let F := EAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  let W := ⁅U,F⁆
  obtain ⟨_,_,_,hWR,hQN,hFN,_⟩ := eight_six_cost_four_initial_residual_module
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hRQ : (VAt Γ previous ⊓ QAt Γ cp.a) ⊔ (V ⊓ QAt Γ cp.a) ≤ Q :=
    data.core_generation ▸ le_sup_left
  have hWQ : W ≤ Q := hWR.trans hRQ
  have hQL : Q ≤ L := hQ ▸ twoCoreIn_le L
  have hUV : U ≤ V := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    (geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hZU : Z ≤ U := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans (by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩)
  have hVR : V ≤ QAt Γ cp.firstStep :=
    neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) _
  have hVV : ⁅V,V⁆ ≤ Z := (Subgroup.commutator_mono le_rfl hVR).trans_eq data.first_commutator
  have hVN : V ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hUV le_rfl).trans (hVV.trans hZU))
  have hVS : V ≤ S := (le_sup_left.trans data.sylow_intersection.symm.le).trans inf_le_right
  have hVP : V ≤ P := hVS.trans (edge_sylow_data ctx.sectionSeven Γ cp).1.1
  have hFdef : F = twoResidualIn P := Γ.twoResidualAt_def _
  have hPNF : P ≤ Subgroup.normalizer (F : Set G) := by
    rw [hFdef]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le P)).mp
      (twoResidualIn_normal P)
  have hVW : V ≤ Subgroup.normalizer (W : Set G) := by
    intro v hv
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (⁅U,F⁆).map (MulAut.conj v).toMonoidHom = ⁅U,F⁆
    simp only [MulEquiv.toMonoidHom_eq_coe]
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVN hv),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPNF (hVP hv))]
  have hF : twoResidualIn L = F :=
    eight_six_equation_one_residual_eq_initial ctx.sectionSeven Γ cp previous D L Q hL data
  have hSyl := eight_six_sylow_intersection_of_residual_le P L S data.closure_le
    (edge_sylow_data ctx.sectionSeven Γ cp).1
    (hFdef.symm.le.trans data.residual_le)
  have hgen : F ⊔ (V ⊔ Q) = L := by
    have hh := twoResidualIn_sup_sylow hSyl
    rw [hF,data.sylow_intersection] at hh
    exact hh
  have hLN : L ≤ Subgroup.normalizer (W : Set G) := by
    rw [←hgen]
    exact sup_le hFN (sup_le hVW hQN)
  exact ⟨hWQ.trans hQL,Subgroup.normal_subgroupOf_of_le_normalizer hLN⟩
end Stellmacher.SectionEight
