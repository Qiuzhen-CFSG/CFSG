module
public import Stellmacher.SectionEight.GeneratedEightSixRigidityResidual
public import Stellmacher.SectionEight.GeneratedEightSixEquationOneCoreTools
public import Stellmacher.SectionEight.GeneratedEightSixSylowIntersection
public import Theory.GroupTheory.Commutator.NormalSupplementPGroup

/-!
# Full initial residual action from equation-one data

The actual local equation-one packet already implies Q=[Q,Ea]D, where Ea
is the initial two-residual. Only the chosen predecessor, the prescribed
L and Q definitions and the equation-one data are needed. No cost branch,
next-core equality, quotient model or critical-length premise is added.

The core commutator identity puts the next factor in [Q,L]D. This subgroup
is normalized by the initial stabilizer, so local transitivity also puts
the predecessor factor in it; generation gives Q=[Q,L]D. The next core R
lies in L and S, while the equation-one Sylow intersection is Vnext Q.
Consequently QR=QVnext. The residual therefore supplements QR in L.
Modulo [Q,Ea]D the residual centralizes the image of Q; the proved finite
p-group normal-supplement commutator lemma then makes that image trivial.

Source: Stellmacher, Journal of Algebra190 (1997), (8.6), equations(1)–(3)
and the subsequent residual-support calculations, printed pp.41–45. This
branch-independent consequence also explains why the existing high-cost
proof's stronger equality Qnext=Vnext is unnecessary for this particular
residual-generation step.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem eight_six_full_residual
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (D L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    Q = ⁅Q,EAt ctx.Γ ctx.criticalPath.a⁆ ⊔ D := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := V ⊓ QAt Γ cp.a
  let F := EAt Γ cp.a
  let C := ⁅Q,L⁆ ⊔ D
  let M := ⁅Q,F⁆ ⊔ D
  have hQL : Q ≤ L := hQ ▸ twoCoreIn_le L
  have hFL : F ≤ L := data.residual_le
  have hRL : R ≤ L := by
    rw [hL]
    exact eight_six_first_core_le_previous_closure ctx.sectionSeven Γ cp previous hprev
  have hLN : P ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  let hLn : (L.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLN
  have hQN : P ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQL.trans data.closure_le)).mp (by
      rw [hQ]
      exact twoCoreIn_normal_of_normal L P data.closure_le hLn)
  have hDN : P ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp data.intersection_normal.2
  have hFN : P ≤ Subgroup.normalizer (F : Set G) := by
    change P ≤ Subgroup.normalizer (Γ.twoResidualAt cp.a : Set G)
    rw [Γ.twoResidualAt_def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le P)).mp (twoResidualIn_normal P)
  have hCN : P ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change C.map (MulAut.conj g).toMonoidHom = C
    simp only [MulEquiv.toMonoidHom_eq_coe]
    rw [Subgroup.map_sup,Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQN hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLN hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDN hg)]
  have hBC : B ≤ C := by
    have hcomm := data.core_commutator
    have hB : B ≤ ⁅Q,R⁆ ⊔ D := hcomm.symm ▸ le_sup_left
    exact hB.trans (sup_le_sup (Subgroup.commutator_mono le_rfl hRL) le_rfl)
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  obtain ⟨g,hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a hfirst hprev
  let f := (MulAut.conj (g:G)⁻¹).toMonoidHom
  have hVmap : V.map f = VAt Γ previous := by
    rw [←hg]
    exact (v_act Γ g cp.firstStep).symm
  have hQamap : (QAt Γ cp.a).map f = QAt Γ cp.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (QAt Γ cp.a : Set G)).inv_mem (stabilizer_le_normalizer_q Γ cp.a g.property))
  have hBmap : B.map f = A := by
    change (V ⊓ QAt Γ cp.a).map f = A
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective,hVmap,hQamap]
  have hAC : A ≤ C := by
    have hh := Subgroup.map_mono (f := f) hBC
    have hCmap : C.map f = C := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (C : Set G)).inv_mem (hCN g.property))
    rw [hBmap,hCmap] at hh
    exact hh
  have hfull : Q ≤ ⁅Q,L⁆ ⊔ D := by
    calc
      Q = A ⊔ B ⊔ D := data.core_generation
      _ ≤ C := sup_le (sup_le hAC hBC) le_sup_right
  have hF : twoResidualIn L = F :=
    eight_six_equation_one_residual_eq_initial ctx.sectionSeven Γ cp previous D L Q hL data
  have hSyl := eight_six_sylow_intersection_of_residual_le P L S data.closure_le
    (edge_sylow_data ctx.sectionSeven Γ cp).1
    ((Γ.twoResidualAt_def cp.a).symm.le.trans data.residual_le)
  have hgen : F ⊔ (Q ⊔ R) = L := by
    have hh := twoResidualIn_sup_sylow hSyl
    rw [hF,data.sylow_intersection] at hh
    change F ⊔ (V ⊔ Q) = L at hh
    have hRle : R ≤ V ⊔ Q :=
      (le_inf hRL (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2).trans_eq
        data.sylow_intersection
    have hVR : V ≤ R := by
      have hVS : V ≤ S := (le_sup_left.trans data.sylow_intersection.symm.le).trans inf_le_right
      have hVnormal : (V.subgroupOf (GAt Γ cp.firstStep)).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (stabilizer_le_normalizer_v Γ cp.firstStep)
      have hVtwo : IsPGroup 2 V :=
        (show IsPGroup 2 S from by
          obtain ⟨_,s,hs⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
          exact hs ▸ s.isPGroup'.map (GAt Γ cp.firstStep).subtype).to_le hVS
      change V ≤ Γ.twoCoreAt cp.firstStep
      rw [Γ.twoCoreAt_def]
      have hVN : V ≤ GAt Γ cp.firstStep := hVS.trans (edge_sylow_data ctx.sectionSeven Γ cp).2.1
      rw [←Subgroup.map_subgroupOf_eq_of_le hVN]
      exact Subgroup.map_mono (le_sSup ⟨hVnormal,hVtwo.comap_subtype⟩)
    have hsup : Q ⊔ R = V ⊔ Q := le_antisymm
      (sup_le le_sup_right hRle) (sup_le (hVR.trans le_sup_right) le_sup_left)
    rw [hsup]
    exact hh
  have hMQ : M ≤ Q := sup_le
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hFL.trans (data.closure_le.trans hQN)))
    (data.core_generation ▸ le_sup_right)
  have hMN : P ≤ Subgroup.normalizer (M : Set G) := by
    intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change M.map (MulAut.conj g).toMonoidHom = M
    simp only [MulEquiv.toMonoidHom_eq_coe]
    rw [Subgroup.map_sup,Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQN hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hFN hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDN hg)]
  let Qi := Q.subgroupOf L
  let Ri := R.subgroupOf L
  let Fi := F.subgroupOf L
  let Mi := M.subgroupOf L
  let _ : Qi.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (data.closure_le.trans hQN)
  let _ : Fi.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (data.closure_le.trans hFN)
  let _ : Mi.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (data.closure_le.trans hMN)
  have hQi : IsPGroup 2 Qi := (hQ ▸ eight_six_two_core_is_two_group L).of_equiv
    (Subgroup.subgroupOfEquivOfLe hQL).symm
  have hRi : IsPGroup 2 Ri := (show IsPGroup 2 R from by
    change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _).of_equiv
      (Subgroup.subgroupOfEquivOfLe hRL).symm
  have hgeni : Fi ⊔ (Qi ⊔ Ri) = ⊤ := by
    rw [←Subgroup.subgroupOf_sup hQL hRL,
      ←Subgroup.subgroupOf_sup hFL (sup_le hQL hRL),hgen,Subgroup.subgroupOf_self]
  have hfulli : Qi ≤ ⁅Qi,(⊤ : Subgroup L)⁆ ⊔ Mi := by
    apply (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp
    rw [Subgroup.map_sup,Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hQL,
      Subgroup.map_subgroupOf_eq_of_le (hMQ.trans hQL),
      ←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact hfull.trans (sup_le_sup le_rfl le_sup_right)
  have hcommi : ⁅Qi,Fi⁆ ≤ Mi := by
    apply (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hQL,
      Subgroup.map_subgroupOf_eq_of_le hFL,Subgroup.map_subgroupOf_eq_of_le (hMQ.trans hQL)]
    exact le_sup_left
  have hresult := Subgroup.le_normal_of_full_commutator_normal_supplement Qi Ri Fi Mi hQi hRi hgeni hfulli hcommi
  apply le_antisymm ?_ hMQ
  intro q hq
  exact hresult (show (⟨q,hQL hq⟩:L) ∈ Qi from hq)
end Stellmacher.SectionEight
