module
public import Stellmacher.SectionEight.EightSixCostFourFixedCoreCard
public import Stellmacher.SectionEight.EightSixResidualFixedDecomposition

/-!
# The Sylow order interval in the cost-four branch

The original selected cost-four configuration of Stellmacher (8.6) satisfies
2^8≤|S|≤2^10 for the prescribed edge Sylow subgroup S. The theorem retains
the local graph, equation-one packet and selected geometric witnesses; all
quotients and projections are constructed from these data.

Write R for the next two-core, V for its neighbor module, Z for the next
central line, and V0 for the centralizer of O²(E) in R. The Frattini equality
Φ(R)=Z makes R/Z elementary. Its literal conjugation action permits the
normalized residual decomposition R=[R,O²(E)]V0. Module saturation gives
V=[R,O²(E)] of order32, and the residual decomposition gives V∩V0=Z of
order two. The fixed-core estimate |V0|≤8 therefore gives 32≤|R|≤128.

The actual next wreath quotient sends the given edge Sylow onto a Sylow
of the concrete wreath product, of order eight by its dihedral model.
The restricted projection has exactly R.subgroupOf S as kernel. Thus
|S|=8|R|, yielding the stated interval without assuming any Sylow size or
identifying R with V.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6)(b), printed p.41,
and the cost-four fixed-core argument on p.44. This supplies the numerical
Sylow field of the existing case-B alternative.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_cost_four_sylow_card_bounds
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
    2 ^ 8 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 10 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let V0 := R ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hVR : V ≤ R := neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hZline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hZV : Z ≤ V := hZline.2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := stabilizer_le_normalizer_q Γ _
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ _
  have hN : (Z.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRP.trans hPZ)
  let _ := hN
  have hRtwo : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt _)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 R) := ⟨hRtwo⟩
  have hbase := eight_six_common_structure_local ctx hcenter hquot hlength hcard previous hprev
    D L Q hD hL hQ
  have hPhi : FrattiniAmbient R = Z := eight_six_next_core_frattini ctx hcenter hlength hcard
    previous D L Q hprev.1 hD hL data hbase.2.2.2
  have hPhiNative : frattini R ≤ Z.subgroupOf R := by
    intro r hr
    exact hPhi.le (Subgroup.mem_map_of_mem R.subtype hr)
  have hWR : IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R) :=
    Subgroup.elementary_quotient_of_frattini_le hRtwo (Z.subgroupOf R) hPhiNative
  let _ := hWR
  have hRR : ⁅R,R⁆ ≤ Z := by
    have hh := Subgroup.map_mono (f := R.subtype)
      (commutator_le_frattini_of_isPGroup (p := 2) (R := R))
    rw [Subgroup.map_subtype_commutator] at hh
    exact hh.trans_eq hPhi
  obtain ⟨action,haction⟩ := Subgroup.exists_quotient_conjugation_action P R Z hPR hPZ hN
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt _).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hkernel : pCore 2 P ≤ action.ker := by
    have hh := Subgroup.quotient_conjugation_action_kills_commutator_layer
      P R Z R hN hPR hRR action haction
    rw [hRnative] at hh
    exact hh
  have hsplit := (eight_six_normalized_residual_fixed_decomposition ctx hcenter hcard
    E geom.group_le R hPR (hZV.trans hVR) hN hWR action haction hkernel).2.2.2
  obtain ⟨hNV,hWV,vaction,hvformula,hvkernel,hvgenerate⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  have hVY : V = ⁅R,twoResidualIn E⁆ := (eight_six_cost_four_full_module_card
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hcost hNV hWV vaction hvformula hvkernel hvgenerate).2
  have hVcard : Nat.card V = 32 := by
    rw [hVY]
    exact (eight_six_cost_four_residual_card ctx hcenter hquot hlength hcard previous
      D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).1
  have hgen : R = V ⊔ V0 := by
    change R = ⁅R,twoResidualIn E⁆ ⊔ V0 at hsplit
    rwa [← hVY] at hsplit
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hfixedV : V ⊓ Subgroup.centralizer (twoResidualIn E : Set G) = Z := by
    have hh := hpacket.2.1
    change ⁅R,twoResidualIn E⁆ ⊓ (V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)) = Z at hh
    rw [← hVY] at hh
    simpa only [← inf_assoc,inf_idem] using hh
  have hinter : V ⊓ V0 = Z := by
    change V ⊓ (R ⊓ Subgroup.centralizer (twoResidualIn E : Set G)) = Z
    rw [← inf_assoc,inf_eq_left.mpr hVR]
    exact hfixedV
  have hnorm : V0 ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (hRP.trans (stabilizer_le_normalizer_v Γ _))
  have hV0bound : Nat.card V0 ≤ 8 := (eight_six_cost_four_fixed_core_card_bound
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hcost).2
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes V V0 hnorm
  rw [hVcard,hinter,hZline.1,← hgen] at hprod
  have hRlower : 32 ≤ Nat.card R := hVcard ▸ Subgroup.card_le_of_le hVR
  have hRupper : Nat.card R ≤ 128 := by omega
  obtain ⟨f,hfsurj,hfker⟩ := eight_six_cost_four_next_quotient ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  obtain ⟨hSP,sylow,hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hSnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hsylow,Subgroup.map_subgroupOf_eq_of_le hSP]
  let T := sylow.mapSurjective hfsurj
  have hTmap : (T : Subgroup SL2TwoWreathC2) = (S.subgroupOf P).map f := by
    change (sylow : Subgroup P).map f = _
    rw [hSnative]
  have hTcard : Nat.card T = 8 := by
    obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four T
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  let projection : S →* T := (f.comp (Subgroup.inclusion hSP)).codRestrict T (by
    intro s
    change f (Subgroup.inclusion hSP s) ∈ (T : Subgroup SL2TwoWreathC2)
    rw [hTmap]
    exact ⟨Subgroup.inclusion hSP s,s.property,rfl⟩)
  have hsurj : Function.Surjective projection := by
    intro t
    have ht : (t:SL2TwoWreathC2) ∈ (S.subgroupOf P).map f := by
      rw [← hTmap]
      exact t.property
    obtain ⟨p,hp,hpt⟩ := ht
    exact ⟨⟨p,hp⟩,Subtype.ext hpt⟩
  have hker : projection.ker = R.subgroupOf S := by
    ext s
    change projection s = 1 ↔ (s:G) ∈ R
    rw [Subtype.ext_iff]
    change f (Subgroup.inclusion hSP s) = 1 ↔ (s:G) ∈ R
    rw [← MonoidHom.mem_ker,hfker]
    rfl
  have hScard : Nat.card S = Nat.card R * 8 := by
    have hh := projection.ker.card_mul_index
    rw [Subgroup.index_ker,hker] at hh
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2).toEquiv] at hh
    rw [projection.range_eq_top_of_surjective hsurj,Subgroup.card_top,hTcard] at hh
    exact hh.symm
  rw [hScard]
  norm_num only [Nat.reducePow]
  omega
end Stellmacher.SectionEight
