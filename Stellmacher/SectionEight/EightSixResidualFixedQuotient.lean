module
public import Stellmacher.SectionEight.EightSixNextQuotientModule
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual

/-!
# The quotient by the actual selected residual-fixed subgroup

For E in the next stabilizer of the distance-two configuration, let
C=Vnext intersect C_G(O²(E)). The literal quotient Vnext/C is elementary
abelian and has an E-conjugation action. The next two-core intersect E acts
trivially, and the image of O²(E) has no nonidentity fixed vector. The normality
proof, action, and exact representative formula are retained together.

The first-commutator identity places the next center line inside C and
controls the derived subgroup and squares of Vnext, giving the quotient
structure and kernel. A vector fixed modulo C defines the inverse-commutator
homomorphism O²(E)→C: the residual centralizes C, so inversion corrects the
order in the commutator product identity even when C is nonabelian. Residual
perfection kills this homomorphism into the two-group C, hence the vector
already lies in C.

This packet supplies the actual quotient on which the selected actor is a
transvection in Stellmacher (8.6)(13), Journal of Algebra 190 (1997), printed
p.43. It assumes no quotient model, coprime decomposition, or action bound.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u

private theorem residual_fixed_lift
    {G : Type u} [Group G] [Finite G] (E C : Subgroup G)
    (hCtwo : IsPGroup 2 C)
    (hcentral : C ≤ Subgroup.centralizer (twoResidualIn E : Set G))
    (v : G) (hdelta : ∀ r ∈ twoResidualIn E, ⁅r,v⁆ ∈ C) :
    v ∈ Subgroup.centralizer (twoResidualIn E : Set G) := by
  let R := twoResidualIn E
  let phi : R →* C := {
    toFun := fun r => ⟨⁅(r:G),v⁆⁻¹,C.inv_mem (hdelta r r.property)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅(a:G)*(b:G),v⁆⁻¹ = ⁅(a:G),v⁆⁻¹ * ⁅(b:G),v⁆⁻¹
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hcomm : (a:G)*⁅(b:G),v⁆ = ⁅(b:G),v⁆*(a:G) :=
        Subgroup.mem_centralizer_iff.mp (hcentral (hdelta b b.property)) a a.property
      rw [hcomm,mul_inv_cancel_right,mul_inv_rev] }
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquot : IsPGroup 2 (R ⧸ phi.ker) :=
    (hCtwo.to_subgroup phi.range).of_equiv (QuotientGroup.quotientKerEquivRange phi).symm
  have hker := BenderSuzuki.External.hktPResidual_le phi.ker inferInstance hquot
  rw [show BenderSuzuki.External.hktPResidual 2 R = ⊤ from
    twoResidualAmbient_has_top_twoResidual E] at hker
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hone := congrArg Subtype.val
    (MonoidHom.mem_ker.mp (hker (show (⟨r,hr⟩:R) ∈ ⊤ from trivial)))
  change ⁅r,v⁆⁻¹ = 1 at hone
  exact commutatorElement_eq_one_iff_mul_comm.mp (inv_eq_one.mp hone)

public theorem eight_six_residual_fixed_quotient_module
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep)
    (E : Subgroup G) (hEP : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep) :
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
    ∃ hN : (C.subgroupOf V).Normal, let _ := hN
      ∃ _hW : IsElementaryAbelian 2 (V ⧸ C.subgroupOf V),
        ∃ action : E →* MulAut (V ⧸ C.subgroupOf V),
          (∀ actor : E, ∀ point : V,
            action actor (QuotientGroup.mk' (C.subgroupOf V) point) =
              QuotientGroup.mk' (C.subgroupOf V)
                ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
                  (Subgroup.mem_normalizer_iff.mp
                    (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                      (hEP actor.property)) point).mp point.property⟩) ∧
          (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf E ≤ action.ker ∧
          FixedPoints.subgroup
            ((twoResidualAmbient (⊤ : Subgroup E)).map action)
            (V ⧸ C.subgroupOf V) = ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let R := twoResidualIn E
  let C := V ⊓ Subgroup.centralizer (R : Set G)
  have hRE : R ≤ E := twoResidualIn_le E
  have hRP := hRE.trans hEP
  have hVQ : V ≤ Q := neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    hEP.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZC : Z ≤ C := le_inf hZV
    ((hcenter.trans (centerAmbient_le_centralizer _)).trans (Subgroup.centralizer_le hRP))
  have hVV : ⁅V,V⁆ ≤ C := ((Subgroup.commutator_mono le_rfl hVQ).trans_eq hcomm).trans hZC
  have hN : (C.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.le_normalizer_iff_commutator_le_left.mpr
        ((Subgroup.commutator_mono inf_le_left le_rfl).trans hVV))
  let _ := hN
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRE).mp (twoResidualIn_normal E)
  have hEC : E ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf hEV (hER.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (R : Set G))).mp inferInstance))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨hNZ,hWZ,_⟩ := eight_six_next_quotient_module_data_local
    ctx hcenter hlength hcard hcomm
  let _ := hNZ
  let _ := hWZ
  have hderived : _root_.commutator V ≤ C.subgroupOf V := by
    intro v hv
    apply hVV
    have hm : (_root_.commutator V).map V.subtype = ⁅V,V⁆ := by
      rw [_root_.commutator_def,Subgroup.map_commutator,← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    exact hm ▸ Subgroup.mem_map_of_mem V.subtype hv
  have hW : IsElementaryAbelian 2 (V ⧸ C.subgroupOf V) := {
    toIsMulCommutative := (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := C.subgroupOf V)).mpr hderived
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro w
      obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf V) w
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply hZC
      have hp : (QuotientGroup.mk' (Z.subgroupOf V) v)^2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ Z.subgroupOf V)) _
      rw [← map_pow] at hp
      exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) (v ^ 2)).mp hp) }
  obtain ⟨action,haction⟩ := Subgroup.exists_quotient_conjugation_action E V C hEV hEC hN
  refine ⟨hN,hW,action,haction,?_,?_⟩
  · exact Subgroup.quotient_conjugation_action_kills_commutator_layer
      E V C Q hN hEV (hcomm.le.trans hZC) action haction
  · have hQtwo : IsPGroup 2 Q := by
      change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    have hCtwo : IsPGroup 2 C := hQtwo.to_le (inf_le_left.trans hVQ)
    have hRmap : (twoResidualAmbient (⊤ : Subgroup E)).map E.subtype = R :=
      map_twoResidualAmbient_of_subgroup_image ⊤ E.subtype E (by
        rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
    have hRint : R.subgroupOf E = twoResidualAmbient (⊤ : Subgroup E) := by
      apply Subgroup.map_injective E.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hRE,hRmap]
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf V) w
    apply Subgroup.mem_bot.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨v.property,residual_fixed_lift E C hCtwo inf_le_right v ?_⟩
    intro r hr
    let rE : E := ⟨r,hRE hr⟩
    have hrint : rE ∈ twoResidualAmbient (⊤ : Subgroup E) := by
      rw [←hRint]
      exact hr
    have hh := hw ⟨action rE,Subgroup.mem_map_of_mem action hrint⟩
    change action rE (QuotientGroup.mk' (C.subgroupOf V) v) =
      QuotientGroup.mk' (C.subgroupOf V) v at hh
    rw [haction] at hh
    have hmem := QuotientGroup.eq_iff_div_mem.mp hh
    change r*(v:G)*r⁻¹/(v:G) ∈ C at hmem
    simpa only [commutatorElement_def,div_eq_mul_inv] using hmem

end Stellmacher.SectionEight
