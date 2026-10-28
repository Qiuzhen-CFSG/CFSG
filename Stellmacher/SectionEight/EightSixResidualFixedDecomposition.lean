module
public import Stellmacher.SectionEight.EightSixNextQuotientModule
public import Stellmacher.SectionThree.ResidualImageOddPGroup
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# Selected-residual fixed decompositions in (8.6)

Retain a supplied conjugation action of the next stabilizer on the literal
quotient of a normalized subgroup V containing Znext, with the next two-core
in its kernel. The quotient must be elementary abelian. The original
Vnext/Znext theorem remains as an exact wrapper. For every selected
subgroup E of that stabilizer, the image of O²(E) has odd order. Its fixed
subgroup is exactly the image of C=V intersect C_G(O²(E)); the quotient
splits as its fixed subgroup and its action commutator. This also gives the
raw equality V=[V,O²(E)] join C.

The local data from (7.3) and the residual theorem (3.3) give odd image for
the full next residual. Residual minimality places O²(E) in that residual.
To identify the fixed lift, a quotient-fixed vector defines a homomorphism
from O²(E) to the central next line of order two. Residual perfection makes
this homomorphism trivial. Coprime fixed/commutator decomposition on the
provided elementary quotient then lifts through the next line, which lies
in C. The proof preserves the caller's normality proof and literal action;
it requires no stronger selector or quotient-dihedral assumption.

This is the fixed-module packet used in Stellmacher (8.6)(13)–(14) and
the full-core quotient transfer in (18), Journal of Algebra 190 (1997),
printed pp.43–45 of
`refs/files/stellmacher-n-group.pdf`. The previously proved source-(8)
containment [Qnext,O²(E)]≤Vnext lets consumers replace the raw commutator by
Y=[Qnext,O²(E)] in the generating equality.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u

private theorem central_two_fixed_lift
    {G : Type u} [Group G] [Finite G] (E Z : Subgroup G)
    (hZcard : Nat.card Z = 2) (hZcent : Z ≤ Subgroup.centralizer (E : Set G))
    (v : G) (hdelta : ∀ r ∈ twoResidualIn E, ⁅r,v⁆ ∈ Z) :
    v ∈ Subgroup.centralizer (twoResidualIn E : Set G) := by
  let R := twoResidualIn E
  let _ : IsCyclic Z := isCyclic_of_prime_card hZcard
  let phi : R →* Z := {
    toFun := fun r => ⟨⁅(r:G),v⁆,hdelta r r.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅(a:G)*(b:G),v⁆ = ⁅(a:G),v⁆ * ⁅(b:G),v⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hcomm : (a:G)*⁅(b:G),v⁆ = ⁅(b:G),v⁆*(a:G) :=
        Subgroup.mem_centralizer_iff.mp (hZcent (hdelta b b.property)) a
          (twoResidualIn_le E a.property)
      rw [hcomm,mul_inv_cancel_right]
      exact congrArg Subtype.val
        (mul_comm (⟨⁅(b:G),v⁆,hdelta b b.property⟩ : Z)
          ⟨⁅(a:G),v⁆,hdelta a a.property⟩) }
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hquot : IsPGroup 2 (R ⧸ phi.ker) :=
    (hZtwo.to_subgroup phi.range).of_equiv (QuotientGroup.quotientKerEquivRange phi).symm
  have hker := BenderSuzuki.External.hktPResidual_le phi.ker inferInstance hquot
  rw [show BenderSuzuki.External.hktPResidual 2 R = ⊤ from
    twoResidualAmbient_has_top_twoResidual E] at hker
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hone := congrArg Subtype.val (MonoidHom.mem_ker.mp (hker (show (⟨r,hr⟩:R) ∈ ⊤ from trivial)))
  change ⁅r,v⁆ = 1 at hone
  exact commutatorElement_eq_one_iff_mul_comm.mp hone

private theorem selected_residual_image_odd
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    {S P1 P2 : Subgroup G} (ctx : SectionEightLocalContext G S P1 P2)
    (E : Subgroup G) (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* X)
    (hker : pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep) ≤ f.ker) :
    Odd (Nat.card (((twoResidualIn E).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map f)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let edgeSylow : Sylow 2 (P ⊓ GAt Γ cp.a : Subgroup G) := default
  let edge := sylowTwoAmbient (P ⊓ GAt Γ cp.a) edgeSylow
  have hdata := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) edgeSylow
  obtain ⟨prime,hprime,hodd,himage⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    edge hdata.1 P hdata.2.1 hdata.2.2.2.1 f hker
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hres : twoResidualIn E ≤ twoResidualIn P := by
    have hs := (edge_sylow_data ctx.sectionSeven Γ cp).2
    have hgen : twoResidualIn P ⊔ S = P := twoResidualIn_sup_sylow hs
    have hn : ((twoResidualIn P).subgroupOf (twoResidualIn P ⊔ S)).Normal := by
      rw [hgen]
      exact twoResidualIn_normal P
    have hp : IsPGroup 2 S := by
      obtain ⟨_,s,hs⟩ := hs
      exact hs ▸ s.isPGroup'.map P.subtype
    exact SectionThree.twoResidualAmbient_le_left_of_le_sup (twoResidualIn P) S E
      hn hp (hE.trans_eq hgen.symm)
  have hnative : (twoResidualIn P).subgroupOf P = twoResidualSubgroup P := by
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hle : ((twoResidualIn E).subgroupOf P).map f ≤ (twoResidualSubgroup P).map f := by
    rw [← hnative]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P hres)
  obtain ⟨n,hn⟩ := (himage.to_le hle).exists_card_eq
  rw [hn]
  exact hodd.pow

public theorem eight_six_normalized_residual_fixed_decomposition
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (E : Subgroup G) (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (V : Subgroup G)
    (hPV : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (V : Set G))
    (hZV : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ V)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf V).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (_hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
      (action : P →* MulAut (V ⧸ Z.subgroupOf V)),
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (hPV actor.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      let R := twoResidualIn E
      let Rbar := (R.subgroupOf P).map action.rangeRestrict
      let C := V ⊓ Subgroup.centralizer (R : Set G)
      Odd (Nat.card Rbar) ∧
        (C.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V)) =
          FixedPoints.subgroup Rbar (V ⧸ Z.subgroupOf V) ∧
        IsCompl (FixedPoints.subgroup Rbar (V ⧸ Z.subgroupOf V))
          (commutatorAction Rbar (V ⧸ Z.subgroupOf V)) ∧
        V = ⁅V,R⁆ ⊔ C := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let R := twoResidualIn E
  let Rbar := (R.subgroupOf P).map action.rangeRestrict
  let C := V ⊓ Subgroup.centralizer (R : Set G)
  let fixed := FixedPoints.subgroup Rbar W
  let projection := QuotientGroup.mk' (Z.subgroupOf V)
  have hRP : R ≤ P := (twoResidualIn_le E).trans hE
  have hkernelRange : pCore 2 P ≤ action.rangeRestrict.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp (hkernel hx)
  have hodd : Odd (Nat.card Rbar) := selected_residual_image_odd ctx E hE
    action.rangeRestrict hkernelRange
  have hZdata := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hZcard : Nat.card Z = 2 := hZdata.1
  have hZP : Z ≤ Subgroup.centralizer (P : Set G) :=
    hcenter.trans (centerAmbient_le_centralizer _)
  have hZE : Z ≤ Subgroup.centralizer (E : Set G) :=
    hZP.trans (Subgroup.centralizer_le hE)
  have hfixedPreimage : fixed.comap projection = C.subgroupOf V := by
    ext v
    constructor
    · intro hv
      refine ⟨v.property, central_two_fixed_lift E Z hZcard hZE v ?_⟩
      intro r hr
      let rP : P := ⟨r,hRP hr⟩
      have hrbar : action.rangeRestrict rP ∈ Rbar :=
        Subgroup.mem_map_of_mem action.rangeRestrict hr
      have heq := (FixedPoints.mem_subgroup (M := Rbar) (a := projection v)).mp hv
        ⟨action.rangeRestrict rP,hrbar⟩
      change action rP (projection v) = projection v at heq
      rw [haction] at heq
      have hmem := QuotientGroup.eq_iff_div_mem.mp heq
      change r*(v:G)*r⁻¹/(v:G) ∈ Z at hmem
      simpa only [commutatorElement_def,div_eq_mul_inv] using hmem
    · intro hv
      rw [Subgroup.mem_comap,FixedPoints.mem_subgroup]
      intro r
      obtain ⟨p,hp,heq⟩ := r.property
      change ((r:Rbar):action.range) • projection v = projection v
      rw [← heq]
      change action p (projection v) = projection v
      rw [haction]
      apply congrArg projection
      apply Subtype.ext
      have hcomm : (p:G)*(v:G) = (v:G)*(p:G) :=
        Subgroup.mem_centralizer_iff.mp hv.2 p hp
      change (p:G)*(v:G)*(p:G)⁻¹ = (v:G)
      rw [hcomm,mul_inv_cancel_right]
  have hfixedImage : (C.subgroupOf V).map projection = fixed := by
    rw [← hfixedPreimage]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (Z.subgroupOf V)) fixed
  have hcop : Nat.Coprime (Nat.card Rbar) (Nat.card W) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hcompl : IsCompl fixed (commutatorAction Rbar W) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := Rbar) (Group.isSolvable_of_comm fun x y => mul_comm x y)
      hcop inferInstance
  refine ⟨hodd,hfixedImage,hcompl,?_⟩
  have hcommV : ⁅V,R⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hRP.trans hPV)
  have hZC : Z ≤ C := le_inf hZV (hZP.trans (Subgroup.centralizer_le hRP))
  have hactorImage : Rbar.map action.range.subtype = (R.subgroupOf P).map action := by
    rw [Subgroup.map_map]
    rfl
  have hcommImage : (⁅V,R⁆.subgroupOf V).map projection = commutatorAction Rbar W := by
    rw [← commutatorAction_map_actor_subtype action.range Rbar, hactorImage]
    exact (Subgroup.quotient_conjugation_commutatorAction_eq_image
      P V Z R hPV hRP hN action haction).symm
  let K := ⁅V,R⁆ ⊔ C
  have hKImage : (K.subgroupOf V).map projection = ⊤ := by
    rw [show K = ⁅V,R⁆ ⊔ C from rfl,
      Subgroup.subgroupOf_sup hcommV (show C ≤ V from inf_le_left),
      Subgroup.map_sup,hcommImage,hfixedImage,sup_comm]
    exact hcompl.sup_eq_top
  have hkernelK : projection.ker ≤ K.subgroupOf V := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.subgroupOf_mono V (hZC.trans le_sup_right)
  have htopK : (⊤ : Subgroup V) ≤ K.subgroupOf V := by
    have hh : (⊤ : Subgroup V) ≤ ((K.subgroupOf V).map projection).comap projection := by
      rw [hKImage,Subgroup.comap_top]
    rwa [Subgroup.comap_map_eq,sup_eq_left.mpr hkernelK] at hh
  apply le_antisymm
  · intro v hv
    exact htopK (show (⟨v,hv⟩:V) ∈ ⊤ from trivial)
  · exact sup_le hcommV inf_le_left

public theorem eight_six_residual_fixed_decomposition
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (_hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (E : Subgroup G) (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (_hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
      (action : P →* MulAut (V ⧸ Z.subgroupOf V)),
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  actor.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      let R := twoResidualIn E
      let Rbar := (R.subgroupOf P).map action.rangeRestrict
      let C := V ⊓ Subgroup.centralizer (R : Set G)
      Odd (Nat.card Rbar) ∧
        (C.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V)) =
          FixedPoints.subgroup Rbar (V ⧸ Z.subgroupOf V) ∧
        IsCompl (FixedPoints.subgroup Rbar (V ⧸ Z.subgroupOf V))
          (commutatorAction Rbar (V ⧸ Z.subgroupOf V)) ∧
        V = ⁅V,R⁆ ⊔ C := by
  exact eight_six_normalized_residual_fixed_decomposition ctx hcenter hcard E hE
    (VAt ctx.Γ ctx.criticalPath.firstStep) (stabilizer_le_normalizer_v ctx.Γ _)
    ((eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
      (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1) hN

end Stellmacher.SectionEight
