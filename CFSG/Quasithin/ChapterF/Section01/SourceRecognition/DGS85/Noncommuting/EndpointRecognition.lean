module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointSections
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.Field.ULift
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.Representation.BinaryConjugationSection.Projection
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import Theory.GroupTheory.PResidual.TwiceOddPrime
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness

/-!
# Residual fixed vectors and faithful critical endpoint sections

For the actual linear local quotient, the full endpoint center has the same
O²-fixed vectors as global fixed vectors. For fields of order at least four,
this follows from perfectness. At field order two, the normal subgroup of
order three and Sylow-fixed generation give the equality. The kernel of the
literal central-omega projection is exactly the global fixed space. Lifting
fixed vectors through this central kernel therefore kills all residual-fixed
vectors in the quotient. Simplicity, or the small intrinsic core-free quotient
argument, then proves faithfulness of the same nonzero section.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126–127, using the
corrected fixed-generation premise of (5.12). `EndpointRecognitionSource`
applies this to the actual constructed critical sections in both orientations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped commutatorElement IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

private theorem residual_fixed_free_of_projection
    {D U W : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D U) (σ : Representation (ZMod 2) D W)
    (f : U →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (he : ∀ g u, f (ρ g u) = σ g (f u))
    (hk : f.ker = fixedSpace ρ ⊤)
    (hr : fixedSpace ρ (pResidual 2 D) = fixedSpace ρ ⊤) :
    fixedSpace σ (pResidual 2 D) = ⊥ := by
  apply bot_unique
  intro w hw
  obtain ⟨v,rfl⟩ := hf w
  have hv := fixed_of_pPerfect_central_kernel ρ (pResidual 2 D)
    (isPPerfect_pResidual 2) f (hk ▸ fixedSpace_antitone ρ le_top) v
    (fun a => (he a v).trans (hw a))
  have hvk : v ∈ f.ker := hk.symm ▸ (hr ▸ hv : v ∈ fixedSpace ρ ⊤)
  exact hvk

private theorem linear_residual_fixed_eq_global
    {D U F : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U]
    [Field F] [Finite F] [CharP F 2]
    (ρ : Representation (ZMod 2) D U) (T : Sylow 2 D)
    (hg : GeneratedByFixedSpace ρ T) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (e : D ≃* SL(2,F)) :
    fixedSpace ρ (pResidual 2 D) = fixedSpace ρ ⊤ := by
  by_cases hn1 : n = 1
  · have hc : Nat.card D = 2*3 := by
      rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF,hn1]
      norm_num
    have ho : Odd (Nat.card (pResidual 2 D)) := by
      rw [card_twoResidual_of_card_twice_odd_prime (by decide : Odd 3) hc]
      decide
    apply NormalOddSeed.fixed_eq ρ ⊤ (pResidual 2 D) T ho
      (by rw [top_inf_eq,pResidual_sup_sylow_eq_top]) (fixedSpace ρ T) le_rfl
    apply top_unique
    rw [←hg]
    apply iSup_le
    rintro g _ ⟨v,hv,rfl⟩
    exact Submodule.subset_span ⟨g,v,hv,rfl⟩
  · have hlarge : 4 ≤ Nat.card F := by
      rw [hF]
      exact (show 4 = 2^2 from rfl).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    let : Group.IsPerfect SL(2,F) := SL2SylowFixedRecognition.perfect hlarge
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hp : IsPPerfect 2 D := by
      intro N hN hq
      let : N.Normal := hN
      by_contra hne
      let : Nontrivial (D ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
      exact Group.IsPerfect.not_isNilpotent (D ⧸ N) hq.isNilpotent
    rw [(pResidual_eq_top_iff 2 D).mpr hp]

universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The literal central endpoint quotient has no residual-fixed vectors
once the actual acting quotient has been recognized as linear. -/
theorem graph_endpoint_section_residual_fixed_bot_of_linear
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    (E : Subgroup G) (c : LocalRankOneData (stabilizer (family P) v) E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    [((Q (family P) v).subgroupOf c.Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar) W)
    (s : BinaryConjugationSection c.Pstar (Z (family P) v)
      (Stellmacher.omegaOneCenterAmbient c.Pstar)
      (σ.comp (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar))))
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar) 2 (2^n)) :
    fixedSpace σ (pResidual 2 (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar)) = ⊥ := by
  let := finite_endpoints h
  let := graph_Z_elementary h v
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let π := QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar)
  obtain ⟨ρ,r,hr⟩ := graph_endpoint_full_action_exists h v E c hodd
  obtain ⟨f,hf,hfcoord,hfker⟩ := exists_projection c.Pstar c.Pstar (Z (family P) v) ⊥
    (Stellmacher.omegaOneCenterAmbient c.Pstar) le_rfl bot_le π π
    (QuotientGroup.mk'_surjective _) (MonoidHom.id _) (fun _ => rfl) ρ σ r s
  apply residual_fixed_free_of_projection ρ σ f.toLinearMap hf
    (fun g z => LinearMap.congr_fun (f.isIntertwining' g) z)
  swap
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    let e' := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
    let T := c.sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
    exact linear_residual_fixed_eq_global ρ T
      (sylow_span_fixedSpace_generated c.Pstar _ ⊥ ρ π r c.sylow
        (local_center_span _ _ c hodd)) hn hcard e'
  rw [hfker]
  apply le_antisymm
  · intro z hz a
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective ((Q (family P) v).subgroupOf c.Pstar) a.val
    change ρ a.val z = z
    rw [←hl]
    have hc : ⁅c.Pstar,Stellmacher.omegaOneCenterAmbient c.Pstar⁆ = ⊥ := by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
      exact fun z hz => (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2
    exact r.fixed_on_imageSpace_of_commutator_le c.Pstar _ hc.le l l.property z hz
  · intro z hz
    obtain ⟨a,ha⟩ := r.onto (Multiplicative.ofAdd z)
    have haz : (r.coordinates a).toAdd = z := congrArg Multiplicative.toAdd ha
    apply (r.mem_imageSpace_iff _ _).mpr
    refine ⟨a,?_,haz⟩
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨r.section_le a.property,
      elemPow_eq_one_of_isElementaryAbelian (a : G) a.property,?_⟩
    intro l hl
    have hh : ⁅(a : G),l⁆ = 1 := mem_bot.mp
      ((r.fixed_coordinate_iff_commutator_mem ⟨l,hl⟩ a).mp (by
        change ρ (π ⟨l,hl⟩) (r.coordinates a).toAdd = _
        rw [haz]
        exact hz ⟨π ⟨l,hl⟩,mem_top _⟩))
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

/-- A linear model of the actual local quotient discharges both remaining
recognition conditions on the same nonzero endpoint section. -/
theorem graph_endpoint_linear_recognition_inputs
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    (E : Subgroup G) (c : LocalRankOneData (stabilizer (family P) v) E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    [((Q (family P) v).subgroupOf c.Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar) W)
    (s : BinaryConjugationSection c.Pstar (Z (family P) v)
      (Stellmacher.omegaOneCenterAmbient c.Pstar)
      (σ.comp (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar))))
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar) 2 (2^n)) :
    Nonempty (BinaryRankOneModel (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar)) ∧
    Function.Injective σ ∧
    fixedSpace σ (pResidual 2 (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar)) = ⊥ := by
  let := finite_endpoints h
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  have hr := graph_endpoint_section_residual_fixed_bot_of_linear h v E c hodd σ s hn hm
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  let e' := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let ρ := σ.comp e'.symm.toMonoidHom
  have hcore : (Q (family P) v).subgroupOf c.Pstar = pCore 2 c.Pstar := by
    rw [show Q (family P) v = c.Pstar.pCoreIn 2 from c.same_core.symm]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  let eQ := (QuotientGroup.quotientMulEquivOfEq hcore).symm.trans e'
  have hr' : fixedSpace ρ (pResidual 2 SL(2,F)) = ⊥ := by
    rw [fixedSpace_comp_map,map_pResidual_of_surjective 2 e'.symm.toMonoidHom e'.symm.surjective]
    exact hr
  have hf := CommutingNontrivial.linear_quotient_action_faithful hn hcard eQ ρ hr'
  let k := ULift.{u} F
  let eK : SL(2,F) ≃* SL(2,k) := Atlas.fieldEquivSL 2 ULift.ringEquiv.symm
  have hK : Nat.card k = 2^n := (Nat.card_congr Equiv.ulift).trans hcard
  refine ⟨⟨.sl2 k n hn hK (e'.trans eK)⟩,?_,hr⟩
  intro a b hab
  apply e'.injective
  apply hf
  simpa only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e'.symm_apply_apply] using hab

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
