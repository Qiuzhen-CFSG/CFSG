module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureFullActor
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.AlternatingEightImage
public import Theory.Representation.BinaryConjugationSection.PointCentralizerImage
public import Theory.SpecificGroups.BinaryLinear.FivePointQuotient
public import Theory.GroupTheory.CComponent.CentralizerMovement
import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
import Theory.GroupTheory.CComponent.ResidualLifting

/-!
# The original degree-five point-centralizer component

The unchanged closure R maps onto the full binary linear group. Its
centralizer of V1 maps onto the full point parabolic, by odd-order lifting
through the central denominator <z>. The actual SL4(2) Levi image lifts
to a C-component using the proved earlier residual-generation sources.
R is normal in C_G(z), so this component promotes to N_G(V1). Its exact
intrinsic two-core quotient is A8; no action-kernel premise is imposed.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open ChapterA.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem sqtk_eight_component {Y : Type*} [Group Y] [Finite Y]
    (hY : IsSQTK KnownSimple.IsKnownSimple Y)
    (f : Y →* alternatingGroup (Fin 8)) (hf : Function.Surjective f) :
    ∃ B : Subgroup Y, B.IsCComponent ∧ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 8)) := by
  let A := alternatingGroup (Fin 8)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple A := { simple :=
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (⊤ : Subgroup A) := IsQuasisimple.of_mulEquiv topEquiv.symm
  let P := (⊤ : Subgroup A).comap f
  have hP := hY.subgroup P
  have hq : IsSQTK KnownSimple.IsKnownSimple (P ⧸ pCore 2 P) := by
    refine ⟨?_,hP.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hP.stronglyQuasithin p hp ho)
  have hgen := Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
      (fun A _ _ => theoremA_knownSimple (G := A))
      (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
        (fun A _ _ => theoremC_knownSimple (G := A))) hX hO) hq
  obtain ⟨B,hB,him⟩ := exists_cComponent_map_eq_of_preimage_layer f hf
    (show (⊤ : Subgroup (alternatingGroup (Fin 8))).IsCComponent from
      (show IsComponent (alternatingGroup (Fin 8)) ⊤ from ⟨.top,inferInstance⟩).isCComponent)
    hgen
  let g := f.comp B.subtype
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨b,hb,hbx⟩ := him.symm ▸ mem_top x
    exact ⟨⟨b,hb⟩,hbx⟩
  have hk := ChapterA.Section03.cComponent_alternating_eight_kernel hY hB g hg
  exact ⟨B,hB,⟨QuotientGroup.liftEquiv _ hg hk.symm⟩⟩

private theorem point_eight_component (R P : Subgroup G)
    (π : R →* SL(5,ZMod 2)) (y : Fin 5 → ZMod 2) (hy : y≠0)
    (him : ((centralizer (P:Set G)).subgroupOf R).map π=MulAction.stabilizer SL(5,ZMod 2) y)
    (hn : centralizer (P:Set G)≤normalizer (R:Set G))
    (hC1 : IsSQTK KnownSimple.IsKnownSimple (centralizer (P:Set G))) :
    ∃ B : Subgroup G, B≤R⊓centralizer (P:Set G) ∧
      (B.subgroupOf (normalizer (P:Set G))).IsCComponent ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 8)) := by
  let S := MulAction.stabilizer SL(5,ZMod 2) y
  let C1 := centralizer (P:Set G)
  let D1 := R.subgroupOf C1
  let : D1.Normal := normal_subgroupOf_of_le_normalizer hn
  let f : D1 →* S := {
    toFun := fun d => ⟨π ⟨d,d.property⟩,by
      have hm := mem_map_of_mem π
        (show (⟨((d:C1):G),d.property⟩:R)∈(centralizer (P:Set G)).subgroupOf R from d.val.property)
      rw [him] at hm
      exact hm⟩
    map_one' := Subtype.ext π.map_one
    map_mul' x y := Subtype.ext (π.map_mul (⟨((x:C1):G),x.property⟩:R)
      (⟨((y:C1):G),y.property⟩:R)) }
  have hf : Function.Surjective f := by
    intro s
    have hs : (s:SL(5,ZMod 2))∈((centralizer (P:Set G)).subgroupOf R).map π := by
      rw [him]
      exact s.property
    obtain ⟨r,hr,he⟩ := hs
    exact ⟨⟨⟨r,hr⟩,r.property⟩,Subtype.ext he⟩
  obtain ⟨eS⟩ := BinaryLinear.PointStabilizerRank.five_point_quotient y hy
  let eA := eS.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  let fA := eA.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 S)).comp f)
  obtain ⟨B0,hB0,⟨eB0⟩⟩ := sqtk_eight_component (hC1.subgroup D1) fA
    (eA.surjective.comp ((QuotientGroup.mk'_surjective _).comp hf))
  let B1 := B0.map D1.subtype
  have hB1 : B1.IsCComponent := hB0.map_subtype (inferInstance : D1.Normal).isSubnormal
  let B := B1.map C1.subtype
  have hBR : B≤R := by rintro _ ⟨_,⟨b,hb,rfl⟩,rfl⟩; exact b.property
  have hBC : B≤C1 := map_subtype_le _
  have hsub : B.subgroupOf C1=B1 := comap_map_eq_self_of_injective C1.subtype_injective B1
  have hBN : (B.subgroupOf (normalizer (P:Set G))).IsCComponent :=
    (hsub.symm ▸ hB1).in_normalizer_of_centralizes hBC le_rfl
  let eB : B0 ≃* B := (B0.equivMapOfInjective D1.subtype D1.subtype_injective).trans
    (B1.equivMapOfInjective C1.subtype C1.subtype_injective)
  exact ⟨B,le_inf hBR hBC,hBN,⟨(QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).symm.trans eB0⟩⟩

/-- If the original central closure has order 64, the literal centralizer
R∩C_G(V1) supplies an A8 C-component in the actual N_G(V1). -/
theorem original_tripleSix_central_closure_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    (h64 : Nat.card (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) = 64) :
    let R := conjugateSpanBy U (centralizer ({(z:G)} : Set G))
    let V1 := tripleSixPoint D a z
    ∃ B : Subgroup G, B ≤ R ⊓ centralizer (V1 : Set G) ∧
      (B.subgroupOf (normalizer (V1 : Set G))).IsCComponent ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 8)) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_full_actor
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,-,-,-,x,hx,hpoint,-,-,-,-,-,-,-,-,-,hwhole,hRimage,-⟩ := hrest
  let := he
  let V := Additive (W ⧸ Z.subgroupOf W)
  let q := QuotientGroup.mk' (Z.subgroupOf W)
  have hp := tripleSixPoint_properties D a z hz
  let : IsElementaryAbelian 2 U := D.elementary
  have hz1 : (z:G) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hzorder : orderOf (z:G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) hz1
  have hZcard : Nat.card Z=2 := by rw [Nat.card_zpowers,hzorder]
  have hZV : Z≤V1 := zpowers_le.mpr hp.1
  have hVW : V1≤W := le_conjugateSpanBy V1 R
  have hZW : Z≤W := hZV.trans hVW
  have hWR : W≤R := conjugateSpanBy_le_self (hp.2.1.trans (le_conjugateSpanBy U C))
  have hRH : R≤H := le_sup_left.trans le_sup_left
  have hHC : H≤C :=
    (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).1
  have hRZ : R≤centralizer (Z : Set G) := by
    intro r hr
    apply mem_centralizer_iff.mpr
    intro u hu
    have hzr : (z:G)∈centralizer ({r} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hHC (hRH hr))).symm
    exact mem_centralizer_singleton_iff.mp ((zpowers_le.mpr hzr) hu)
  have hdim : Module.finrank (ZMod 2) V=5 := by
    have hc := (Z.subgroupOf W).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv,hZcard,h64] at hc
    change Nat.card (W ⧸ Z.subgroupOf W)*2=64 at hc
    have hv := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=V)
    rw [Nat.card_zmod] at hv
    have heq : 2^(Module.finrank (ZMod 2) V)=2^5 := by
      change Nat.card (W ⧸ Z.subgroupOf W)=_ at hv
      omega
    exact Nat.pow_right_injective (by decide) heq
  let e := (Module.finBasisOfFinrankEq (ZMod 2) V hdim).equivFun
  let eG := (BinaryLinear.SmallParabolicLevi.linearGroupCongr e).trans
    (BinaryLinear.OuterCyclic.slEquivLinear 5).symm
  let π : R →* SL(5,ZMod 2) := eG.toMonoidHom.comp (φ.comp (inclusion hRH))
  have hπ : Function.Surjective π := by
    intro g
    have hg : eG.symm g ∈ (R.subgroupOf H).map φ := hRimage.symm ▸ hwhole.symm ▸ mem_top _
    obtain ⟨r,hr,hrg⟩ := hg
    refine ⟨⟨r,hr⟩,?_⟩
    change eG (φ r)=g
    rw [hrg,eG.apply_symm_apply]
  let c : BinaryConjugationSection R W Z ((specialLinearNatural 5).comp π) := {
    section_le := hWR
    kernel_le := hZW
    normalized := hRH.trans hHW
    coordinates := {
      toFun := fun w => Multiplicative.ofAdd (e (Additive.ofMul (q w)))
      map_one' := by simp
      map_mul' := fun u v => by simp only [map_mul]; exact congrArg Multiplicative.ofAdd (e.map_add _ _) }
    onto := by
      intro y
      obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) (e.symm y.toAdd).toMul
      refine ⟨w,?_⟩
      change e (Additive.ofMul (q w))=y.toAdd
      rw [hw]
      exact e.apply_symm_apply _
    kernel_eq := by
      ext w
      change e (Additive.ofMul (q w))=0 ↔ w∈Z.subgroupOf W
      rw [e.map_eq_zero_iff]
      exact QuotientGroup.eq_one_iff w
    equivariant := by
      intro r w
      change e (Additive.ofMul (q ⟨(r:G)*w*(r:G)⁻¹,_⟩))=
        BinaryLinear.OuterCyclic.slEquivLinear 5 (π r) (e (Additive.ofMul (q w)))
      have hφ := hformula (inclusion hRH r) w
      change φ (inclusion hRH r) (Additive.ofMul (q w))=Additive.ofMul (q ⟨(r:G)*w*(r:G)⁻¹,_⟩) at hφ
      rw [←hφ]
      change _=BinaryLinear.OuterCyclic.slEquivLinear 5
        ((BinaryLinear.OuterCyclic.slEquivLinear 5).symm
          (BinaryLinear.SmallParabolicLevi.linearGroupCongr e (φ (inclusion hRH r)))) _
      rw [MulEquiv.apply_symm_apply,BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply,e.symm_apply_apply] }
  have hxV : x.toMul∈(V1.subgroupOf W).map q := by
    have hh := hpoint ▸ Submodule.mem_span_singleton_self x
    exact hh
  obtain ⟨v,hv,hvx⟩ := hxV
  have hvZ : (v:G)∉Z := by
    intro hvZ
    have hqv : q v=1 := (QuotientGroup.eq_one_iff v).mpr hvZ
    apply hx
    apply Additive.toMul.injective
    exact hvx.symm.trans hqv
  let y := (c.coordinates v).toAdd
  have hy : y≠0 := by
    intro hy
    exact hvZ ((c.coordinates_eq_one_iff v).mp hy)
  let S := MulAction.stabilizer SL(5,ZMod 2) y
  have hres : primeToResidual 3 S=⊤ := BinaryLinear.PointStabilizerRank.five_point_primeToResidual y hy
  have him : ((centralizer (V1:Set G)).subgroupOf R).map π=S :=
    c.point_centralizer_image _ _ hπ V1 hZV (by
      have hc := relIndex_mul_card_of_le hZV
      rw [hZcard,hp.2.2.1] at hc
      omega) hZcard hRZ v hv hvZ hres
  have hC1C : centralizer (V1:Set G)≤C := centralizer_le (Set.singleton_subset_iff.mpr hp.1)
  have hC1 : IsSQTK KnownSimple.IsKnownSimple (centralizer (V1:Set G)) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hC1C)).mp
      ((h.simpleQTKE.involution_centralizer_sqtk hzorder).subgroup
        ((centralizer (V1:Set G)).subgroupOf C))
  exact point_eight_component R V1 π y hy him
    (hC1C.trans (le_normalizer_conjugateSpanBy U C)) hC1

end CFSG.Quasithin.Chapter12.Section07
