module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherTensor
public import Theory.Representation.BinaryDoubledNaturalNormalizer
public import Theory.GroupTheory.SylowThreeNormalizerSection

/-!
# The marked higher normalizer and its original prime normalizer complement

Assume the remaining source component step Y normal in N_G(C_T(U)). The
proved dimension and centralizer results give d=4, R=U and C_G(U)=U.
The conjugate-axis coordinates identify the literal Y-action with the doubled
natural SL₃(2) action. Its full binary normalizer is the tensor product of
SL₃(2) and SL₂(2). The original I=PUV commutes with Y on U, and its order-three
P-image and order-two V-image fill the six-element multiplicity centralizer.
Thus N_G(U)=YI, and the actual quotient isomorphism retains its conjugation
equation on every representative and vector.

The same calculation makes I, and hence O²(I)=PU, normal in N_G(U).
Frattini applied to P in PU gives N_G(U)=U N_{N_G(U)}(P); the original
fixed-free action C_U(P)=1 makes the factors disjoint. Consequently the
literal N_G(U) intersection N_G(P) is a complement to U and is isomorphic
to SL₃(2) × S₃. This also supplies the full-normalizer complement in 12.2.26,
separately from the existing parabolic complement and Gaschütz promotion.

The component-normality premise remains with qt-d-12213-local-rigidity.
These theorems do not assert unconditional 12.2.25--26 or settle the
remaining dimension-three tensor-action marking.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25--26, printed pp.805--806.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Representation
namespace TensorModel
abbrev Space := SL3DoubledNaturalOffenders.Space (ZMod 2)
abbrev Ambient := SL3DoubledNaturalOffenders.Ambient (ZMod 2)
abbrev Factors := SL3DoubledNaturalOffenders.SL (ZMod 2) ×
  SL3DoubledNaturalOffenders.MultiplicitySL (ZMod 2)
abbrev component := SL3DoubledNaturalOffenders.component (ZMod 2)
abbrev normalizer := SL3DoubledNaturalOffenders.normalizer (ZMod 2)
abbrev tensor := SL3DoubledNaturalOffenders.tensorRepresentation (ZMod 2)
end TensorModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G}

private theorem centralizer_eq_of_pair_orders
    {X : Type*} [Group X] [Finite X]
    (φ : X →* TensorModel.Ambient) (J PP VV : Subgroup X)
    (hPJ : PP ≤ J) (hVJ : VV ≤ J)
    (hcentral : J.map φ ≤ centralizer (TensorModel.component : Set TensorModel.Ambient))
    (hP : Nat.card (PP.map φ) = 3) (hV : Nat.card (VV.map φ) = 2) :
    J.map φ = centralizer (TensorModel.component : Set TensorModel.Ambient) := by
  let : Finite TensorModel.Ambient := Finite.of_injective
    (fun a : TensorModel.Ambient => fun v : TensorModel.Space =>
      (a : Module.End (ZMod 2) TensorModel.Space) v)
    (fun _ _ he => Units.ext (LinearMap.ext (congrFun he)))
  apply eq_of_le_of_card_ge hcentral
  have hthree : Nat.card (PP.map φ) ∣ Nat.card (J.map φ) := card_dvd_of_le (map_mono hPJ)
  have htwo : Nat.card (VV.map φ) ∣ Nat.card (J.map φ) := card_dvd_of_le (map_mono hVJ)
  rw [hP] at hthree
  rw [hV] at htwo
  have hsix : 6 ∣ Nat.card (J.map φ) :=
    (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd htwo hthree
  have he : TensorModel.component = BinaryDoubledNatural.component 3 := rfl
  rw [he,BinaryDoubledNatural.card_centralizer (by decide : 2 ≤ 3)]
  exact Nat.le_of_dvd Nat.card_pos hsix

theorem source_tensor_normalizer_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 4) (C : CyclicLocalAnalysis T L V 4 H P U)
    (hnone : NoEscape L V)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    normalizer (U : Set G) = rigidityHyperplaneResidual L U V ⊔ cyclicPairJoin P U V ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] TensorModel.Space,
      ∃ f : NormalizerQuotient U ≃* TensorModel.Factors,
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            TensorModel.tensor (f (quotient U g)) (e (Additive.ofMul u)) := by
  let := C.elementary
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  let Y := rigidityHyperplaneResidual L U V
  let I := cyclicPairJoin P U V
  let N := normalizer (U : Set G)
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B)
  have hs := higher_kernel_vanishing_consequences D B hz
  have hCU := (higher_selfCentralizing_of_kernel_vanishing h D structural A C B hz).2
  have hNY : N ≤ normalizer (Y : Set G) := by simpa only [hs.2.2.2] using hn
  have hYN : Y ≤ N := by simpa only [hs.2.2.2] using B.residual_normalizes
  have hIN : I ≤ N := by
    simpa only [hs.2.2.2] using higher_pair_normalizes_sylow_centralizer D A C
  have hPN : P ≤ N := (le_sup_left.trans le_sup_left).trans hIN
  have hVN : V ≤ N := le_sup_right.trans hIN
  have hPY : P ≤ normalizer (Y : Set G) := hPN.trans hNY
  have hUY : U ≤ Y := core_le_residual_of_pair_normalizes D A C (by decide) hPY
  obtain ⟨q,hq,e,he⟩ := exists_natural_double D A C (by decide) hYN hPY
  let ψ : MulAut U ≃* TensorModel.Ambient :=
    (BinaryFixedLine.linearAutEquiv.trans
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr e)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) TensorModel.Space).symm
  let φ : N →* TensorModel.Ambient := ψ.toMonoidHom.comp U.normalizerMonoidHom
  have hφ (g : N) (u : U) :
      (φ g : Module.End (ZMod 2) TensorModel.Space) (e (Additive.ofMul u)) =
        e (Additive.ofMul (U.normalizerMonoidHom g u)) := by
    change e (Additive.ofMul (U.normalizerMonoidHom g
      (e.symm (e (Additive.ofMul u))).toMul)) = _
    rw [e.symm_apply_apply]
    rfl
  have hker : φ.ker = U.subgroupOf N := by
    ext g
    change ψ (U.normalizerMonoidHom g) = 1 ↔ (g : G) ∈ U
    rw [← map_one ψ,ψ.injective.eq_iff]
    change g ∈ U.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker,hCU]
    rfl
  have hφY (y : Y) : φ (inclusion hYN y) =
      (SL3DoubledNaturalOffenders.representation (ZMod 2)).asGroupHom (q y) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := e.surjective v
    exact (hφ _ u.toMul).trans (he y u.toMul)
  have hYimage : (Y.subgroupOf N).map φ = TensorModel.component := by
    apply le_antisymm
    · rintro b ⟨y,hy,rfl⟩
      exact ⟨q ⟨y,hy⟩, (hφY ⟨y,hy⟩).symm⟩
    · rintro b ⟨a,rfl⟩
      obtain ⟨y,rfl⟩ := hq a
      exact ⟨inclusion hYN y,y.property,hφY y⟩
  have hφN : ∀ g : N, φ g ∈ TensorModel.normalizer := by
    intro g
    change φ g ∈ normalizer (TensorModel.component : Set TensorModel.Ambient)
    rw [← hYimage]
    apply (Y.subgroupOf N).le_normalizer_map φ
    apply mem_map_of_mem φ
    rw [←subgroupOf_normalizer_eq hYN]
    exact hNY g.property
  have hIcentral : (I.subgroupOf N).map φ ≤
      centralizer (TensorModel.component : Set TensorModel.Ambient) := by
    rintro b ⟨i,hi,rfl⟩
    rw [mem_centralizer_iff,←hYimage]
    rintro a ⟨y,hy,rfl⟩
    have hk : ⁅i,y⁆ ∈ φ.ker := by
      rw [hker]
      exact RigidityParabolic.residual_pair_commutator D A C hPY
        (commutator_mem_commutator hi hy)
    have hh := MonoidHom.mem_ker.mp hk
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
    exact hh.symm
  have hcard (K : Subgroup G) (hKN : K ≤ N) :
      Nat.card ((K.subgroupOf N).map φ) = U.relIndex K := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hKN]
  have hPcard : Nat.card ((P.subgroupOf N).map φ) = 3 := by
    rw [hcard P hPN,←inf_relIndex_left]
    have hd : Disjoint U P := disjoint_of_coprime_natCard (by
      rw [C.dimension]; exact C.odd_order.coprime_two_left.pow_left _)
    rw [hd.symm.eq_bot,relIndex_bot_left]
    exact cubic_of_residual_normal h D structural A C hnone (by decide) hn
  have hVcard : Nat.card ((V.subgroupOf N).map φ) = 2 := by
    rw [hcard V hVN,←inf_relIndex_left]
    rw [inf_comm V U]
    exact RigidityResidual.hyperplane_index A C
  have hIimage : (I.subgroupOf N).map φ =
      centralizer (TensorModel.component : Set TensorModel.Ambient) := by
    exact centralizer_eq_of_pair_orders φ (I.subgroupOf N) (P.subgroupOf N) (V.subgroupOf N)
      (subgroupOf_mono N (le_sup_left.trans le_sup_left))
      (subgroupOf_mono N le_sup_right) hIcentral hPcard hVcard
  have hjoin : ((Y ⊔ I).subgroupOf N).map φ = TensorModel.normalizer := by
    rw [subgroupOf_sup hYN hIN,Subgroup.map_sup,hYimage,hIimage,
      ←SL3DoubledNaturalOffenders.binary_normalizer_eq_sup]
  have hsurj : Function.Surjective (φ.codRestrict TensorModel.normalizer hφN) := by
    intro b
    have hb : (b : TensorModel.Ambient) ∈ ((Y ⊔ I).subgroupOf N).map φ :=
      hjoin.symm ▸ b.property
    obtain ⟨g,hg,hgb⟩ := mem_map.mp hb
    exact ⟨g,Subtype.ext hgb⟩
  have hgen : N = Y ⊔ I := by
    apply le_antisymm ?_ (sup_le hYN hIN)
    intro g hg
    obtain ⟨k,hk,hkg⟩ := mem_map.mp (hjoin.symm ▸ hφN ⟨g,hg⟩)
    have hdiff : k⁻¹ * (⟨g,hg⟩ : N) ∈ φ.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hkg,inv_mul_cancel]
    have hU : (k : G)⁻¹ * g ∈ U := by
      change k⁻¹ * (⟨g,hg⟩ : N) ∈ U.subgroupOf N
      rwa [←hker]
    have hh : (k : G) * ((k : G)⁻¹ * g) ∈ Y ⊔ I :=
      (Y ⊔ I).mul_mem hk (mem_sup_left (hUY hU))
    simpa only [mul_inv_cancel_left] using hh
  let fN := φ.codRestrict TensorModel.normalizer hφN
  have hkN : fN.ker = U.subgroupOf N := by
    exact (MonoidHom.ker_codRestrict φ _ _).trans hker
  let f := ((QuotientGroup.quotientMulEquivOfEq hkN.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fN hsurj)).trans
      SL3DoubledNaturalOffenders.binaryNormalizerEquiv
  refine ⟨hgen,e,f,?_⟩
  intro g u
  exact (hφ g u).symm.trans
    (SL3DoubledNaturalOffenders.binaryNormalizerEquiv_action (fN g) (e (Additive.ofMul u)))
/-- Frattini gives the source complement in the full normalizer, with the
original P retained. This uses only normality of PU and its fixed-free action. -/
private theorem full_normalizer_complement
    {d : ℕ} (C : CyclicLocalAnalysis T L V d H P U)
    (hNP : normalizer (U : Set G) ≤ normalizer ((U ⊔ P : Subgroup G) : Set G)) :
    (U.subgroupOf (normalizer (U : Set G))).IsComplement'
      ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) := by
  let := C.elementary
  let : Fact (Nat.card P).Prime := ⟨C.prime_order⟩
  let N := normalizer (U : Set G)
  let J := U ⊔ P
  have hPN : P ≤ N :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  have hJN : J ≤ N := sup_le U.le_normalizer hPN
  have hcop : (Nat.card U).Coprime (Nat.card P) := by
    rw [C.dimension]
    exact C.odd_order.coprime_two_left.pow_left _
  have hd : Disjoint U P := disjoint_of_coprime_natCard hcop
  have hp : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (by simp)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint U P hPN hd
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) P J bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,hc,mul_comm (Nat.card U)] at hi
  have he : (P.subgroupOf J).index = Nat.card U := Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  have hPi : IsPGroup (Nat.card P) (P.subgroupOf J) :=
    hp.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  let S : Sylow (Nat.card P) J := hPi.toSylow (by
    rw [he]; exact C.prime_order.coprime_iff_not_dvd.mp hcop.symm)
  have hS : (S : Subgroup J).map J.subtype = P := by
    rw [IsPGroup.toSylow_coe]
    exact map_subgroupOf_eq_of_le le_sup_right
  let J' := J.subgroupOf N
  let : J'.Normal := (normal_subgroupOf_iff_le_normalizer hJN).mpr hNP
  let e : J ≃* J' := (subgroupOfEquivOfLe hJN).symm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : (S' : Subgroup J').map J'.subtype = P.subgroupOf N := by
    apply map_injective N.subtype_injective
    change (((S : Subgroup J).map e.toMonoidHom).map J'.subtype).map N.subtype = _
    rw [map_map,map_map,map_subgroupOf_eq_of_le hPN]
    exact hS
  have hfr := S'.normalizer_sup_eq_top
  rw [hmap,←subgroupOf_normalizer_eq hPN] at hfr
  have hs : U.subgroupOf N ⊔ (normalizer (P : Set G)).subgroupOf N = ⊤ := by
    change (normalizer (P : Set G)).subgroupOf N ⊔ (U ⊔ P).subgroupOf N = ⊤ at hfr
    rw [subgroupOf_sup U.le_normalizer hPN,sup_left_comm,
      sup_eq_left.mpr (subgroupOf_mono N P.le_normalizer)] at hfr
    exact hfr
  have hd' : Disjoint (U.subgroupOf N) ((normalizer (P : Set G)).subgroupOf N) := by
    rw [disjoint_iff]
    change (U ⊓ normalizer (P : Set G)).subgroupOf N = ⊥
    rw [SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf U P hPN hd,C.fixed]
    exact bot_subgroupOf _
  apply isComplement'_of_disjoint_and_mul_eq_univ hd'
  rw [←coe_mul_of_right_le_normalizer_left _ _
    (by rw [(U.subgroupOf N).normalizer_eq_top]; exact le_top),hs]
  rfl

/-- The actual full-normalizer complement from original 12.2.26. The module
marking is supplied by the previous theorem, not inferred from its group type. -/
theorem source_normalizer_complement_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 4) (C : CyclicLocalAnalysis T L V 4 H P U)
    (hnone : NoEscape L V)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    (U.subgroupOf (normalizer (U : Set G))).IsComplement'
      ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) ∧
    Nonempty ((normalizer (U : Set G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
      TensorModel.Factors) := by
  obtain ⟨hgen,e,f,hact⟩ := source_tensor_normalizer_of_residual_normal h D structural A C hnone hn
  let Y := rigidityHyperplaneResidual L U V
  let I := cyclicPairJoin P U V
  let N := normalizer (U : Set G)
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B)
  have hR := (higher_kernel_vanishing_consequences D B hz).2.2.2
  have hNY : N ≤ normalizer (Y : Set G) := by simpa only [hR] using hn
  have hPN : P ≤ N := (le_sup_left.trans le_sup_left).trans (le_sup_right.trans hgen.ge)
  have hNI : N ≤ normalizer (I : Set G) := by
    change normalizer (U : Set G) ≤ normalizer (I : Set G)
    rw [hgen]
    apply sup_le ?_ I.le_normalizer
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (RigidityParabolic.residual_pair_commutator D A C (hPN.trans hNY)).trans
      (le_sup_right.trans le_sup_left)
  have hNP : N ≤ normalizer ((U ⊔ P : Subgroup G) : Set G) := by
    rw [sup_comm U P,←RigidityParabolic.pair_residual D C]
    exact hNI.trans (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hcomp := full_normalizer_complement C hNP
  refine ⟨hcomp,?_⟩
  let k : ((normalizer (P : Set G)).subgroupOf N) ≃*
      (N ⊓ normalizer (P : Set G) : Subgroup G) := {
    toFun x := ⟨x, x.val.property, x.property⟩
    invFun x := ⟨⟨x,x.property.1⟩,x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact ⟨(k.symm.trans hcomp.symm.QuotientMulEquiv.symm).trans f⟩

/-- Both source normalizer conclusions for every higher-dimensional input.
The dimension cutoff is discharged by the previous cubic-rank argument;
only the containing-component normality step remains with this owner. -/
theorem source_higher_normalizer_of_residual_normal
    {d : ℕ} (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    d = 4 ∧
      normalizer (U : Set G) =
        rigidityHyperplaneResidual L U V ⊔ cyclicPairJoin P U V ⊔ (T : Subgroup G) ∧
      (U.subgroupOf (normalizer (U : Set G))).IsComplement'
        ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) ∧
      Nonempty ((normalizer (U : Set G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
        (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3))) ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] TensorModel.Space,
      ∃ f : NormalizerQuotient U ≃* TensorModel.Factors,
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            TensorModel.tensor (f (quotient U g)) (e (Additive.ofMul u)) := by
  have hd4 := dimension_four_of_residual_normal h D structural A C hnone hd hn
  subst d
  obtain ⟨hgen,e,f,hact⟩ := source_tensor_normalizer_of_residual_normal h D structural A C hnone hn
  obtain ⟨hcomp,⟨k⟩⟩ := source_normalizer_complement_of_residual_normal h D structural A C hnone hn
  refine ⟨rfl,?_,hcomp,?_,e,f,hact⟩
  · rw [←hgen,sup_eq_left.mpr C.sylow_normalizes_core]
  · exact ⟨k.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
