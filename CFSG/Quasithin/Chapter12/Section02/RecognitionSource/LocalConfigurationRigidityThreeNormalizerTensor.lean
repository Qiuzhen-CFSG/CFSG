module
public import Theory.Representation.BinaryDoubledNaturalTensor
public import Theory.GroupTheory.SylowThreeNormalizerSection
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherTensorAxes
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeParabolicFactors
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeQuotient

/-!
# The marked dimension-three normalizer and original prime complement

The canonical subgroup K=C_{N_L(U)}(P) acts on W=U∩V through its full
binary automorphism group. This follows from N_L(U)=UVK: the factor UV
centralizes W, and N_L(U)=N_L(W) has the full hyperplane action. Since K
centralizes the original g∈P, the pair coordinates U=W×Wᵍ identify its
action with two identical natural planes. These are literal conjugation
coordinates, not an inference from the abstract quotient isomorphism.

The actual I=PUV action commutes with K modulo U. Its original order-three
P-image and order-two V-image fill the multiplicity centralizer. The two
actions therefore fill the tensor subgroup SL₂(2)×SL₂(2). The previously
proved quotient order 36 excludes a larger image and gives the marked
isomorphism on N_G(U)/U, as well as N_G(U)=YIT. Relative normality of I
and Frattini's argument then give the genuine complement N_G(U)∩N_G(P),
with the original P retained.

This closes the remaining tensor-action and full-normalizer complement
obligations in the dimension-three branch. The higher-dimensional component
sieve, exceptional-module recognition and final source assembly remain with
qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25--26, printed pp.805--806.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
open HigherRigidity Representation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G}

omit [Finite G] in
/-- The fixed actor preserves the original hyperplane. -/
theorem fixedActor_normalizes_hyperplane (D : ChosenModule T L V) :
    parabolicFixedActor L U P ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
  (le_inf (inf_le_left.trans inf_le_right)
    ((inf_le_left.trans inf_le_left).trans D.normalizes)).trans inf_normalizer_le_normalizer_inf

/-- The original conjugation action of the fixed actor on the hyperplane. -/
def fixedActorHyperplaneAction (D : ChosenModule T L V) :
    parabolicFixedActor L U P →* MulAut (U ⊓ V : Subgroup G) :=
  (U ⊓ V : Subgroup G).normalizerMonoidHom.comp (inclusion (fixedActor_normalizes_hyperplane D))

omit [Finite G] in
/-- Removing the trivial UV action from the parabolic leaves the full action. -/
theorem fixedActorHyperplaneAction_surjective
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (F : ParabolicFactorization L V U P)
    (hF : L ⊓ normalizer (U : Set G) = hyperplaneNormalizer L U V) :
    Function.Surjective (fixedActorHyperplaneAction D (U := U) (P := P)) := by
  let := C.elementary
  let := D.elementary
  let K := parabolicFixedActor L U P
  let J := L ⊓ normalizer (U : Set G)
  have hKW : K ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) := fixedActor_normalizes_hyperplane D
  have hfix : U ⊔ V ≤ centralizer ((U ⊓ V : Subgroup G) : Set G) := sup_le
    ((le_centralizer U).trans (centralizer_le inf_le_left))
    ((le_centralizer V).trans (centralizer_le inf_le_right))
  have hKn : K ≤ normalizer ((U ⊔ V : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans inf_le_right)
      ((inf_le_left.trans inf_le_left).trans D.normalizes)).trans (normalizer_inf_normalizer_le_normalizer_sup U V)
  intro a
  obtain ⟨l,hl⟩ := hyperplaneAction_surjective D A a
  have hlJ : (l : G) ∈ J := hF.ge l.property
  have hlprod : (l : G) ∈ ((U ⊔ V : Subgroup G) : Set G) * (K : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hKn,F.generate]
    exact hlJ
  obtain ⟨x,hx,k,hk,hxk⟩ := hlprod
  refine ⟨⟨k,hk⟩,?_⟩
  rw [←hl]
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  change k * (w : G) * k⁻¹ = (l : G) * (w : G) * (l : G)⁻¹
  rw [←hxk]
  have hc := hfix hx (k * (w : G) * k⁻¹)
    ((mem_normalizer_iff.mp (hKW hk) w).mp w.property)
  calc
    _ = x * (k * (w : G) * k⁻¹) * x⁻¹ := by rw [←hc,mul_inv_cancel_right]
    _ = _ := by group

/-- The original conjugate axes carry the identical fixed-actor action. -/
theorem fixedActor_pair_coordinates (D : ChosenModule T L V)
    (C : CyclicLocalAnalysis T L V 3 H P U) :
    ∃ e : ((U ⊓ V : Subgroup G) × (U ⊓ V : Subgroup G)) ≃* U,
      ∀ (k : parabolicFixedActor L U P) w,
        U.normalizerMonoidHom ⟨k,k.property.1.2⟩ (e w) =
          e (fixedActorHyperplaneAction D k w.1,fixedActorHyperplaneAction D k w.2) := by
  obtain ⟨g,e,hg,he⟩ := exists_pair_coordinates C
  refine ⟨e,fun k w => ?_⟩
  apply Subtype.ext
  change (k : G) * (e w : G) * (k : G)⁻¹ = _
  rw [he,he]
  change _ = ((k : G) * (w.1 : G) * (k : G)⁻¹) * (g : G) *
    ((k : G) * (w.2 : G) * (k : G)⁻¹) * (g : G)⁻¹
  have hc : Commute (g : G) (k : G) := k.property.2 g g.property
  calc
    _ = ((k : G) * (w.1 : G) * (k : G)⁻¹) * ((k : G) * (g : G)) *
      (w.2 : G) * ((k : G) * (g : G))⁻¹ := by group
    _ = ((k : G) * (w.1 : G) * (k : G)⁻¹) * ((g : G) * (k : G)) *
      (w.2 : G) * ((g : G) * (k : G))⁻¹ := by rw [hc.eq]
    _ = _ := by group

/-- The original source hypotheses give the full doubled natural marking. -/
theorem source_fixedActor_natural_double
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    letI := C.elementary
    ∃ q : parabolicFixedActor L U P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      Function.Surjective q ∧
      ∃ e : Additive U ≃ₗ[ZMod 2] Representation.BinaryDoubledNatural.Space 2,
        ∀ (k : parabolicFixedActor L U P) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom ⟨k,k.property.1.2⟩ u)) =
            Representation.BinaryDoubledNatural.representation 2 (q k) (e (Additive.ofMul u)) := by
  let := C.elementary
  let : IsElementaryAbelian 2 (U ⊓ V : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (show U ⊓ V ≤ U from inf_le_left)) (inclusion_injective _)
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := ((structural G T L h).2.2 V D).1
  let := source_oddCore_elementary h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B hTV hTI inferInstance
  have hz := kernel_vanishing_of_residual_image_normal h D structural A C B hn
  have hR := (higher_kernel_vanishing_consequences D B hz).2.2.2
  have hF : L ⊓ normalizer (U : Set G) = hyperplaneNormalizer L U V := by
    simpa only [radical,hR] using component_radical_normalizer D A C B hTV
  have F := (source_rigidity_factors h D structural A C hnone hTI).2.2
  obtain ⟨f,hf⟩ := fixedActor_pair_coordinates D C
  let c := hyperplaneCoordinates C
  let a := f.symm.toAdditive.trans (AddEquiv.prodAdditive _ _)
  let b : Additive U ≃ₗ[ZMod 2]
      (Additive (U ⊓ V : Subgroup G) × Additive (U ⊓ V : Subgroup G)) :=
    { a with map_smul' := ZMod.map_smul a }
  let e := (b.trans (c.prodCongr c)).trans (LinearEquiv.finTwoArrow (ZMod 2) (Fin 2 → ZMod 2)).symm
  let q := (hyperplaneAutEquiv C).toMonoidHom.comp (fixedActorHyperplaneAction D (P := P))
  refine ⟨q,(hyperplaneAutEquiv C).surjective.comp
    (fixedActorHyperplaneAction_surjective D A C F hF),e,?_⟩
  intro k u
  obtain ⟨w,rfl⟩ := f.surjective u
  rw [hf]
  have hm (w) : c (Additive.ofMul (fixedActorHyperplaneAction D k w)) =
      Representation.specialLinearNatural 2 (q k) (c (Additive.ofMul w)) := by
    change _ = (BinaryLinear.OuterCyclic.slEquivLinear 2
      (hyperplaneAutEquiv C (fixedActorHyperplaneAction D k))) _
    simp only [hyperplaneAutEquiv,MulEquiv.trans_apply,MulEquiv.apply_symm_apply,
      BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply]
    rw [c.symm_apply_apply]
    rfl
  have he (w) : e (Additive.ofMul (f w)) = ![c (Additive.ofMul w.1),c (Additive.ofMul w.2)] := by
    change ![c (Additive.ofMul (f.symm (f w)).1),c (Additive.ofMul (f.symm (f w)).2)] = _
    rw [f.symm_apply_apply]
  rw [he,he]
  funext i
  fin_cases i <;> exact hm _

omit [Finite G] in
/-- The literal pair and canonical fixed actor commute modulo U. -/
theorem fixedActor_pair_commutator (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U) :
    ⁅cyclicPairJoin P U V,parabolicFixedActor L U P⁆ ≤ U := by
  let K := parabolicFixedActor L U P
  have hVK : ⁅V,K⁆ ≤ U ⊓ V := commutator_le_of_normalized_index_two V (U ⊓ V) K
    inf_le_right (RigidityResidual.hyperplane_index A C)
    ((inf_le_left.trans inf_le_left).trans D.normalizes) (fixedActor_normalizes_hyperplane D)
  obtain ⟨g,hg,_,hI,_⟩ := C.pair
  have hKg : K.map (MulAut.conj g).toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.centralizer_le_normalizer _) (le_centralizer_iff.mp inf_le_right hg))
  have hPH : P ≤ H := by rw [C.overgroup]; exact le_sup_left
  have hUg : U.map (MulAut.conj g).toMonoidHom = U := mem_normalizer_iff_map_conj_eq.mp
    (C.overgroup_normalizes_core (hPH hg))
  have hVgK : ⁅V.map (MulAut.conj g).toMonoidHom,K⁆ ≤ U := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (hVK.trans inf_le_left)
    rwa [map_commutator,hKg,hUg] at hh
  have hIH : cyclicPairJoin P U V ≤ H := sup_le (sup_le hPH
    (C.core_le_sylow.trans C.sylow_le_overgroup)) (D.le_sylow.trans C.sylow_le_overgroup)
  rw [hI]
  exact commutator_sup_le_of_relative_normal (cyclicPairJoin P U V) _ _ K U
    (hIH.trans C.overgroup_normalizes_core) le_sup_right (by rw [hI]; exact le_sup_right)
    (hVK.trans inf_le_left) hVgK

private theorem centralizer_eq_of_pair_orders
    {X : Type*} [Group X] [Finite X]
    (φ : X →* BinaryDoubledNatural.Ambient 2) (J PP VV : Subgroup X)
    (hPJ : PP ≤ J) (hVJ : VV ≤ J)
    (hcentral : J.map φ ≤ centralizer (BinaryDoubledNatural.component 2 : Set (BinaryDoubledNatural.Ambient 2)))
    (hP : Nat.card (PP.map φ) = 3) (hV : Nat.card (VV.map φ) = 2) :
    J.map φ = centralizer (BinaryDoubledNatural.component 2 : Set (BinaryDoubledNatural.Ambient 2)) := by
  let : Finite (BinaryDoubledNatural.Ambient 2) := Finite.of_injective
    (fun a : BinaryDoubledNatural.Ambient 2 => fun v : BinaryDoubledNatural.Space 2 =>
      (a : Module.End (ZMod 2) (BinaryDoubledNatural.Space 2)) v)
    (fun _ _ he => Units.ext (LinearMap.ext (congrFun he)))
  apply eq_of_le_of_card_ge hcentral
  have hthree : Nat.card (PP.map φ) ∣ Nat.card (J.map φ) := card_dvd_of_le (map_mono hPJ)
  have htwo : Nat.card (VV.map φ) ∣ Nat.card (J.map φ) := card_dvd_of_le (map_mono hVJ)
  rw [hP] at hthree
  rw [hV] at htwo
  rw [BinaryDoubledNatural.card_centralizer (by decide : 2 ≤ 2)]
  exact Nat.le_of_dvd Nat.card_pos ((show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd htwo hthree)

/-- The two canonical commuting actions fill the literal tensor subgroup.
The quotient isomorphism retains evaluation on every original vector. -/
theorem source_tensor_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    normalizer (U : Set G) = parabolicFixedActor L U P ⊔ cyclicPairJoin P U V ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] Representation.BinaryDoubledNatural.Space 2,
      ∃ f : HigherRigidity.NormalizerQuotient U ≃*
          (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            Representation.BinaryDoubledNatural.tensorRepresentation 2
              (f (HigherRigidity.quotient U g)) (e (Additive.ofMul u)) := by
  let := C.elementary
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := ((structural G T L h).2.2 V D).1
  let := source_oddCore_elementary h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B hTV hTI inferInstance
  have hz := kernel_vanishing_of_residual_image_normal h D structural A C B hn
  have hs := higher_kernel_vanishing_consequences D B hz
  have hCU := (higher_selfCentralizing_of_kernel_vanishing h D structural A C B hz).2
  let K := parabolicFixedActor L U P
  let I := cyclicPairJoin P U V
  let N := normalizer (U : Set G)
  have hKN : K ≤ N := inf_le_left.trans inf_le_right
  have hIN : I ≤ N := by
    simpa only [hs.2.2.2] using higher_pair_normalizes_sylow_centralizer D A C
  have hPN : P ≤ N := (le_sup_left.trans le_sup_left).trans hIN
  have hVN : V ≤ N := le_sup_right.trans hIN
  obtain ⟨q,hq,e,he⟩ := source_fixedActor_natural_double h D structural A C hnone hTI
  let : Finite (BinaryDoubledNatural.Ambient 2) := Finite.of_injective
    (fun a : BinaryDoubledNatural.Ambient 2 => fun v : BinaryDoubledNatural.Space 2 =>
      (a : Module.End (ZMod 2) (BinaryDoubledNatural.Space 2)) v)
    (fun _ _ he => Units.ext (LinearMap.ext (congrFun he)))
  let ψ : MulAut U ≃* BinaryDoubledNatural.Ambient 2 :=
    (BinaryFixedLine.linearAutEquiv.trans
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr e)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BinaryDoubledNatural.Space 2)).symm
  let φ : N →* BinaryDoubledNatural.Ambient 2 := ψ.toMonoidHom.comp U.normalizerMonoidHom
  have hφ (g : N) (u : U) :
      (φ g : Module.End (ZMod 2) (BinaryDoubledNatural.Space 2)) (e (Additive.ofMul u)) =
        e (Additive.ofMul (U.normalizerMonoidHom g u)) := by
    change e (Additive.ofMul (U.normalizerMonoidHom g (e.symm (e (Additive.ofMul u))).toMul)) = _
    rw [e.symm_apply_apply]
    rfl
  have hker : φ.ker = U.subgroupOf N := by
    ext g
    change ψ (U.normalizerMonoidHom g) = 1 ↔ (g : G) ∈ U
    rw [←map_one ψ,ψ.injective.eq_iff]
    change g ∈ U.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker,hCU]
    rfl
  have hφK (k : K) : φ (inclusion hKN k) = (BinaryDoubledNatural.representation 2).asGroupHom (q k) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := e.surjective v
    exact (hφ _ u.toMul).trans (he k u.toMul)
  have hKimage : (K.subgroupOf N).map φ = BinaryDoubledNatural.component 2 := by
    apply le_antisymm
    · rintro b ⟨k,hk,rfl⟩
      exact ⟨q ⟨k,hk⟩,(hφK ⟨k,hk⟩).symm⟩
    · rintro b ⟨a,rfl⟩
      obtain ⟨k,rfl⟩ := hq a
      exact ⟨inclusion hKN k,k.property,hφK k⟩
  have hIcentral : (I.subgroupOf N).map φ ≤
      centralizer (BinaryDoubledNatural.component 2 : Set (BinaryDoubledNatural.Ambient 2)) := by
    rintro b ⟨i,hi,rfl⟩
    rw [mem_centralizer_iff,←hKimage]
    rintro a ⟨k,hk,rfl⟩
    have hmem : ⁅i,k⁆ ∈ φ.ker := by
      rw [hker]
      exact fixedActor_pair_commutator D A C (commutator_mem_commutator hi hk)
    have hh := MonoidHom.mem_ker.mp hmem
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
    exact hh.symm
  have hcard (J : Subgroup G) (hJN : J ≤ N) : Nat.card ((J.subgroupOf N).map φ) = U.relIndex J := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hJN]
  have hPcard : Nat.card ((P.subgroupOf N).map φ) = 3 := by
    rw [hcard P hPN,←inf_relIndex_left]
    have hd : Disjoint U P := disjoint_of_coprime_natCard (by
      rw [C.dimension]; exact C.odd_order.coprime_two_left.pow_left _)
    rw [hd.symm.eq_bot,relIndex_bot_left]
    exact source_prime_card_three h D structural A C hnone
  have hVcard : Nat.card ((V.subgroupOf N).map φ) = 2 := by
    rw [hcard V hVN,←inf_relIndex_left,inf_comm V U]
    exact RigidityResidual.hyperplane_index A C
  have hIimage : (I.subgroupOf N).map φ =
      centralizer (BinaryDoubledNatural.component 2 : Set (BinaryDoubledNatural.Ambient 2)) := by
    exact centralizer_eq_of_pair_orders φ (I.subgroupOf N) (P.subgroupOf N) (V.subgroupOf N)
      (subgroupOf_mono N (le_sup_left.trans le_sup_left)) (subgroupOf_mono N le_sup_right)
      hIcentral hPcard hVcard
  have hjoin : ((K ⊔ I).subgroupOf N).map φ = BinaryDoubledNatural.tensorSubgroup 2 := by
    rw [subgroupOf_sup hKN hIN,Subgroup.map_sup,hKimage,hIimage,
      ←BinaryDoubledNatural.tensorSubgroup_eq_sup (hn := by decide)]
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    obtain ⟨j⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr j.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  have htcard : Nat.card (BinaryDoubledNatural.tensorSubgroup 2) = 36 := by
    rw [Nat.card_congr (BinaryDoubledNatural.tensorEquiv 2).toEquiv,Nat.card_prod,hSL]
  have hrangecard : Nat.card φ.range = 36 := by
    let m := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
    obtain ⟨j⟩ := (source_normalizer_quotient_and_centralizers h D structural A C hnone hTI).2
    rw [←Nat.card_congr m.toEquiv,Nat.card_congr j.toEquiv,Nat.card_prod,
      Nat.card_perm,Nat.card_fin]
    rfl
  have hrange : φ.range = BinaryDoubledNatural.tensorSubgroup 2 := by
    symm
    apply eq_of_le_of_card_ge (hjoin ▸ map_le_range φ ((K ⊔ I).subgroupOf N))
    rw [hrangecard,htcard]
  have hφN : ∀ g : N, φ g ∈ BinaryDoubledNatural.tensorSubgroup 2 :=
    fun g => hrange ▸ (show φ g ∈ φ.range from ⟨g,rfl⟩)
  have hgen : N = K ⊔ I := by
    apply le_antisymm ?_ (sup_le hKN hIN)
    intro g hg
    obtain ⟨k,hk,hkg⟩ := mem_map.mp (hjoin.symm ▸ hφN ⟨g,hg⟩)
    have hdiff : k⁻¹ * (⟨g,hg⟩ : N) ∈ φ.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hkg,inv_mul_cancel]
    have hU : (k : G)⁻¹ * g ∈ U := by
      change k⁻¹ * (⟨g,hg⟩ : N) ∈ U.subgroupOf N
      rwa [←hker]
    have hh : (k : G) * ((k : G)⁻¹ * g) ∈ K ⊔ I := (K ⊔ I).mul_mem hk
      (mem_sup_right (mem_sup_left (mem_sup_right hU)))
    simpa only [mul_inv_cancel_left] using hh
  let fN := φ.codRestrict (BinaryDoubledNatural.tensorSubgroup 2) hφN
  have hsurj : Function.Surjective fN := by
    intro b
    have hb : (b : BinaryDoubledNatural.Ambient 2) ∈ φ.range := hrange.symm ▸ b.property
    obtain ⟨g,hgb⟩ := hb
    exact ⟨g,Subtype.ext hgb⟩
  have hkN : fN.ker = U.subgroupOf N := (MonoidHom.ker_codRestrict φ _ _).trans hker
  let f := ((QuotientGroup.quotientMulEquivOfEq hkN.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fN hsurj)).trans (BinaryDoubledNatural.tensorEquiv 2)
  refine ⟨hgen,e,f,?_⟩
  intro g u
  exact (hφ g u).symm.trans (BinaryDoubledNatural.tensorEquiv_action 2 (fN g) (e (Additive.ofMul u)))
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

/-- Both full-normalizer conclusions in the dimension-three source branch,
including the literal tensor marking and the original P-normalizer complement. -/
theorem source_three_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    normalizer (U : Set G) =
        rigidityHyperplaneResidual L U V ⊔ cyclicPairJoin P U V ⊔ (T : Subgroup G) ∧
      (U.subgroupOf (normalizer (U : Set G))).IsComplement'
        ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) ∧
      Nonempty ((normalizer (U : Set G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] Representation.BinaryDoubledNatural.Space 2,
      ∃ f : HigherRigidity.NormalizerQuotient U ≃*
          (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            Representation.BinaryDoubledNatural.tensorRepresentation 2
              (f (HigherRigidity.quotient U g)) (e (Additive.ofMul u)) := by
  obtain ⟨hgen,e,f,hact⟩ := source_tensor_normalizer h D structural A C hnone hTI
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := ((structural G T L h).2.2 V D).1
  let := source_oddCore_elementary h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B hTV hTI inferInstance
  have hz := kernel_vanishing_of_residual_image_normal h D structural A C B hn
  have hR := (higher_kernel_vanishing_consequences D B hz).2.2.2
  let Y := rigidityHyperplaneResidual L U V
  let I := cyclicPairJoin P U V
  let N := normalizer (U : Set G)
  let F := HigherRigidity.hyperplaneNormalizer L U V
  have hYN : Y ≤ N := by simpa only [hR] using B.residual_normalizes
  have hIN : I ≤ N := le_sup_right.trans hgen.ge
  have hNI : N ≤ normalizer (I : Set G) := by
    change normalizer (U : Set G) ≤ _
    rw [hgen]
    exact sup_le ((inf_le_left : parabolicFixedActor L U P ≤ L ⊓ normalizer (U : Set G)).trans
      (parabolic_normalizes_pair_of_residual_image_normal h D structural A C B hn)) I.le_normalizer
  have hNP : N ≤ normalizer ((U ⊔ P : Subgroup G) : Set G) := by
    rw [sup_comm U P,←RigidityParabolic.pair_residual D C]
    exact hNI.trans (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hcomp := full_normalizer_complement C hNP
  have hTW : (T : Subgroup G) ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf D.sylow_normalizes_component (hTW.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hJF : L ⊓ normalizer (U : Set G) ≤ F :=
    le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans D.normalizes)).trans
      inf_normalizer_le_normalizer_inf)
  refine ⟨?_,hcomp,?_,e,f,hact⟩
  · apply le_antisymm ?_ (sup_le (sup_le hYN hIN) C.sylow_normalizes_core)
    change normalizer (U : Set G) ≤ _
    rw [hgen]
    exact sup_le ((inf_le_left.trans hJF).trans
      ((le_embedded_pResidual_sup_sylow_of_normalizes T F hTF).trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right)))
      (le_sup_right.trans le_sup_left)
  · let k : ((normalizer (P : Set G)).subgroupOf N) ≃*
        (N ⊓ normalizer (P : Set G) : Subgroup G) := {
      toFun x := ⟨x,x.val.property,x.property⟩
      invFun x := ⟨⟨x,x.property.1⟩,x.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
    obtain ⟨s⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    exact ⟨((k.symm.trans hcomp.symm.QuotientMulEquiv.symm).trans f).trans (MulEquiv.prodCongr s s)⟩
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
