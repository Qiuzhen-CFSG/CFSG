module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityParabolicFactors
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeReduction
public import Theory.SpecificGroups.SL3.BinaryPointStabilizer
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# TI fusion and Burnside transfer in dimension three

Put R=C_T(U), W=U∩V, and work in the literal quotient N_G(R)/R.
The natural action and the already established equality O₂(L)=V give
|L|=1344 and |T∩L|=64. The central factor cancels from the orders of T
and R, so the original Sylow image has order four; the V-image has order
two. These counts do not assume that the Sylow image is noncyclic.

The two centralizer splittings give C_T(W)=RV, and [R,V]=W. If a conjugate
of the V-image lies in the Sylow image, its lift Vᵍ lies in T. The
commutator [W,Vᵍ] lies in W∩Wᵍ. The TI condition therefore makes it
trivial unless g already normalizes V. It follows that the V-image is
strongly closed in the original Sylow image. Its normalizer fixes this
subgroup of index two, and Burnside transfer supplies a normal odd
complement. Both the actual P-image and the image of the hyperplane
two-residual lie in the resulting odd core.

The source applications discharge the shared centralizer calculation and
retain the original quotient map, subgroups, and earlier structural input.
The identification with S₃×S₃, cubic order, central-factor elimination,
and the higher-dimensional branch remain with qt-d-12213-local-rigidity.
This module proves the fusion and transfer portion of that argument.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25, printed pp.805--806, especially the dimension-three
Burnside-transfer argument on p.806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

private theorem component_sylow (D : ChosenModule T L V) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let N := normalizer (L : Set G)
  obtain ⟨S,hS⟩ := (T.subtype D.sylow_normalizes_component).exists_subgroupOf_eq_of_normal
    (L.subgroupOf N)
  let e := subgroupOfEquivOfLe L.le_normalizer
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup (L.subgroupOf N)).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha
  · intro hx
    exact ⟨⟨⟨x,L.le_normalizer x.property⟩,x.property⟩,hx,rfl⟩

omit [Finite G] in
theorem component_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (B : LocalRigidityCentralizers T L V U P) :
    Nat.card L = 1344 := by
  obtain ⟨e,f,hf⟩ := A.natural
  have hcore : Nat.card (pCore 2 L) = 8 := by
    rw [← card_map_of_injective L.subtype_injective]
    change Nat.card (L.pCoreIn 2) = 8
    rw [RigidityResidual.component_core_of_centralizers D B]
    exact RigidityKernel.chosen_card A
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),
    Nat.card_congr e.toEquiv, BinaryLinear.NaturalThreePoint.group_card, hcore]

theorem component_sylow_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (B : LocalRigidityCentralizers T L V U P) :
    Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 64 := by
  obtain ⟨S,hS⟩ := component_sylow D
  have hc := S.card_eq_multiplicity
  rw [component_card D A B] at hc
  have hm : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hS,subgroupOf_map_subtype,inf_comm]
  rw [← hm,card_map_of_injective L.subtype_injective]
  exact hc.trans (by decide +kernel)

/-- The original Sylow has order 64 times the still-possible central factor. -/
theorem sylow_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (B : LocalRigidityCentralizers T L V U P) :
    Nat.card T = 64 * Nat.card ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) := by
  conv_lhs => rw [B.sylow_split]
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    ((inf_le_right.trans (centralizer_le inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)) B.sylow_disjoint,component_sylow_card D A B]

omit [Finite G] in
/-- Cardinalities of literal subgroup images under N_G(R) → N_G(R)/R. -/
theorem image_card (K : Subgroup G) (hK : K ≤ normalizer (radical T U : Set G)) :
    Nat.card (image T U K) = (radical T U).relIndex K := by
  rw [image,← relIndex_ker]
  change (QuotientGroup.mk' ((radical T U).subgroupOf (normalizer (radical T U : Set G)))).ker.relIndex
    (K.subgroupOf (normalizer (radical T U : Set G))) = _
  rw [QuotientGroup.ker_mk',relIndex_subgroupOf hK]

/-- The quotient of the original Sylow has order four, before killing C_T(L). -/
theorem quotientSylow_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) : Nat.card (quotientSylow C) = 4 := by
  change Nat.card (image T U (T : Subgroup G)) = 4
  rw [image_card _ (sylow_normalizes_radical C)]
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hR : Nat.card (radical T U) = 16 * Nat.card Z := by
    rw [show radical T U = U ⊔ Z from B.centralizer_split,
      card_sup_eq_mul_of_normalizes_of_disjoint _ _
        (((le_sup_right.trans B.centralizer_split.symm.le).trans inf_le_right).trans
          (Subgroup.centralizer_le_normalizer _)) B.centralizer_disjoint]
    rw [C.dimension]
    rfl
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (radical T U) (T : Subgroup G)
    bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hR,sylow_card D A B] at hh
  have hp : 0 < Nat.card Z := Nat.card_pos
  change (radical T U).relIndex (T : Subgroup G) = 4
  nlinarith

omit [Finite G] in
/-- The image of V is the original subgroup of order two in the quotient Sylow. -/
theorem chosen_image_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U) :
    Nat.card (image T U V) = 2 := by
  rw [image_card _ (D.le_sylow.trans (sylow_normalizes_radical C))]
  have hi : radical T U ⊓ V = U ⊓ V := by
    rw [radical,inf_assoc,inf_comm (centralizer _) V,
      RigidityParabolic.chosen_centralizer_core A C,
      inf_eq_right.mpr (inf_le_right.trans D.le_sylow)]
  rw [← inf_relIndex_left,inf_comm V,hi]
  exact RigidityResidual.hyperplane_index A C

omit [Finite G] in
/-- The hyperplane centralizer is exactly the full preimage of the involution image. -/
theorem hyperplane_centralizer_eq_radical_sup
    (D : ChosenModule T L V) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) = radical T U ⊔ V := by
  let := D.elementary
  let := C.elementary
  have hUR : U ≤ radical T U := le_inf C.core_le_sylow (le_centralizer U)
  apply le_antisymm
  · rw [B.hyperplane_centralizer]
    apply sup_le (sup_le (hUR.trans le_sup_left) le_sup_right)
    exact (le_inf inf_le_left (inf_le_right.trans (centralizer_le
      (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))).trans le_sup_left
  · exact sup_le (inf_le_inf_left _ (centralizer_le inf_le_left))
      (le_inf D.le_sylow ((le_centralizer V).trans (centralizer_le inf_le_right)))

omit [Finite G] in
/-- Commuting the radical with the original V recovers precisely its hyperplane. -/
theorem radical_chosen_commutator
    (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ⁅radical T U,V⁆ = U ⊓ V := by
  let := C.elementary
  have hUR : U ≤ radical T U := le_inf C.core_le_sylow (le_centralizer U)
  have hRW : radical T U ≤ centralizer ((U ⊓ V : Subgroup G) : Set G) :=
    inf_le_right.trans (centralizer_le inf_le_left)
  apply le_antisymm
  · rw [commutator_comm]
    exact commutator_le_of_normalized_index_two V (U ⊓ V) (radical T U)
      inf_le_right (RigidityResidual.hyperplane_index A C) (inf_le_left.trans hTV)
      (hRW.trans (Subgroup.centralizer_le_normalizer _))
  · rw [← C.transvections]
    exact commutator_mono hUR le_rfl

omit [Finite G] in
private theorem conjugate_chosen_le_radical_sup
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (g : G) (hg : g ∈ normalizer (radical T U : Set G))
    (hVgT : V.map (MulAut.conj g).toMonoidHom ≤ T) :
    V.map (MulAut.conj g).toMonoidHom ≤ radical T U ⊔ V := by
  let W := U ⊓ V
  let Vg := V.map (MulAut.conj g).toMonoidHom
  by_cases hgn : g ∈ normalizer (V : Set G)
  · have he : Vg = V := mem_normalizer_iff_map_conj_eq.mp hgn
    exact he.le.trans le_sup_right
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hXW : ⁅W,Vg⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (hVgT.trans hTW)
  have hRg : (radical T U).map (MulAut.conj g).toMonoidHom = radical T U :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hcomm := congrArg (map (MulAut.conj g).toMonoidHom) (radical_chosen_commutator A C hTV)
  rw [map_commutator,hRg] at hcomm
  have hWR : W ≤ radical T U := by
    let := C.elementary
    exact le_inf (inf_le_right.trans D.le_sylow) (inf_le_left.trans (le_centralizer U))
  have hXVg : ⁅W,Vg⁆ ≤ Vg :=
    ((commutator_mono hWR le_rfl).trans hcomm.le).trans (map_mono inf_le_right)
  have hz : ⁅W,Vg⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨v,hv,he⟩ := hXVg hx
    exact hTI g hgn ⟨(hXW hx).2,⟨v,hv,he⟩⟩
  rw [← hyperplane_centralizer_eq_radical_sup D C B]
  exact le_inf hVgT (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hz))

omit [Finite G] in
/-- Pulling back an image adds precisely the original radical. -/
theorem image_comap (K : Subgroup G) (hK : K ≤ normalizer (radical T U : Set G)) :
    (image T U K).comap (quotient T U) =
      (K ⊔ radical T U).subgroupOf (normalizer (radical T U : Set G)) := by
  rw [image,comap_map_eq]
  change K.subgroupOf _ ⊔ (QuotientGroup.mk' ((radical T U).subgroupOf
    (normalizer (radical T U : Set G)))).ker = _
  rw [QuotientGroup.ker_mk',subgroupOf_sup hK (radical T U).le_normalizer]

/-- A conjugate of the involution subgroup inside the original Sylow image equals it. -/
theorem chosen_image_fusion
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (g : NormalizerQuotient T U)
    (hg : (image T U V).map (MulAut.conj g).toMonoidHom ≤ quotientSylow C) :
    (image T U V).map (MulAut.conj g).toMonoidHom = image T U V := by
  obtain ⟨a,rfl⟩ := quotient_surjective (T := T) (U := U) g
  have hTN := sylow_normalizes_radical C
  have hVN := D.le_sylow.trans hTN
  have hVgT : V.map (MulAut.conj (a : G)).toMonoidHom ≤ T := by
    rintro x ⟨v,hv,rfl⟩
    let v' : normalizer (radical T U : Set G) := ⟨v,hVN hv⟩
    have hm : quotient T U (a * v' * a⁻¹) ∈ image T U (T : Subgroup G) := by
      have hh := hg (mem_map_of_mem (MulAut.conj (quotient T U a)).toMonoidHom
        (show quotient T U v' ∈ image T U V from mem_map_of_mem _ hv))
      change quotient T U a * quotient T U v' * (quotient T U a)⁻¹ ∈ image T U (T : Subgroup G) at hh
      simpa only [map_mul,map_inv] using hh
    change a * v' * a⁻¹ ∈ (image T U (T : Subgroup G)).comap (quotient T U) at hm
    rw [image_comap _ hTN,sup_eq_left.mpr (show radical T U ≤ (T : Subgroup G) from inf_le_left)] at hm
    exact hm
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj _).injective])
  rintro x ⟨y,⟨v,hv,rfl⟩,rfl⟩
  change quotient T U a * quotient T U v * (quotient T U a)⁻¹ ∈ image T U V
  rw [← map_inv,← map_mul,← map_mul]
  change a * v * a⁻¹ ∈ (image T U V).comap (quotient T U)
  rw [image_comap _ hVN]
  change (a : G) * (v : G) * (a : G)⁻¹ ∈ V ⊔ radical T U
  rw [sup_comm]
  exact conjugate_chosen_le_radical_sup D A C B hTV hTI a a.property hVgT
    (mem_map_of_mem (MulAut.conj (a : G)).toMonoidHom hv)

/-- The involution in the V-image has no fusion to its complement in the Sylow image. -/
theorem chosen_involution_fusion
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (g x : NormalizerQuotient T U) (hx : x ∈ image T U V)
    (hconj : g * x * g⁻¹ ∈ (quotientSylow C : Subgroup (NormalizerQuotient T U))) :
    g * x * g⁻¹ ∈ image T U V := by
  by_cases hx1 : x = 1
  · simp [hx1]
  have hS : (image T U V).map (MulAut.conj g).toMonoidHom ≤ quotientSylow C := by
    obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : image T U V)).mp (chosen_image_card D A C)
    rintro y ⟨v,hv,rfl⟩
    by_cases hv1 : v = 1
    · simp [hv1]
    have he : (⟨v,hv⟩ : image T U V) = ⟨x,hx⟩ :=
      (hz _ (fun he => hv1 (congrArg Subtype.val he))).trans
        (hz _ (fun he => hx1 (congrArg Subtype.val he))).symm
    have hval : v = x := congrArg Subtype.val he
    change g * v * g⁻¹ ∈ (quotientSylow C : Subgroup (NormalizerQuotient T U))
    rw [hval]
    exact hconj
  rw [← chosen_image_fusion D A C B hTV hTI g hS]
  exact mem_map_of_mem (MulAut.conj g).toMonoidHom hx

/-- TI forces the Sylow normalizer to fix the original involution image. -/
theorem quotientSylow_normalizer_centralizes_chosen
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    normalizer (quotientSylow C : Set (NormalizerQuotient T U)) ≤
      centralizer (image T U V : Set (NormalizerQuotient T U)) := by
  apply le_trans ?_ (normalizer_le_centralizer_of_card_two _ (chosen_image_card D A C))
  intro n hn
  apply mem_normalizer_fintype
  intro x hx
  apply chosen_involution_fusion D A C B hTV hTI n x hx
  exact (mem_normalizer_iff.mp hn x).mp (map_mono (subgroupOf_mono _ D.le_sylow) hx)

/-- Burnside transfer for the literal radical quotient in dimension three. -/
theorem normal_two_complement
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    HasNormalPComplement 2 (NormalizerQuotient T U) := by
  let S := quotientSylow C
  let E := image T U V
  have hES : E ≤ (S : Subgroup (NormalizerQuotient T U)) :=
    map_mono (subgroupOf_mono _ D.le_sylow)
  let : IsMulCommutative S := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 2) (by simpa using quotientSylow_card D A C B)
  let F := E.subgroupOf S
  have hF : Nat.card F = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv).trans (chosen_image_card D A C)
  have hidx : F.index ≤ 2 := by
    have hh := F.card_mul_index
    rw [hF,quotientSylow_card D A C B] at hh
    omega
  apply S.hasNormalTwoComplement_of_fixed_index_le_two F hidx
  intro n a ha
  apply Subtype.ext
  change (n : NormalizerQuotient T U) * (a : NormalizerQuotient T U) *
    (n : NormalizerQuotient T U)⁻¹ = a
  exact mul_inv_eq_iff_eq_mul.mpr
    ((quotientSylow_normalizer_centralizes_chosen D A C B hTV hTI n.property) a ha).symm

/-- Original-source application with the common centralizers discharged. -/
theorem source_normal_two_complement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    HasNormalPComplement 2 (NormalizerQuotient T U) :=
  normal_two_complement D A C (RigidityKernel.source_centralizers h D structural A C hnone)
    (((structural G T L h).2.2 V D).1) hTI

/-- The actual odd prime image lies in the normal odd complement obtained by transfer. -/
theorem prime_image_le_oddCore
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    image T U P ≤ pPrimeCore 2 (NormalizerQuotient T U) := by
  obtain ⟨N,hN,hcop,hquot⟩ := normal_two_complement D A C B hTV hTI
  let := hN
  have hodd : Odd (Nat.card (image T U P)) := C.odd_order.of_dvd_nat
    ((card_map_dvd _ _).trans (card_comap_dvd_of_injective P
      (normalizer (radical T U : Set G)).subtype
      (normalizer (radical T U : Set G)).subtype_injective))
  intro x hx
  exact mem_pPrimeCore_of_normal_complement N hcop hquot x
    ((Nat.coprime_two_left.mpr hodd).of_dvd_right ((image T U P).orderOf_dvd_natCard hx))

/-- The literal hyperplane residual image also lies in that same odd core. -/
theorem residual_image_le_oddCore
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    image T U (rigidityHyperplaneResidual L U V) ≤ pPrimeCore 2 (NormalizerQuotient T U) := by
  rw [← pResidual_eq_pPrimeCore_of_hasNormalPComplement (normal_two_complement D A C B hTV hTI)]
  let Y := rigidityHyperplaneResidual L U V
  have hp : IsPPerfect 2 Y := isPPerfect_embedded_pResidual 2 _
  let e := subgroupOfEquivOfLe B.residual_normalizes
  have hs : IsPPerfect 2 (Y.subgroupOf (normalizer (radical T U : Set G))) :=
    hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  exact le_pResidual_of_isPPerfect _ (hs.of_surjective
    ((quotient T U).subgroupMap _) ((quotient T U).subgroupMap_surjective _))

/-- Transfer supplies a single normal odd core containing both source odd actors. -/
theorem source_odd_core_contains_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    pResidual 2 (NormalizerQuotient T U) = pPrimeCore 2 (NormalizerQuotient T U) ∧
      image T U P ⊔ image T U (rigidityHyperplaneResidual L U V) ≤
        pPrimeCore 2 (NormalizerQuotient T U) := by
  have B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := (((structural G T L h).2.2 V D).1)
  exact ⟨pResidual_eq_pPrimeCore_of_hasNormalPComplement (normal_two_complement D A C B hTV hTI),
    sup_le (prime_image_le_oddCore D A C B hTV hTI) (residual_image_le_oddCore D A C B hTV hTI)⟩

/-- The source fusion conclusion, with all shared centralizer premises discharged. -/
theorem source_chosen_involution_fusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (g x : NormalizerQuotient T U) (hx : x ∈ image T U V)
    (hconj : g * x * g⁻¹ ∈ (quotientSylow C : Subgroup (NormalizerQuotient T U))) :
    g * x * g⁻¹ ∈ image T U V :=
  chosen_involution_fusion D A C (RigidityKernel.source_centralizers h D structural A C hnone)
    (((structural G T L h).2.2 V D).1) hTI g x hx hconj

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
