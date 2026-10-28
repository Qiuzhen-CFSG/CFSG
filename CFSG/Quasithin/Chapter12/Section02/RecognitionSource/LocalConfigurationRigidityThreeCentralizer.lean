module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeTransfer
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse


/-!
# The involution centralizer and residual-image route in dimension three

Write R=C_T(U), W=U∩V, and Y=O²(N_L(W)). All images below use the
literal map N_G(R) → N_G(R)/R. The preimage of the V-image is VR, and
[R,VR]=W. Thus an element normalizing that image preserves W; TI puts
it in N_G(V). Conversely N_G(V) centralizes its order-two quotient image.
This identifies the involution centralizer with the original N_G(L)-image
and proves that it normalizes the original Y-image.

The full natural action on the four-group W forces three to divide the
order of the Y-image. The P-image also retains its original prime order.
Combining the preceding Burnside transfer with an abelian odd core would
make the Y-image normal. Image normality alone suffices for the uniqueness
argument killing C_T(L): the fixed subgroup C_R(YR)=C_T(L) is then
normalized by the escaping pair. Conjugating the displacement bound
[V,YR]≤U through the actual pair gives the parabolic normalization needed
by the existing complement and Gaschütz constructions.

The final applications retain abelianness of the odd core and cubic order
as explicit, unresolved premises. Their proofs, the actual S₃×S₃ quotient,
and the higher-dimensional branch remain with qt-d-12213-local-rigidity.
No completion of the full source theorem is asserted here.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25--26, printed pp.805--806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

omit [Finite G] in
theorem radical_product_commutator (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ⁅radical T U, V ⊔ radical T U⁆ = U ⊓ V := by
  let R := radical T U
  let W := U ⊓ V
  let : IsElementaryAbelian 2 R := B.elementary
  have hRW : R ≤ centralizer (W : Set G) :=
    inf_le_right.trans (centralizer_le inf_le_left)
  have hVW : V ≤ normalizer (W : Set G) :=
    D.le_sylow.trans
      ((le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf)
  have hcomm := radical_chosen_commutator A C hTV
  apply le_antisymm ?_ (hcomm.ge.trans (commutator_mono le_rfl le_sup_left))
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (V ⊔ R) V R R W
    (sup_le hVW (hRW.trans (Subgroup.centralizer_le_normalizer _))) le_sup_left le_sup_right
    ((commutator_comm V R).trans hcomm).le
    ((commutator_self_eq_bot_iff.mpr inferInstance).trans_le bot_le)

omit [Finite G] in
theorem chosen_image_normalizer_lift
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (normalizer (image T U V : Set (NormalizerQuotient T U))).comap (quotient T U) ≤
      (normalizer ((U ⊓ V : Subgroup G) : Set G)).subgroupOf
        (normalizer (radical T U : Set G)) := by
  let N := normalizer (radical T U : Set G)
  have hVN : V ≤ N := D.le_sylow.trans (sylow_normalizes_radical C)
  have hSN : V ⊔ radical T U ≤ N := sup_le hVN (radical T U).le_normalizer
  intro g hg
  have hgn : g ∈ normalizer ((image T U V).comap (quotient T U) : Set N) :=
    le_normalizer_comap _ hg
  rw [image_comap _ hVN, ← subgroupOf_normalizer_eq hSN] at hgn
  change (g : G) ∈ normalizer ((V ⊔ radical T U : Subgroup G) : Set G) at hgn
  change (g : G) ∈ normalizer ((U ⊓ V : Subgroup G) : Set G)
  rw [mem_normalizer_iff_map_conj_eq, ← radical_product_commutator D A C B hTV,
    map_commutator, mem_normalizer_iff_map_conj_eq.mp g.property,
    mem_normalizer_iff_map_conj_eq.mp hgn]

/-- The full inverse image of the original involution centralizer is exactly
its actual module normalizer inside N_G(R). -/
theorem chosen_image_centralizer_comap
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    (centralizer (image T U V : Set (NormalizerQuotient T U))).comap (quotient T U) =
      (normalizer (V : Set G)).subgroupOf (normalizer (radical T U : Set G)) := by
  have hW : (U ⊓ V : Subgroup G) ≠ ⊥ := by
    intro he
    have hh := C.hyperplane
    rw [he,card_bot] at hh
    norm_num at hh
  apply le_antisymm
  · exact (comap_mono (Subgroup.centralizer_le_normalizer _)).trans
      ((chosen_image_normalizer_lift D A C B hTV).trans
        (subgroupOf_mono _ (hTI.normalizer_le_of_ne_bot hW inf_le_right)))
  · intro g hg
    apply normalizer_le_centralizer_of_card_two _ (chosen_image_card D A C)
    apply mem_normalizer_fintype
    rintro x ⟨v,hv,rfl⟩
    change quotient T U g * quotient T U v * (quotient T U g)⁻¹ ∈ image T U V
    rw [← map_inv,← map_mul,← map_mul]
    exact mem_map_of_mem (quotient T U) ((mem_normalizer_iff.mp hg v).mp hv)

/-- The actual centralizer in the radical quotient, with its original marking. -/
theorem chosen_image_centralizer
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    centralizer (image T U V : Set (NormalizerQuotient T U)) =
      image T U (normalizer (V : Set G)) := by
  change centralizer (image T U V : Set (NormalizerQuotient T U)) =
    ((normalizer (V : Set G)).subgroupOf (normalizer (radical T U : Set G))).map (quotient T U)
  rw [← chosen_image_centralizer_comap D A C B hTV hTI,
    map_comap_eq_self_of_surjective quotient_surjective]

/-- Centralizing the original involution image forces normalization of the
literal residual Y, before taking its image. -/
theorem chosen_centralizer_lift_normalizes_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    (centralizer (image T U V : Set (NormalizerQuotient T U))).comap (quotient T U) ≤
      (normalizer (rigidityHyperplaneResidual L U V : Set G)).subgroupOf
        (normalizer (radical T U : Set G)) := by
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  have hVL : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    D.normal_subgroup_normalizer_le h.toHypothesis1221
      (D.le_component.trans le_sup_left) D.ne_bot (sup_le D.normalizes hTV)
  intro g hg
  have hgV := (chosen_image_centralizer_comap D A C B hTV hTI).le hg
  have hgW := chosen_image_normalizer_lift D A C B hTV
    ((comap_mono (Subgroup.centralizer_le_normalizer _)) hg)
  have hgF : (g : G) ∈ normalizer (F : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hVL hgV,(normalizer _).le_normalizer hgW⟩
  exact normalizer_le_normalizer_characteristic_image F (pResidual 2 F) hgF

/-- The source residual image is normal in the actual involution centralizer. -/
theorem chosen_centralizer_normalizes_residual_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    centralizer (image T U V : Set (NormalizerQuotient T U)) ≤
      normalizer (image T U (rigidityHyperplaneResidual L U V) : Set (NormalizerQuotient T U)) := by
  let N := normalizer (radical T U : Set G)
  let Y := rigidityHyperplaneResidual L U V
  intro g hg
  obtain ⟨a,rfl⟩ := quotient_surjective (T := T) (U := U) g
  have ha := chosen_centralizer_lift_normalizes_residual h D A C B hTV hTI hg
  have han : a ∈ normalizer (Y.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq B.residual_normalizes]
    exact ha
  exact (Y.subgroupOf N).le_normalizer_map (quotient T U) (mem_map_of_mem _ han)

/-- The involution centralizer is the original component-normalizer image,
and it normalizes the original residual image. This source application has
no additional action or normalizer-classification premise. -/
theorem source_involution_centralizer_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    centralizer (image T U V : Set (NormalizerQuotient T U)) =
        image T U (normalizer (L : Set G)) ∧
      centralizer (image T U V : Set (NormalizerQuotient T U)) ≤
        normalizer (image T U (rigidityHyperplaneResidual L U V) : Set (NormalizerQuotient T U)) := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := ((structural G T L h).2.2 V D).1
  have hNV : normalizer (V : Set G) = normalizer (L : Set G) := by
    apply le_antisymm (D.normal_subgroup_normalizer_le h.toHypothesis1221
      (D.le_component.trans le_sup_left) D.ne_bot (sup_le D.normalizes hTV))
    rw [← RigidityResidual.component_core_of_centralizers D B]
    exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  exact ⟨(chosen_image_centralizer D A C B hTV hTI).trans (congrArg (image T U) hNV),
    chosen_centralizer_normalizes_residual_image h D A C B hTV hTI⟩

/-- The odd prime subgroup survives unchanged in the actual quotient. -/
theorem prime_image_card (C : CyclicLocalAnalysis T L V 3 H P U) :
    Nat.card (image T U P) = Nat.card P := by
  have hPN : P ≤ normalizer (radical T U : Set G) :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans (overgroup_normalizes_radical C)
  have hd : Disjoint (radical T U) P := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le (show radical T U ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr C.odd_order).pow_left n
  rw [image_card _ hPN, ← inf_relIndex_left, inf_comm P, hd.eq_bot, relIndex_bot_left]

/-- The natural action on the original four-group forces a cubic divisor
in the literal residual image, independently of the classification of N_G(R). -/
theorem three_dvd_residual_image_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    3 ∣ Nat.card (image T U (rigidityHyperplaneResidual L U V)) := by
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  let Y := rigidityHyperplaneResidual L U V
  let W := U ⊓ V
  let := D.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (show W ≤ V from inf_le_right)) (inclusion_injective _)
  have hAut : Nat.card (MulAut W) = 6 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow W 2 C.hyperplane]
    decide
  have hF : 3 ∣ Nat.card F := by
    have hd := card_dvd_of_surjective
      (W.normalizerMonoidHom.comp (inclusion (show F ≤ normalizer (W : Set G) from inf_le_right)))
        (RigidityResidual.hyperplane_full D A)
    rw [hAut] at hd
    exact (by decide : 3 ∣ 6).trans hd
  have hY : 3 ∣ Nat.card Y := by
    change 3 ∣ Nat.card ((pResidual 2 F).map F.subtype)
    rw [card_map_of_injective F.subtype_injective]
    rw [← (pResidual 2 F).card_mul_index] at hF
    apply (Nat.prime_three.dvd_mul.mp hF).resolve_right
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := F) 2).exists_card_eq
    change ¬ 3 ∣ Nat.card (F ⧸ pResidual 2 F)
    rw [hn]
    exact Nat.prime_three.coprime_iff_not_dvd.mp ((by decide : Nat.Coprime 3 2).pow_right n)
  rw [image_card _ B.residual_normalizes]
  have he := relIndex_mul_relIndex (⊥ : Subgroup G) (radical T U ⊓ Y) Y bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left] at he
  have hi : (radical T U ⊓ Y).relIndex Y = (radical T U).relIndex Y := by
    rw [inf_comm,inf_relIndex_left]
  rw [hi] at he
  rw [← he] at hY
  apply (Nat.prime_three.dvd_mul.mp hY).resolve_left
  obtain ⟨n,hn⟩ := (T.isPGroup'.to_le
    (show radical T U ⊓ Y ≤ (T : Subgroup G) from inf_le_left.trans inf_le_left)).exists_card_eq
  rw [hn]
  exact Nat.prime_three.coprime_iff_not_dvd.mp ((by decide : Nat.Coprime 3 2).pow_right n)

/-- The hyperplane residual acts nontrivially in N_G(R)/R. -/
theorem residual_image_ne_bot (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    image T U (rigidityHyperplaneResidual L U V) ≠ ⊥ := by
  intro he
  have hd := three_dvd_residual_image_card D A C B
  rw [he,card_bot] at hd
  norm_num at hd

omit [Finite G] in
theorem sylow_normalizes_residual (D : ChosenModule T L V)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) := by
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  have hTW : (T : Subgroup G) ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  exact ((le_inf D.sylow_normalizes_component (hTW.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image F (pResidual 2 F))

/-- Burnside transfer reduces residual image normality to an abelian odd core. -/
theorem residual_image_normal_of_abelian_oddCore
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (hab : IsMulCommutative (pPrimeCore 2 (NormalizerQuotient T U))) :
    (image T U (rigidityHyperplaneResidual L U V)).Normal := by
  let N := normalizer (radical T U : Set G)
  let Y := rigidityHyperplaneResidual L U V
  let O := pPrimeCore 2 (NormalizerQuotient T U)
  let := hab
  have hYO := residual_image_le_oddCore D A C B hTV hTI
  have hON : O ≤ normalizer (image T U Y : Set (NormalizerQuotient T U)) :=
    ((le_centralizer O).trans (centralizer_le hYO)).trans (Subgroup.centralizer_le_normalizer _)
  have hTN : (quotientSylow C : Subgroup (NormalizerQuotient T U)) ≤
      normalizer (image T U Y : Set (NormalizerQuotient T U)) := by
    change (image T U (T : Subgroup G)) ≤ _
    rintro g ⟨t,ht,rfl⟩
    have htn : t ∈ normalizer (Y.subgroupOf N : Set N) := by
      rw [← subgroupOf_normalizer_eq B.residual_normalizes]
      exact sylow_normalizes_residual D C hTV ht
    exact (Y.subgroupOf N).le_normalizer_map (quotient T U) (mem_map_of_mem _ htn)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top (quotientSylow C),
    pResidual_eq_pPrimeCore_of_hasNormalPComplement (normal_two_complement D A C B hTV hTI)]
  exact sup_le hON hTN

omit [Finite G] in
/-- Lifting residual image normality gives normality of the literal product YR. -/
theorem residual_product_normalized
    (B : LocalRigidityCentralizers T L V U P)
    (hn : (image T U (rigidityHyperplaneResidual L U V)).Normal) :
    normalizer (radical T U : Set G) ≤
      normalizer ((rigidityHyperplaneResidual L U V ⊔ radical T U : Subgroup G) : Set G) := by
  let := hn
  have hc := (image T U (rigidityHyperplaneResidual L U V)).normal_comap (quotient T U)
  rw [image_comap _ B.residual_normalizes] at hc
  exact (normal_subgroupOf_iff_le_normalizer
    (sup_le B.residual_normalizes (radical T U).le_normalizer)).mp hc

/-- Normality of Y modulo R suffices for the central-factor elimination. -/
theorem kernel_vanishing_of_residual_image_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hn : (image T U (rigidityHyperplaneResidual L U V)).Normal) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  let R := radical T U
  let N := normalizer (R : Set G)
  let Y := rigidityHyperplaneResidual L U V
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 R := B.elementary
  let := hn
  have hnorm : N ≤ normalizer ((Y ⊔ R : Subgroup G) : Set G) :=
    residual_product_normalized B hn
  have hfix : R ⊓ centralizer ((Y ⊔ R : Subgroup G) : Set G) = Z := by
    trans R ⊓ centralizer (Y : Set G)
    · apply le_antisymm (inf_le_inf_left R (centralizer_le (show Y ≤ Y ⊔ R from le_sup_left)))
      refine le_inf inf_le_left ?_
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp inf_le_right)
        ((le_centralizer R).trans (centralizer_le inf_le_left))
    · exact RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B
  have hNZ : N ≤ normalizer (Z : Set G) := by
    rw [← hfix]
    exact (le_inf le_rfl (hnorm.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  apply chosen_common_normal_subgroup_eq_bot h D C (inf_le_left.trans le_sup_right)
  · exact (sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp B.component_centralizer_central)).trans
        (Subgroup.centralizer_le_normalizer _)
  · exact (higher_pair_normalizes_sylow_centralizer D A C).trans hNZ

/-- Source application: the only additional hypothesis is the small linear
odd-core assertion; all centralizer and fixed-space inputs are discharged. -/
theorem source_rigidity_of_abelian_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (hab : IsMulCommutative (pPrimeCore 2 (NormalizerQuotient T U))) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧ centralizer (U : Set G) = U := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B
    (((structural G T L h).2.2 V D).1) hTI hab
  have hz := kernel_vanishing_of_residual_image_normal h D structural A C B hn
  exact ⟨higher_normalizer_eq_of_kernel_vanishing h D structural A C B hz,
    RigidityResidual.component_core_of_centralizers D B,
    (higher_selfCentralizing_of_kernel_vanishing h D structural A C B hz).2⟩

/-- Normality in the quotient also supplies the pair normalization needed by
the literal parabolic construction. -/
theorem parabolic_normalizes_pair_of_residual_image_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hn : (image T U (rigidityHyperplaneResidual L U V)).Normal) :
    L ⊓ normalizer (U : Set G) ≤ normalizer (cyclicPairJoin P U V : Set G) := by
  let R := radical T U
  let Y := rigidityHyperplaneResidual L U V
  let W := U ⊓ V
  let F := L ⊓ normalizer (W : Set G)
  have hTV := ((structural G T L h).2.2 V D).1
  have hYL : Y ≤ L := (map_subtype_le _).trans inf_le_left
  have hYW : Y ≤ normalizer (W : Set G) := (map_subtype_le _).trans inf_le_right
  have hRW : R ≤ normalizer (W : Set G) :=
    (inf_le_right.trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hVY : ⁅V,Y⁆ ≤ W := commutator_le_of_normalized_index_two V W Y
    inf_le_right (RigidityResidual.hyperplane_index A C) (hYL.trans D.normalizes) hYW
  have hVYR : ⁅V,Y ⊔ R⁆ ≤ U := by
    rw [commutator_comm]
    apply le_trans (commutator_sup_le_of_relative_normal (Y ⊔ R) Y R V W
      (sup_le hYW hRW) le_sup_left le_sup_right
      ((commutator_comm Y V).le.trans hVY)
      (radical_chosen_commutator A C hTV).le) inf_le_left
  have hPH : P ≤ H := by rw [C.overgroup]; exact le_sup_left
  have hPN : P ≤ normalizer ((Y ⊔ R : Subgroup G) : Set G) :=
    hPH.trans ((overgroup_normalizes_radical C).trans (residual_product_normalized B hn))
  obtain ⟨g,hg,_,hI,_⟩ := C.pair
  have hgY : (Y ⊔ R).map (MulAut.conj g).toMonoidHom = Y ⊔ R :=
    mem_normalizer_iff_map_conj_eq.mp (hPN hg)
  have hgU : U.map (MulAut.conj g).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (C.overgroup_normalizes_core (hPH hg))
  have hVg : ⁅V.map (MulAut.conj g).toMonoidHom,Y ⊔ R⁆ ≤ U := by
    have he := map_mono (f := (MulAut.conj g).toMonoidHom) hVYR
    rwa [map_commutator,hgY,hgU] at he
  have hIH : cyclicPairJoin P U V ≤ H := sup_le (sup_le hPH
    (C.core_le_sylow.trans C.sylow_le_overgroup)) (D.le_sylow.trans C.sylow_le_overgroup)
  have hIY : ⁅cyclicPairJoin P U V,Y⁆ ≤ U := by
    apply le_trans (commutator_mono le_rfl le_sup_left)
    rw [hI]
    exact commutator_sup_le_of_relative_normal (cyclicPairJoin P U V) _ _ (Y ⊔ R) U
      (hIH.trans C.overgroup_normalizes_core) le_sup_right
      (by rw [hI]; exact le_sup_right) hVYR hVg
  have hYI : Y ≤ normalizer (cyclicPairJoin P U V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hIY.trans (le_sup_right.trans le_sup_left))
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf D.sylow_normalizes_component (hTW.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hJF : L ⊓ normalizer (U : Set G) ≤ F :=
    le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans D.normalizes)).trans
      inf_normalizer_le_normalizer_inf)
  exact (hJF.trans (le_embedded_pResidual_sup_sylow_of_normalizes T F hTF)).trans
    (sup_le hYI (C.sylow_le_overgroup.trans C.pair_normal))

/-- The exact dimension-three rigidity and parabolic conclusion from the
remaining cubic and abelian-odd-core inputs. Their discharge remains with
qt-d-12213-local-rigidity. -/
theorem source_parabolic_of_abelian_oddCore_and_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (hab : IsMulCommutative (pPrimeCore 2 (NormalizerQuotient T U))) (hp : Nat.card P = 3) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧ ParabolicSplitting T L V U := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B
    (((structural G T L h).2.2 V D).1) hTI hab
  have hz := kernel_vanishing_of_residual_image_normal h D structural A C B hn
  exact ⟨higher_normalizer_eq_of_kernel_vanishing h D structural A C B hz,
    RigidityResidual.component_core_of_centralizers D B,
    RigidityParabolic.source_parabolic_of_cubic_pair_normalized h D structural A C hnone hz hp
      (parabolic_normalizes_pair_of_residual_image_normal h D structural A C B hn)⟩

/-- Actual application of the new quotient route to the existing Gaschütz
consumer, retaining all unresolved source premises explicitly. -/
theorem source_split_of_abelian_oddCore_and_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (hab : IsMulCommutative (pPrimeCore 2 (NormalizerQuotient T U))) (hp : Nat.card P = 3) :
    SplitLinearConfiguration L V 3 := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B
    (((structural G T L h).2.2 V D).1) hTI hab
  exact RigidityParabolic.source_split_of_cubic_pair_normalized h D structural A C hnone
    (kernel_vanishing_of_residual_image_normal h D structural A C B hn) (Or.inl rfl) hp
    (parabolic_normalizes_pair_of_residual_image_normal h D structural A C B hn)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
