module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeOddCore
public import Theory.GroupAction.SixteenOddComplements.Nine

/-!
# The actual dimension-three normalizer quotient

The original V-image centralizes the residual Y-image, while its chosen
involution inverts the P-image. Since both odd images have order three,
their intersection is trivial. They lie in the elementary odd core,
whose order divides nine; hence that core has order exactly nine.

Residual-image normality kills the common Sylow central factors and
identifies R=C_T(U) with U. Burnside transfer supplies a four-group
complement to the normal nine. The faithful action on the literal U,
followed by the checked normal-nine/four-group recognition, constructs
an actual isomorphism N_G(U)/U ≃ S₃ × S₃. The equality R=U transports
the original relative quotient, rather than replacing it by a group tag.

The source application combines this with the original cubic prime and
centralizer assertions, discharging the dimension-three transfer contract.
Higher-dimensional source assembly remains with qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25, printed p.806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

theorem prime_disjoint_residual_image
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    Disjoint (image T U P) (image T U (rigidityHyperplaneResidual L U V)) := by
  let N := normalizer (radical T U : Set G)
  let q := quotient T U
  have hYV : image T U (rigidityHyperplaneResidual L U V) ≤
      centralizer (image T U V : Set (NormalizerQuotient T U)) := by
    rw [chosen_image_centralizer D A C B hTV hTI]
    apply map_mono
    apply subgroupOf_mono
    exact (map_subtype_le _).trans (inf_le_left.trans D.normalizes)
  apply disjoint_def.mpr
  intro x hxP hxY
  obtain ⟨p,hp,rfl⟩ := hxP
  obtain ⟨v,hv,_,hvP⟩ := C.inverted
  let vN : N := ⟨v,sylow_normalizes_radical C (D.le_sylow hv)⟩
  have hvq : q vN ∈ image T U V := ⟨vN,hv,rfl⟩
  have hc : q vN * q p = q p * q vN := hYV hxY (q vN) hvq
  have hi : q vN * q p * (q vN)⁻¹ = (q p)⁻¹ := by
    rw [← map_inv,← map_mul,← map_mul,← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact hvP p hp
  have hinv : q p = (q p)⁻¹ := by
    calc
      q p = q vN * q p * (q vN)⁻¹ := by rw [hc,mul_inv_cancel_right]
      _ = (q p)⁻¹ := hi
  have h2 : q p ^ 2 = 1 := by
    calc
      q p ^ 2 = q p * q p := pow_two _
      _ = q p * (q p)⁻¹ := congrArg (fun a => q p * a) hinv
      _ = 1 := mul_inv_cancel _
  have h3 : q p ^ 3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have hh := (image T U P).orderOf_dvd_natCard (show q p ∈ image T U P from ⟨p,hp,rfl⟩)
    rwa [prime_image_card C,prime_card_three D A C B] at hh
  calc
    q p = q p ^ 3 * (q p ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3,h2]; simp

theorem source_oddCore_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    Nat.card (pPrimeCore 2 (NormalizerQuotient T U)) = 9 := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := ((structural G T L h).2.2 V D).1
  let R := radical T U
  let O := pPrimeCore 2 (NormalizerQuotient T U)
  let PP := image T U P
  let YY := image T U (rigidityHyperplaneResidual L U V)
  let : IsElementaryAbelian 2 R := B.elementary
  let : IsElementaryAbelian 2 (quotientSylow C) := quotientSylow_elementary D A C B
  let : IsElementaryAbelian 3 O := source_oddCore_elementary h D structural A C hnone
  have he := radical_selfCentralizing h C B
  have hd : Nat.card O ∣ 9 :=
    Theory.GroupAction.odd_card_dvd_nine_of_card_sixteen_or_thirtytwo
      (HigherRigidity.action R he.symm.le) (HigherRigidity.action_injective R he)
      (radical_card C B) (quotientSylow C) O (quotientSylow_card D A C B)
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (O.normalizer_eq_top ▸ le_top)
  have hPO : PP ≤ O := prime_image_le_oddCore D A C B hTV hTI
  have hYO : YY ≤ O := residual_image_le_oddCore D A C B hTV hTI
  have hnorm : YY ≤ normalizer (PP : Set (NormalizerQuotient T U)) :=
    ((hYO.trans (le_centralizer O)).trans (centralizer_le hPO)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hprod : Nat.card (PP ⊔ YY : Subgroup (NormalizerQuotient T U)) = 9 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint PP YY hnorm
      (prime_disjoint_residual_image D A C B hTV hTI),
      show Nat.card PP = 3 from (prime_image_card C).trans (prime_card_three D A C B),
      show Nat.card YY = 3 from residual_image_card D A C B hTV hTI]
  exact Nat.dvd_antisymm hd (hprod ▸ card_dvd_of_le (sup_le hPO hYO))

/-- The common central factors agree and the literal N_G(U)/U is the
actual product of the two degree-three symmetric groups. -/
theorem source_normalizer_quotient_and_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) =
        (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) ∧
      Nonempty (HigherRigidity.NormalizerQuotient U ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := ((structural G T L h).2.2 V D).1
  let R := radical T U
  let O := pPrimeCore 2 (NormalizerQuotient T U)
  let S : Subgroup (NormalizerQuotient T U) := quotientSylow C
  let : IsElementaryAbelian 2 R := B.elementary
  let : IsElementaryAbelian 2 S := quotientSylow_elementary D A C B
  let : IsElementaryAbelian 3 O := source_oddCore_elementary h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B hTV hTI inferInstance
  have hZ := kernel_vanishing_of_residual_image_normal h D structural A C B hn
  have hR : R = U := by
    change (T : Subgroup G) ⊓ centralizer (U : Set G) = U
    rw [B.centralizer_split,hZ,sup_bot_eq]
  have hZI : (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    apply mem_bot.mpr
    apply disjoint_def.mp C.core_disjoint_sylow_pair_centralizer ?_ hz
    rw [← hR]
    exact ⟨hz.1,centralizer_le (show U ≤ cyclicPairJoin P U V from
      le_sup_right.trans le_sup_left) hz.2⟩
  refine ⟨hZ.trans hZI.symm,?_⟩
  have hRcard : Nat.card R = 16 := by rw [hR]; simpa using C.dimension
  have hO : Nat.card O = 9 := source_oddCore_card h D structural A C hnone hTI
  have hS : Nat.card S = 4 := quotientSylow_card D A C B
  have hsup : O ⊔ S = ⊤ := by
    rw [show O = pResidual 2 (NormalizerQuotient T U) from
      (pResidual_eq_pPrimeCore_of_hasNormalPComplement
        (normal_two_complement D A C B hTV hTI)).symm]
    exact pResidual_sup_sylow_eq_top (quotientSylow C)
  have hdis : Disjoint O S := disjoint_of_coprime_natCard (by rw [hO,hS]; decide)
  have hQ : Nat.card (NormalizerQuotient T U) = 36 := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint O S
      (O.normalizer_eq_top ▸ le_top) hdis
    rw [hsup,card_top,hO,hS] at hh
    exact hh
  have he := radical_selfCentralizing h C B
  let f := HigherRigidity.action R he.symm.le
  let F := f.range
  let e : NormalizerQuotient T U ≃* F :=
    MonoidHom.ofInjective (HigherRigidity.action_injective R he)
  let J := O.map e.toMonoidHom
  let K := S.map e.toMonoidHom
  let : J.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.map e.toMonoidHom
  have hJ : Nat.card J = 9 := (card_map_of_injective e.injective).trans hO
  have hK : Nat.card K = 4 := (card_map_of_injective e.injective).trans hS
  have hF : Nat.card F = 36 := (Nat.card_congr e.toEquiv).symm.trans hQ
  have hcomp : J.IsComplement' K := isComplement'_of_coprime
    (by rw [hJ,hK,hF]) (by rw [hJ,hK]; decide)
  obtain ⟨m⟩ := SixteenOddComplements.equiv_of_normal_nine_four hRcard F J hJ K hK hcomp
  have hh : Nonempty (HigherRigidity.NormalizerQuotient R ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := ⟨e.trans m⟩
  rwa [hR] at hh

/-- The complete transferred dimension-three contract for the original data. -/
theorem source_transfer_conclusions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    Nat.card P = 3 ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) =
        (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) ∧
      Nonempty (HigherRigidity.NormalizerQuotient U ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
  ⟨source_prime_card_three h D structural A C hnone,
    source_normalizer_quotient_and_centralizers h D structural A C hnone hTI⟩

/-- The involution centralizer is the literal original component image. -/
theorem source_involution_centralizer_eq_component_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    centralizer (image T U V : Set (NormalizerQuotient T U)) = image T U L := by
  have hh := (source_involution_centralizer_control h D structural A C hnone hTI).1
  rwa [(source_parabolic h D structural A C hnone hTI).1] at hh

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
