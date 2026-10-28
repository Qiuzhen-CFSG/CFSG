module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveSymmetry
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupAction.Order512FiveFourInvolutionSeed
public import Theory.GroupAction.Order512FiveFourSquareTransport

/-!
# An involution in the original five-residual outside its derived layer

The actual endpoint action on the residual Frattini quotient has precisely
the original full core as kernel. Thus the original group of order twenty
acts faithfully on that quotient, without selecting a split lift upstairs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem paired_actions_of_image
    {K V W : Type*} [Group K] [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (a : K →* MulAut V) (b : K →* MulAut W)
    (e : a.range ≃* FiveFour.Group)
    (p : V →* (W →* Multiplicative (ZMod 2)))
    (hp : Function.Injective p) (hcard : Nat.card V = Nat.card W)
    (he : ∀ k v w, p (a k v) (b k w) = p v w) :
    ∃ (a' : FiveFour.Group →* MulAut V) (b' : FiveFour.Group →* MulAut W)
      (π : K →* FiveFour.Group), Function.Surjective π ∧
      Function.Injective a' ∧ Function.Injective b' ∧
      (∀ k, a' (π k) = a k) ∧ (∀ k, b' (π k) = b k) := by
  let π := e.toMonoidHom.comp a.rangeRestrict
  have hπ : Function.Surjective π := e.surjective.comp a.rangeRestrict_surjective
  let a' : FiveFour.Group →* MulAut V := a.range.subtype.comp e.symm.toMonoidHom
  have ha' : Function.Injective a' := Subtype.val_injective.comp e.symm.injective
  have hleft (k : K) : a' (π k) = a k := by
    change ((e.symm (e (a.rangeRestrict k)) : a.range) : MulAut V) = a k
    rw [e.symm_apply_apply]
    rfl
  have hker : π.ker ≤ b.ker := by
    intro k hk
    have hka : a k = 1 := by
      rw [←hleft,hk,map_one]
    apply MulEquiv.ext
    intro w
    apply (p.binary_pairing_flip_bijective hcard hp).1
    apply MonoidHom.ext
    intro v
    simpa only [MonoidHom.flip_apply, hka, MulAut.one_apply] using he k v w
  let ek := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let b' : FiveFour.Group →* MulAut W :=
    (QuotientGroup.lift π.ker b hker).comp ek.symm.toMonoidHom
  have hright (k : K) : b' (π k) = b k := by
    change QuotientGroup.lift π.ker b hker (ek.symm (π k)) = b k
    have hh : ek (QuotientGroup.mk' π.ker k) = π k := rfl
    rw [←hh,ek.symm_apply_apply]
    rfl
  have he' (k : FiveFour.Group) (v : V) (w : W) : p (a' k v) (b' k w) = p v w := by
    obtain ⟨k,rfl⟩ := hπ k
    rw [hleft,hright]
    exact he k v w
  have hb' : Function.Injective b' := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro k hk
    apply ha'
    rw [map_one]
    apply MulEquiv.ext
    intro v
    apply hp
    apply MonoidHom.ext
    intro w
    simpa only [show b' k = 1 from hk, MulAut.one_apply] using he' k v w
  exact ⟨a',b',π,hπ,ha',hb',hleft,hright⟩

private theorem involution_of_frattini_action_image
    {K P : Type*} [Group K] [Group P] [Finite P]
    (ρ : K →* MulAut P) (hP : IsPGroup 2 P)
    (hPcard : Nat.card P = 512)
    (hElem : IsElementaryAbelian 2 (frattini P))
    (hDcard : Nat.card (frattini P) = 32)
    (hupper : frattini P = Subgroup.upperCentralSeries P 2)
    (hZcard : Nat.card (center P) = 2)
    (e : ((quotientAut (frattini P)).comp ρ).range ≃* FiveFour.Group) :
    ∃ x : P, x ^ 2 = 1 ∧ x ∉ frattini P := by
  let D := frattini P
  let V := P ⧸ D
  let Z := (center P).subgroupOf D
  let W := D ⧸ Z
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 W := {
    exponent_dvd_p := (MonoidHom.exponent_dvd (f := QuotientGroup.mk' Z)
      (QuotientGroup.mk'_surjective Z)).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }
  let : MulDistribMulAction K P := MulDistribMulAction.compHom P ρ
  let : IsInvariant K P D := isInvariant_of_characteristic D
  let : IsInvariant K P (center P) := isInvariant_of_characteristic (center P)
  let : IsInvariant K D Z := isInvariant_subgroupOf (center P) D
  let : MulDistribMulAction K W := quotientMulDistribMulAction Z inferInstance
  let a : K →* MulAut V := (quotientAut D).comp ρ
  let b : K →* MulAut W := MulDistribMulAction.toMulAut K W
  have hDupper : D ≤ Subgroup.upperCentralSeries P 2 := hupper.le
  have hZD : center P ≤ D := by
    change center P ≤ frattini P
    rw [hupper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono P (show 1 ≤ 2 by decide)
  have hVcard : Nat.card V = 16 := by
    have hh := D.index_mul_card
    change Nat.card V * Nat.card D = Nat.card P at hh
    rw [hDcard,hPcard] at hh
    omega
  have hWcard : Nat.card W = 16 := by
    have hh := Z.index_mul_card
    change Nat.card W * Nat.card Z = Nat.card D at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv,hZcard,hDcard] at hh
    omega
  have hsq (x : P) : x ^ 2 ∈ D := by
    apply (QuotientGroup.eq_one_iff (N := D) _).mp
    change QuotientGroup.mk' D (x ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) _
  let eZ : center P ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hZcard (Nat.card_zmod 2)
  let p := Theory.GroupAction.Order512FiveFour.squarePairing D hDupper eZ
  have hp : Function.Injective p :=
    (Theory.GroupAction.Order512FiveFour.squarePairing_bijective
      D hDupper eZ (hWcard.trans hVcard.symm)).1
  have hact (k : K) :
      (∀ v w, p (a k v) (b k w) = p v w) ∧
      (∀ v, elementarySecondCenterSquare D hDupper hsq (a k v) =
        b k (elementarySecondCenterSquare D hDupper hsq v)) := by
    apply Theory.GroupAction.Order512FiveFour.square_layers_transport
      D hDupper hsq eZ (ρ k)
      (fun d => characteristic_iff_le_comap.mp inferInstance (ρ k) d.property)
      (a k) (b k)
    · intro x
      exact quotientAut_apply_mk D (ρ k) x
    · intro d
      rfl
  obtain ⟨a',b',π,hπ,ha',hb',hleft,hright⟩ := paired_actions_of_image a b e p hp
    (hVcard.trans hWcard.symm) (fun k => (hact k).1)
  exact Theory.GroupAction.Order512FiveFour.exists_involution_outside_of_five_four_layers
    D hDupper hsq eZ (commutator_le_frattini_of_isPGroup (p := 2)) hVcard hWcard
    FiveFour.action FiveFour.action_injective a' b' ha' hb'
    (by
      intro k v w
      obtain ⟨k,rfl⟩ := hπ k
      rw [hleft,hright]
      exact (hact k).1 v w)
    (by
      intro k v
      obtain ⟨k,rfl⟩ := hπ k
      rw [hleft,hright]
      exact (hact k).2 v)

/-- The original action on the residual Frattini quotient has the exact core
kernel and the actual Frobenius group of order twenty as its image. -/
theorem source_quintic_large_five_residual_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let R := ⁅H.pCoreIn 2,A⁆
    ∃ ρ : H →* MulAut R,
      (∀ h r, (ρ h r : G) = (h : G) * (r : G) * (h : G)⁻¹) ∧
      let α := (quotientAut (frattini R)).comp ρ
      α.ker = pCore 2 H ∧ Nonempty (α.range ≃* FiveFour.Group) := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let R := ⁅Q,A⁆
  let C := H ⊓ centralizer (U : Set G)
  have hHR : H ≤ normalizer (R : Set G) :=
    (source_quintic_five_normalizer_action
      hG T hempty hM hu hmany hcard e H hH hi A hAH hA).2.2
  let ρ : H →* MulAut R := R.normalizerMonoidHom.comp (inclusion hHR)
  let α := (quotientAut (frattini R)).comp ρ
  have hρ (h : H) (r : R) : (ρ h r : G) = (h : G) * (r : G) * (h : G)⁻¹ := rfl
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp
    (hAH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  obtain ⟨_,_,_,_,_,hUR,_,_⟩ := source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hkerQ : ρ.ker ≤ pCore 2 H := by
    intro h hh
    have hh' : ρ h = 1 := hh
    have hhC : (h : G) ∈ C := by
      refine ⟨h.property, mem_centralizer_iff.mpr ?_⟩
      intro u hu
      have he := congrArg (fun f : MulAut R => (f ⟨u,hUR hu⟩ : G)) hh'
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hm : (h : G) ∈ (pCore 2 H).map H.subtype := hCQ hhC
    obtain ⟨k,hk,he⟩ := hm
    exact (Subtype.ext he : k = h) ▸ hk
  have hkerTwo : IsPGroup 2 α.ker :=
    (isPGroup_quotientAut_frattini_kernel ((isPGroup_pCoreIn 2 H).to_le hRQ)).comap_of_ker_isPGroup
      ρ (pCore_isPGroup.to_le hkerQ)
  have hkerle : α.ker ≤ pCore 2 H := le_sSup ⟨inferInstance,hkerTwo⟩
  have hPhi : (frattini R).map R.subtype = U :=
    (source_quintic_large_five_residual_structure
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2.2.2.2.1
  have hderived : ⁅Q,Q⁆ = U := (source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hQker : pCore 2 H ≤ α.ker := by
    intro h hh
    have hhQ : (h : G) ∈ Q := mem_map_of_mem H.subtype hh
    apply MulEquiv.ext
    intro v
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (frattini R) v
    change quotientAut (frattini R) (ρ h) (QuotientGroup.mk' (frattini R) r) =
      QuotientGroup.mk' (frattini R) r
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hm : ((ρ h r : R) : G) / (r : G) ∈ U := by
      rw [hρ,div_eq_mul_inv]
      exact hderived.le (commutator_mem_commutator hhQ (hRQ r.property))
    rw [←hPhi] at hm
    obtain ⟨k,hk,he⟩ := hm
    exact (Subtype.ext he : k = ρ h r / r) ▸ hk
  have heq : α.ker = pCore 2 H := le_antisymm hkerle hQker
  obtain ⟨_,⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient
    hG T hempty hM hu hmany hcard e H hH hi
  refine ⟨ρ,hρ,heq,?_⟩
  exact ⟨(QuotientGroup.quotientKerEquivRange α).symm |>.trans
    ((QuotientGroup.quotientMulEquivOfEq heq).trans (eSuz.trans FiveFour.suzukiZeroEquiv.symm))⟩

private theorem source_quintic_large_five_residual_intrinsic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let R := ⁅H.pCoreIn 2,A⁆
    Nat.card R = 512 ∧ Nat.card (commutator R) = 32 ∧
      commutator R = frattini R ∧ commutator R = Subgroup.upperCentralSeries R 2 ∧
      IsElementaryAbelian 2 (commutator R) ∧ Nat.card (center R) = 2 := by
  let U := conjugateSpanBy (localModule T M) H
  let R := ⁅H.pCoreIn 2,A⁆
  obtain ⟨_,_,hRcard,_,_,hder,hPhi,hupper,hZ,_⟩ :=
    source_quintic_large_five_residual_structure
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hDmap : (commutator R).map R.subtype = U := by
    rw [map_subtype_commutator]
    exact hder
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let eD : commutator R ≃* U :=
    ((commutator R).equivMapOfInjective R.subtype R.subtype_injective).trans
      (MulEquiv.subgroupCongr hDmap)
  refine ⟨hRcard,?_,?_,?_,IsElementaryAbelian.of_injective eD.toMonoidHom eD.injective,?_⟩
  · exact (Nat.card_congr eD.toEquiv).trans
      (source_quintic_span_card_and_core_radical
        hG T hempty hM hu hmany hcard e H hH hi).1
  · exact map_injective R.subtype_injective (hDmap.trans hPhi.symm)
  · exact map_injective R.subtype_injective (hDmap.trans hupper.symm)
  · rw [←card_map_of_injective R.subtype_injective,hZ]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e

/-- The original large residual contains an actual involution outside the
original elementary quintic span. No further geometric hypothesis is imposed. -/
theorem source_quintic_large_five_residual_seed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    ∃ b ∈ ⁅H.pCoreIn 2,A⁆, b ^ 2 = 1 ∧
      b ∉ conjugateSpanBy (localModule T M) H := by
  let R := ⁅H.pCoreIn 2,A⁆
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨ρ,_,_,⟨eR⟩⟩ := source_quintic_large_five_residual_action
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  obtain ⟨hRcard,hDcard,hPhi,hupper,hElem,hZcard⟩ :=
    source_quintic_large_five_residual_intrinsic
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hRtwo : IsPGroup 2 R := IsPGroup.of_card (n := 9) hRcard
  obtain ⟨b,hb,hbPhi⟩ := involution_of_frattini_action_image ρ hRtwo hRcard
    (hPhi ▸ hElem) (hPhi ▸ hDcard) (hPhi.symm.trans hupper) hZcard eR
  refine ⟨b,b.property,congrArg Subtype.val hb,?_⟩
  intro hbU
  have hDmap : (commutator R).map R.subtype = U := by
    rw [map_subtype_commutator]
    exact (source_quintic_large_five_residual_structure
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2.2.2.1
  have hm : (b : G) ∈ (commutator R).map R.subtype := hDmap.symm ▸ hbU
  obtain ⟨x,hx,he⟩ := hm
  have hbD : b ∈ commutator R := (Subtype.ext he : x = b) ▸ hx
  exact hbPhi (hPhi ▸ hbD)

end CFSG.Quasithin.Chapter14.Section06
