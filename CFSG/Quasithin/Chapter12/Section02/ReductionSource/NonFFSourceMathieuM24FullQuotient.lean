module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24ResidualImage

/-!
# The full centralizer quotient of the original marked M₂₄ cocode

For B, the literal image of L_z in C_G(z)/O₂(C_G(z)), the original cocode
marking identifies O₂(B) with V/V_z, equivariantly with the natural binary
four-space on the same six tetrads. Thus |O₂(B)| = 16 and B/O₂(B) is the
full triple cover 3·A₆. The extraspecial core gives a faithful action of the
full centralizer quotient in binary dimension twelve. The actual Sylow
image normalizes B, and a normal quasisimple component strictly contains B.
Its complete earlier-source simple/three-cover catalogue is retained.

The original M₂₄ Sylow forces a factor 2⁸ in the quotient order. Hence
any identified 3·M₂₂ component is proper. Cubic-center chief
factors and James's minimum degree force irreducibility of the actual
12-dimensional action. The quotient is then the concrete 3·M₂₂·2, retaining
its cubic kernel. Component identification, construction of the whole
cocode marking, and final application remain with source assembly owner
qt-d-1222-nonff-mathieu; the independent Aschbacher–Segev recognition theorem
belongs to qt-d-1222-j4-simple-type-recognition. The conditional final
theorems here do not assert those missing source results.

Source: Aschbacher–Smith, Proposition 8.2.13 and Theorem 8.2.14, printed
pp.722–723; A.3.6 and the containing-component argument in A.3.12.
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open scoped IsMulCommutative commutatorElement

public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Faithful conjugation by the full centralizer quotient on the actual
extraspecial central quotient, of binary dimension twelve. -/
theorem sourceOrbit_m24_centralizer_quotient_faithful_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let C := centralizer ({(z : G)} : Set G)
    ∃ he : IsExtraspecial 2 (pCore 2 C),
      let := he
      ∃ ρ : Representation (ZMod 2) (C ⧸ pCore 2 C)
        (ExtraspecialSquare.Space (pCore 2 C)),
        Function.Injective ρ ∧
        Module.finrank (ZMod 2) (ExtraspecialSquare.Space (pCore 2 C)) = 12 ∧
        ∀ (c : C) (x : pCore 2 C),
          ρ (QuotientGroup.mk' (pCore 2 C) c)
            (Additive.ofMul (QuotientGroup.mk' (center (pCore 2 C)) x)) =
          Additive.ofMul (QuotientGroup.mk' (center (pCore 2 C)) (MulAut.conjNormal c x)) := by
  let C := centralizer ({(z : G)} : Set G)
  have hcore : pCore 2 C = sourceClosure L D.sourceOrbit z := by
    apply map_injective C.subtype_injective
    exact D.sourceOrbit_m24_centralizer_core_eq_closure h hmany hV hq hnon a E hE z hz hne
  obtain ⟨he,hcard,_⟩ := D.sourceOrbit_m24_centralizer_extraspecial h hmany hV hq hnon a E hE z hz hne
  have heC : IsExtraspecial 2 (pCore 2 C) := hcore.symm ▸ he
  let := heC
  have hc : Nat.card (pCore 2 C) = 2^(12+1) := by rw [hcore,hcard]; norm_num
  have hz2 : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property)
    (fun he => hne (Subtype.ext he))
  have hTC : (T : Subgroup G) ≤ C := fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  have hchar : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) (isTwoLocal_involution_centralizer hz2) hTC)
  obtain ⟨ρ,hρ,hact⟩ := MathieuSextet.faithful_core_action hchar
  exact ⟨heC,ρ,hρ,ExtraspecialSquare.space_finrank (pCore 2 C) 12 hc,hact⟩


/-- The ambient Sylow and original M₂₄ cocode force a factor 2⁸ in the
full centralizer quotient. Consequently an identified 3·M₂₂ subgroup
cannot be the whole quotient. -/
theorem sourceOrbit_m24_centralizer_quotient_two_divisor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let C := centralizer ({(z : G)} : Set G)
    2 ^ 8 ∣ Nat.card (C ⧸ pCore 2 C) := by
  let C := centralizer ({(z : G)} : Set G)
  let f := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hf : Function.Surjective f := a.surjective.comp
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq))
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    exact D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq)
  have hcore := (D.sourceOrbit_m24_cocode_block_core h hmany hV hq hnon a E hE).2.2
  have hv := (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).2.1
  have hLc : Nat.card (pCore 2 L) = 2048 := by
    rw [←card_map_of_injective L.subtype_injective]
    change Nat.card (L.pCoreIn 2) = 2048
    rw [←hcore]
    exact hv
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hL : Nat.card L = 244823040 * 2048 := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,Nat.card_congr e.toEquiv,
      m24_order,hk,hLc]
  have hdivL : 2 ^ 21 ∣ Nat.card L := by rw [hL]; norm_num
  have hdivT : 2 ^ 21 ∣ Nat.card T :=
    T.pow_dvd_card_of_pow_dvd_card (hdivL.trans L.card_subgroup_dvd_card)
  have hTC : (T : Subgroup G) ≤ C := fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  have hdivC : 2 ^ 21 ∣ Nat.card C := hdivT.trans (card_dvd_of_le hTC)
  have hc : pCore 2 C = sourceClosure L D.sourceOrbit z := by
    apply map_injective C.subtype_injective
    exact D.sourceOrbit_m24_centralizer_core_eq_closure h hmany hV hq hnon a E hE z hz hne
  have hCc : Nat.card (pCore 2 C) = 8192 := by
    rw [hc]
    exact (D.sourceOrbit_m24_centralizer_extraspecial h hmany hV hq hnon a E hE z hz hne).2.1
  have hC := card_eq_card_quotient_mul_card_subgroup (pCore 2 C)
  rw [hCc] at hC
  apply (Nat.mul_dvd_mul_iff_right (by decide : 0 < 8192)).mp
  change 2 ^ 21 ∣ Nat.card (C ⧸ pCore 2 C) * 8192
  rw [←hC]
  exact hdivC

/-- Once the containing component is identified, the
original twelve-dimensional action supplies irreducibility and the full
3.M22.2 quotient. The cubic kernel of its map to Aut(M22) is retained. -/
theorem sourceOrbit_m24_centralizer_quotient_extension_of_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hcomponent : ∃ K : Subgroup ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G))),
      K.Normal ∧ Nonempty (K ≃* M22TripleCover)) :
    let C := centralizer ({(z : G)} : Set G)
    Nonempty ((C ⧸ pCore 2 C) ≃*
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.actionGroup) ∧
      ∃ π : (C ⧸ pCore 2 C) →* MulAut M22, Function.Surjective π ∧ Nat.card π.ker = 3 := by
  obtain ⟨he,ρ,hρ,hd,hact⟩ :=
    D.sourceOrbit_m24_centralizer_quotient_faithful_action h hmany hV hq hnon a E hE z hz hne
  let := he
  obtain ⟨K,hK,⟨e⟩⟩ := hcomponent
  have hproper : K ≠ ⊤ := by
    intro ht
    let eQ := ((topEquiv.symm.trans (MulEquiv.subgroupCongr ht).symm).trans e)
    have hdvd := D.sourceOrbit_m24_centralizer_quotient_two_divisor
      h hmany hV hq hnon a E hE z hz hne
    dsimp only at hdvd
    rw [Nat.card_congr eQ.toEquiv,M22TripleCover.card] at hdvd
    norm_num at hdvd
  let := hK
  let : IsIrreducible (ρ.comp K.subtype) :=
    MathieuSextet.triple_cover_irreducible e (ρ.comp K.subtype) (hρ.comp K.subtype_injective) hd
  let eqC := coveringExtensionEquiv ρ hρ K e hd hproper
  exact ⟨⟨eqC⟩,exists_cubic_kernel_of_coveringExtension eqC⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
