module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalSeedCentralizer

/-!
# The original noncentral seed and centralizer quotient action

A seed outside V has an index-two centralizer in both Q = O₂(LT) and
R = L₁T in the noncentral branch. Correcting any element of R by an
element of Q gives a representative centralizing the seed, so that
centralizer has the entire original marked parabolic image.

The five-generator argument makes the literal quotient Q/C_Q(U_L)
elementary abelian. Its denominator is normalized by LT, and its
commutative structure makes Q act trivially. Descending this conjugation
action through the proved original natural-action kernel gives its
six-letter representation, with dimension between one and five.
The source application constructs the seed and both indices along with
this action; no abstract module is substituted for the quotient.

Source: Aschbacher--Smith, proof of 13.8.33, printed p.968. Identifying
this action as the required natural module or cover and comparing the
actual chief filtrations remain necessary. The central-seed application
of 13.4.1 and the strict-denominator/13.8.34 assembly also remain open.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The index-two centralizer in the original point parabolic has its entire
original marked image. Representatives can be corrected by the actual two-core. -/
theorem original_cover_seed_parabolic_centralizer
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W)
    (u : Source.U1 H K V₃) (hu : (u : G) ∉ V)
    (hH : H = G₁) (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hnc : ¬ Source.U1 H K V₃ ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    let P := L ⊔ (T : Subgroup G)
    let Q := P.pCoreIn 2
    let R := sourceOne L T V₁ ⊔ (T : Subgroup G)
    let C := centralizer ({(u : G)} : Set G)
    C.relIndex Q = 2 ∧ C.relIndex R = 2 ∧
      ((R ⊓ C).subgroupOf P).map (Section07.NaturalAction.permutation (localNaturalSetup d)) =
        (R.subgroupOf P).map (Section07.NaturalAction.permutation (localNaturalSetup d)) := by
  let P := L ⊔ (T : Subgroup G)
  let Q := P.pCoreIn 2
  let R := sourceOne L T V₁ ⊔ (T : Subgroup G)
  let C := centralizer ({(u : G)} : Set G)
  obtain ⟨hsmall,hiff⟩ := original_cover_seed_core_index d h c hDH hDg hHz
    K hK hprod a e F hF hp u hu
  have hne : C.relIndex Q ≠ 1 := fun he => hnc (hiff.mp he)
  have hpos : 0 < C.relIndex Q := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hiQ : C.relIndex Q = 2 := by
    change C.relIndex Q ≤ 2 at hsmall
    omega
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq (map_subgroupOf_eq_of_le le_sup_right)
  have hQR : Q ≤ R := hQT.trans le_sup_right
  have hRP : R ≤ P := (original_point_parabolic_eq d hH).le.trans inf_le_left
  have hRH : R ≤ H := hHz.1.2
  have hULQ : Source.UL L H V₃ ≤ Q := Section07.span_UH_L_le_core (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have huQ : (u : G) ∈ Q := hULQ ((le_conjugateSpanBy _ _) u.property.1)
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (zpowers (u : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (u : G)
      (show (u : G) ∈ Source.UH H V₃ from u.property.1))
      (fun he => hu (he ▸ V.one_mem))
  have hcomm := (original_cover_seed d h c hDH hDg hHz K hK hprod a e F hF hp).2.2.1
  have hsmallR : C.relIndex R ≤ 2 := by
    simpa only [inf_relIndex_left,zpowers_eq_closure,centralizer_closure] using
      line_centralizer_index_le_two R V₁ (zpowers (u : G)) d.line_card hcard
        (zpowers_le.mpr (hQR huQ))
        ((commutator_mono le_rfl (zpowers_le.mpr u.property)).trans hcomm)
        (le_centralizer_iff.mp (hRH.trans h.H_centralizes))
  have hneR : C.relIndex R ≠ 1 := by
    intro he
    exact hne (relIndex_eq_one.mpr (hQR.trans (relIndex_eq_one.mp he)))
  have hposR : 0 < C.relIndex R := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hiR : C.relIndex R = 2 := by omega
  refine ⟨hiQ,hiR,?_⟩
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  have hk : π.ker = pCore 2 P := ordinary_natural_kernel d h eL
  apply le_antisymm (map_mono (subgroupOf_mono P inf_le_left))
  rintro y ⟨r,hr,rfl⟩
  change (r : G) ∈ R at hr
  by_cases hrC : (r : G) ∈ C
  · exact mem_map.mpr ⟨r,⟨hr,hrC⟩,rfl⟩
  obtain ⟨q,hq,hqC,_⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hiQ
  obtain ⟨s,hs,hsC,hcos⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hiR
  have hrC' := (hcos r hr).resolve_right hrC
  have hqC' := (hcos q (hQR hq)).resolve_right hqC
  have hc : (r : G) * q⁻¹ ∈ C := by
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using C.mul_mem hrC' (C.inv_mem hqC')
  let qP : P := ⟨q,hRP (hQR hq)⟩
  have hqker : qP ∈ π.ker := by
    rw [hk]
    exact (mem_map_iff_mem P.subtype_injective).mp hq
  refine mem_map.mpr ⟨r * qP⁻¹,⟨R.mul_mem hr (R.inv_mem (hQR hq)),hc⟩,?_⟩
  rw [map_mul,map_inv,(show π qP = 1 from hqker),inv_one,mul_one]

/-- The noncentral source quotient, with its literal action along the original
natural six-letter marking. -/
theorem full_denominators_noncentral_core_action
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hnc : ¬ Source.U1 H K V₃ ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    let P := L ⊔ (T : Subgroup G)
    let Q := P.pCoreIn 2
    let C := A6Endgame.ActionAnalysis33.CQUL Q L H V₃
    let R := sourceOne L T V₁ ⊔ (T : Subgroup G)
    ∃ u : Source.U1 H K V₃, (u : G) ∉ V ∧
      ((centralizer ({(u : G)} : Set G)).relIndex Q = 2 ∧
        (centralizer ({(u : G)} : Set G)).relIndex R = 2 ∧
        ((R ⊓ centralizer ({(u : G)} : Set G)).subgroupOf P).map
            (Section07.NaturalAction.permutation (localNaturalSetup d)) =
          (R.subgroupOf P).map (Section07.NaturalAction.permutation (localNaturalSetup d))) ∧
    ∃ hN : (C.subgroupOf Q).Normal,
      let _ := hN
      ∃ hE : IsElementaryAbelian 2 (Q ⧸ C.subgroupOf Q),
        let _ := hE
        ∃ hn : P ≤ normalizer (Q : Set G),
          ∃ ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6))
              (Additive (Q ⧸ C.subgroupOf Q)),
            SectionConjugationAlong P Q C
              (Section07.NaturalAction.permutation (localNaturalSetup d)) hn ρ ∧
            1 ≤ Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) ∧
            Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) ≤ 5 := by
  classical
  let P := L ⊔ (T : Subgroup G)
  let Q := P.pCoreIn 2
  let C := A6Endgame.ActionAnalysis33.CQUL Q L H V₃
  obtain ⟨u,hu,g,hg,hiff,hcase⟩ := full_denominators_seed_core_alternatives d h c hDH hDg
    hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨hi,hN,hE,hcard⟩ := hcase.resolve_left (fun hz => hnc (hiff.mpr hz))
  let _ := hN
  let _ := hE
  have hCQ : C ≤ Q := inf_le_left
  have hn : P ≤ normalizer (Q : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hPU : P ≤ normalizer (Source.UL L H V₃ : Set G) :=
    SectionStructure.LT_normalizes_UL L H T V₃ h.T_le_H d.normalizes_L
  have hPC : P ≤ normalizer (C : Set G) :=
    (le_inf hn (hPU.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hab : ⁅Q,Q⁆ ≤ C := by
    have hh := (Normal.quotient_commutative_iff_commutator_le (N := C.subgroupOf Q)).mp
      (inferInstance : IsMulCommutative (Q ⧸ C.subgroupOf Q))
    have hm : (_root_.commutator Q).map Q.subtype = ⁅Q,Q⁆ := by
      rw [_root_.commutator_def,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    rw [← hm]
    exact (map_mono hh).trans_eq (map_subgroupOf_eq_of_le hCQ)
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  have hk : π.ker = pCore 2 P := ordinary_natural_kernel d h eL
  have hkill : ⁅Q,π.ker.map P.subtype⁆ ≤ C := by
    rw [hk]
    exact hab
  obtain ⟨τ,hτ⟩ := exists_section_representation P Q C π.ker hn hPC hkill
  let eπ := QuotientGroup.quotientKerEquivOfSurjective π
    (full_denominators_natural_surjective d h c hDH hDg)
  let ρ := τ.comp eπ.symm.toMonoidHom
  have hρ : SectionConjugationAlong P Q C π hn ρ := by
    intro p q
    change τ (eπ.symm (π p)) _ = _
    have he : eπ.symm (π p) = QuotientGroup.mk' π.ker p := by
      apply eπ.injective
      rw [eπ.apply_symm_apply]
      rfl
    rw [he]
    exact hτ p q
  have hCne : C ≠ Q := by
    intro he
    have hz : Source.UL L H V₃ ≤ centralizer (Q : Set G) := by
      apply le_centralizer_iff.mp
      exact he ▸ (show C ≤ centralizer (Source.UL L H V₃ : Set G) from inf_le_right)
    exact hnc (hiff.mpr hz)
  have hdimpos : 1 ≤ Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) := by
    have hc : Nat.card (Q ⧸ C.subgroupOf Q) ≠ 1 := by
      intro hc
      have hle : Q ≤ C := relIndex_eq_one.mp hc
      exact hCne (le_antisymm hCQ hle)
    change Nat.card (Additive (Q ⧸ C.subgroupOf Q)) ≠ 1 at hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    by_contra hno
    have hz : Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) = 0 := by omega
    exact hc (by rw [hz,pow_zero])
  have hd : Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) ≤ 5 := by
    change Nat.card (Additive (Q ⧸ C.subgroupOf Q)) ≤ 32 at hcard
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  have hseed := original_cover_seed_parabolic_centralizer d h c hDH hDg hHz
    K hK hprod a e F hF hp u hu hH eL hnc
  exact ⟨u,hu,hseed,hN,hE,hn,ρ,hρ,hdimpos,hd⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
