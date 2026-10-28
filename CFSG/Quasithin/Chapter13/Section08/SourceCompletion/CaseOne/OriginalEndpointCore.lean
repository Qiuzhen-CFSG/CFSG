module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalSmallMovement
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
public import Theory.GroupTheory.QuotientPointCore
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.Cover

/-!
# The actual endpoint core and the whole original cover

Return the original span by inverse conjugation by the specified endpoint
conjugator. Abelianness puts U_L inside O₂(H), and the returned O₂(H) is
normalized by the actual point centralizer. The centralizer is normal in
the preimage of the quotient point stabilizer, so its two-subgroup image
lies in the literal point radical. Mutual quadratic action then bounds
that image by four, including when the quotient point is constant.

This supplies the previously explicit endpoint index in OriginalSmallMovement.
Consequently the literal U_L/V is the five-dimensional augmentation cover,
with its constant line, actor kernel and original L-marking retained.
The original U_L has order 512 and contains U₂ with index two. Neither
abelianness, endpoint index nor these orders is an added source premise.

The central-seed 13.4.1 application, noncentral-seed chief-factor comparison
and strict-denominator assembly remain unfinished; this module does not
assert the full 13.8.33--34 conclusion.
Source: Aschbacher--Smith, proof of 13.8.33, printed pp.967--968.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The returned span lies in the actual point radical, using the specified
endpoint conjugator. The source application below supplies abelianness. -/
theorem span_returned_point_core
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hab : IsMulCommutative (Source.UL L H V₃))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (z : V₁) (hz : (z : G) ≠ 1) :
    ∃ u : Source.UH H V₃, MulAut.conj (c.gb : G) (u : G) = (z : G) ∧
      (Source.UL L H V₃).map (MulAut.conj (c.gb : G)).symm.toMonoidHom ≤ H ∧
      Source.starImage H ((Source.UL L H V₃).map (MulAut.conj (c.gb : G)).symm.toMonoidHom) ≤
        (A6Endgame.PointNormalizer.pointStabilizer a u).pCoreIn 2 := by
  let _ := hab
  let ψ := (MulAut.conj (c.gb : G)).symm
  let R := (Source.UL L H V₃).map ψ.toMonoidHom
  let Y := (Source.QH H).map ψ.toMonoidHom
  have hpoint := (ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator
    d h c hDH hDg).2.2
  have hu : ψ (z : G) ∈ Source.UH H V₃ := mem_map_equiv.mp (hpoint z.property)
  let u : Source.UH H V₃ := ⟨ψ (z : G),hu⟩
  have hULT : Source.UL L H V₃ ≤ (T : Subgroup G) := by
    apply (Section07.span_UH_L_le_core (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)).trans
    exact (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hULQ : Source.UL L H V₃ ≤ Source.QH H := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro x hx
    have hc : x ∈ centralizer (Source.UH H V₃ : Set G) :=
      ((le_centralizer (Source.UL L H V₃)).trans
        (centralizer_le (le_conjugateSpanBy _ _))) hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨h.T_le_H (hULT hx), fun v hv => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc v hv)]
      exact V₁.one_mem⟩
  have hA : c.Aone V₁ ≤ Source.UL L H V₃ :=
    (endpoint_commutator d h c hDH hDg hcentral).2.trans (le_conjugateSpanBy _ _)
  have hULJ : Source.UL L H V₃ ≤ CriticalGeometry.vertexGroup L (T : Subgroup G) H c.gamma := by
    rw [Terminal.endpoint_eq_line_normalizer d c hH]
    exact ((le_centralizer (Source.UL L H V₃)).trans (centralizer_le hA)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hRH : R ≤ H := by
    rw [c.vertexGroup_gamma] at hULJ
    rintro _ ⟨x,hx,rfl⟩
    exact mem_map_equiv.mp (hULJ hx)
  have hHc : H = centralizer ({(z : G)} : Set G) :=
    (hH.trans d.first_normalizer).trans
      (A6Endgame.PointNormalizer.normalizer_eq_point_centralizer V₁ d.line_card z z.property hz)
  have hCs : H.map ψ.toMonoidHom = centralizer ({(u : G)} : Set G) := by
    ext x
    rw [mem_map_equiv]
    change ψ.symm x ∈ H ↔ x ∈ centralizer ({ψ (z : G)} : Set G)
    rw [hHc,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    constructor
    · intro he
      simpa only [map_mul,MulEquiv.apply_symm_apply] using congrArg ψ he
    · intro he
      simpa only [map_mul,MulEquiv.symm_apply_apply] using congrArg ψ.symm he
  have hy : Y ≤ centralizer ({(u : G)} : Set G) :=
    (map_mono (pCoreIn_le 2 H)).trans_eq hCs
  have hny : centralizer ({(u : G)} : Set G) ≤ normalizer (Y : Set G) := by
    rw [← hCs]
    exact (map_mono (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H))).trans
      (le_normalizer_map ψ.toMonoidHom)
  have hcore := point_core_image_le_stabilizer_core 2 H (Source.UH H V₃) V₁ Y
    ((d.line_le_uh H).trans h.UH_le_H) h.H_centralizes
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    a.action a.normalizes a.conjugation u ((isPGroup_pCoreIn 2 H).map ψ.toMonoidHom) hy hny
  refine ⟨u,(MulAut.conj (c.gb : G)).apply_symm_apply z,hRH,?_⟩
  exact (map_mono (subgroupOf_mono H (map_mono hULQ))).trans hcore

/-- The genuine endpoint image bound from the unchanged original setup.
The whole cover, including its fixed point, supplies the quadratic bound. -/
theorem full_denominators_endpoint_index
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
 :
    c.Qgamma.relIndex (Source.UL L H V₃) ≤ 4 := by
  obtain ⟨hab,F,hF,_⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  obtain ⟨u,_,hRH,hpoint⟩ := span_returned_point_core d h c hH hDH hDg hcentral hab a z
    (fun he => hz (Subtype.ext he))
  let ψ := (MulAut.conj (c.gb : G)).symm
  let R := (Source.UL L H V₃).map ψ.toMonoidHom
  let B := Source.starImage H R
  let A := B.map e.toMonoidHom
  let ρ := tildeRepresentation H (Source.UH H V₃) V₁ a
  let w := Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)
  have hS : (A6Endgame.PointNormalizer.pointStabilizer a u).map e.toMonoidHom =
      BinaryPermutation.SixCorePoint.stabilizer (F w) := by
    ext g
    rw [mem_map_equiv]
    change ρ (e.symm g) w = w ↔ BinaryPermutation.coreRepresentation (Fin 6) g (F w) = F w
    have hh : F (ρ (e.symm g) w) = BinaryPermutation.coreRepresentation (Fin 6) g (F w) := by
      rw [hF,e.apply_symm_apply]
    rw [← hh]
    exact F.injective.eq_iff.symm
  have hAC : A ≤ (BinaryPermutation.SixCorePoint.stabilizer (F w)).pCoreIn 2 := by
    have hh := map_mono (f := e.toMonoidHom) hpoint
    rw [map_pCoreIn_of_injective 2 _ _ e.injective,hS] at hh
    exact hh
  have hback (X : Subgroup G) :
      (X.map (MulAut.conj (c.gb : G)).toMonoidHom).map ψ.toMonoidHom = X := by
    rw [map_map]
    have he : ψ.toMonoidHom.comp (MulAut.conj (c.gb : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      exact (MulAut.conj (c.gb : G)).symm_apply_apply x
    rw [he,map_id]
  have hd : ⁅R,⁅R,Source.UH H V₃⁆⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map ψ.toMonoidHom)
      (full_denominators_span_quadratic d h c hH hDH hDg hcentral hab).2.2.2.2
    rw [map_commutator,map_commutator,Subgroup.map_bot] at hh
    change ⁅⁅R,(c.Ugamma V₃).map ψ.toMonoidHom⁆,R⁆ = ⊥ at hh
    rw [show (c.Ugamma V₃).map ψ.toMonoidHom = Source.UH H V₃ from hback _] at hh
    rwa [commutator_comm] at hh
  let s : ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.ConjugationSection
      H (Source.UH H V₃) V₁ ρ := {
    le := h.UH_le_H
    normalizes := a.normalizes
    centralizes := h.H_centralizes
    line_le := d.line_le_uh H
    quotient := MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
    surjective := MulEquiv.toMultiplicative_toAdditive.symm.surjective.comp
      (QuotientGroup.mk'_surjective _)
    kernel := by
      ext x
      exact QuotientGroup.eq_one_iff x
    conjugates := a.conjugation }
  have hq : Representation.BinaryOffender.IsQuadratic ρ B := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨b,hb,rfl⟩ v
    obtain ⟨x,hx⟩ := s.surjective (Multiplicative.ofAdd v)
    have hv : (s.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
    rw [← hv,s.displacement]
    apply sub_eq_zero.mp
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    exact (hd.le.trans bot_le)
      (commutator_mem_commutator hg (commutator_mem_commutator hb x.property))
  have hqA : ∀ g ∈ A, ∀ b ∈ A, ∀ v : BinaryPermutation.core (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) g
        (BinaryPermutation.coreRepresentation (Fin 6) b v - v) =
          BinaryPermutation.coreRepresentation (Fin 6) b v - v := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨b,hb,rfl⟩ v
    obtain ⟨x,rfl⟩ := F.surjective v
    have hh := congrArg F (hq g hg b hb x)
    dsimp only [ρ] at hh
    simpa only [hF,map_sub,MulEquiv.coe_toMonoidHom] using hh
  have hc := Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.cover_point_core_bound
    A (F w) hAC hqA
  rw [card_map_of_injective e.injective] at hc
  change Nat.card (Source.starImage H R) ≤ 4 at hc
  rw [CriticalGeometry.starImage_card H R hRH] at hc
  change (Source.QH H).relIndex ((Source.UL L H V₃).map ψ.toMonoidHom) ≤ 4 at hc
  have hQback : c.Qgamma.map ψ.toMonoidHom = Source.QH H := hback _
  rw [← hQback,relIndex_map_map_of_injective _ _ ψ.injective] at hc
  exact hc

/-- The original whole section is the five-dimensional augmentation cover.
The endpoint image bound is proved from the same original hypotheses. -/
theorem full_denominators_whole_cover
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    IsMulCommutative (Source.UL L H V₃) ∧
    Source.UL L H V₃ = ⁅Source.UL L H V₃,L⁆ ∧
    ∃ hUL : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G),
      ∃ hN : (V.subgroupOf (Source.UL L H V₃)).Normal,
        let _ := hN
        ∃ hE : IsElementaryAbelian 2 (Source.ULsection L H V₃ V),
          let _ := hE
          ∃ hA : (actorKernel (L ⊔ (T : Subgroup G)) V).Normal,
            let _ := hA
            ∃ eB : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸
                actorKernel (L ⊔ (T : Subgroup G)) V) ≃* Equiv.Perm (Fin 6),
              (eB.toMonoidHom.comp ((QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)).comp
                (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)))).range =
                  alternatingGroup (Fin 6) ∧
              ∃ ρ : Representation (ZMod 2)
                  ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V)
                  (Additive (Source.ULsection L H V₃ V)),
                SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
                  (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)) hUL ρ ∧
                Coinvariants.ker ρ = ⊤ ∧
                (let σ := ρ.comp (eB.symm.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype)
                 Nonempty (Representation.Equiv (BinaryPermutation.alternatingCoreRepresentation (Fin 6)) σ)) ∧
                Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 5 := by
  exact full_denominators_whole_cover_of_endpoint_index d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
    (full_denominators_endpoint_index d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief)

/-- Exact size of the original span and its original U₂ index, with no
endpoint-index premise. -/
theorem full_denominators_whole_size
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    Nat.card (Source.UL L H V₃) = 512 ∧
      (Source.U2 H V V₂).relIndex (Source.UL L H V₃) = 2 := by
  exact full_denominators_whole_size_of_endpoint_index d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
    (full_denominators_endpoint_index d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
