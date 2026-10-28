module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.StandingAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Faithfulness
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.NaturalSection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Quotient

/-!
# Source marking and local-core assembly for 13.8.6

Apply the universal earlier 13.7.6(3) only after constructing its natural
section from the literal image of [U_H,K] modulo its K-fixed space.
This gives the ordinary A₆ quotient of L and the weight-four point.
The original natural action on V then supplies the compatible L-module
and flag; its degree and ordinary quotient marking are proved, not assumed.
The full faithful H* action, simultaneous point/plane marking, A₄ residual
image and two-kernel parabolic surjection are constructed in both dimensions.
In the cover case, the derived V₃=⟨V₂^L₁⟩ transports the weight-four
condition to every nonzero vector of the actual section plane.

The earlier 13.5.4 implication is applied to the actual L-action and flag.
Its normal-closure and centralizer identities combine with the proved
residual and generation identities to give both core bounds and
U₂=[U₂,L₂]≤U_L. Both relative-normalizer conventions for L₁ and L₂
are identified as literal subgroups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6(1)–(3),(6), p.948; 13.7.6(3), pp.938–939;
13.5.4, p.916; Notations 13.2.1 and 13.3.3, pp.877,885.
The two earlier universal source implications remain explicit permitted
inputs. This conditional assembly does not assert the rank and final
representation clauses (4),(5), nor prove the earlier source theorems.
-/

public section
open Subgroup Module BinaryPermutation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
open TransvectionRecognition EarlierCore Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G]

/-- An actual homomorphism onto one of the two duad parabolics, with its
surjectivity and two-group kernel. -/
@[expose] def ParabolicSurjection (P : Subgroup G) : Prop :=
  (∃ f : P →* duadStabilizer, Function.Surjective f ∧ IsPGroup 2 f.ker) ∨
  (∃ f : P →* a6DuadStabilizer, Function.Surjective f ∧ IsPGroup 2 f.ker)

private theorem parabolicSurjection_of_image (H P : Subgroup G) (hPH : P ≤ H)
    (ψ : H →* Equiv.Perm (Fin 6)) (hk : IsPGroup 2 ψ.ker)
    (hi : (P.subgroupOf H).map ψ = BinaryFlags.H1 ∨
      (P.subgroupOf H).map ψ = BinaryFlags.L1) : ParabolicSurjection P := by
  rcases hi with hi | hi
  · let f := imageSurjection H P hPH ψ BinaryFlags.H1 hi
    refine Or.inl ⟨flagDuadEquiv.toMonoidHom.comp f,
      flagDuadEquiv.surjective.comp (imageSurjection_surjective H P hPH ψ _ hi), ?_⟩
    have he : (flagDuadEquiv.toMonoidHom.comp f).ker = f.ker := by
      ext x
      exact flagDuadEquiv.map_eq_one_iff
    rw [he]
    exact imageSurjection_kernel H P hPH ψ _ hi hk
  · let f := imageSurjection H P hPH ψ BinaryFlags.L1 hi
    refine Or.inr ⟨flagA6DuadEquiv.toMonoidHom.comp f,
      flagA6DuadEquiv.surjective.comp (imageSurjection_surjective H P hPH ψ _ hi), ?_⟩
    have he : (flagA6DuadEquiv.toMonoidHom.comp f).ker = f.ker := by
      ext x
      exact flagA6DuadEquiv.map_eq_one_iff
    rw [he]
    exact imageSurjection_kernel H P hPH ψ _ hi hk

private theorem elementary_of_order_two (Z : Subgroup G) (h : Nat.card Z = 2) :
    IsElementaryAbelian 2 Z := by
  let : IsMulCommutative Z := (isCyclic_of_prime_card h).isMulCommutative
  refine ⟨?_⟩
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro z
  rw [← h]
  exact pow_card_eq_one'

variable {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Simultaneous coordinates for the literal Ṽ₂ and Ṽ₃, compatible with
the full H* action. Cover weight is retained before taking the natural quotient. -/
@[expose] def ModelFlag (V₂ : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6)) : Prop :=
  (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6),
    (∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u)) ∧
    (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.naturalPointSpace ∧
    (sectionImage H V₃ V₁ V₃).map E.toLinearMap =
      OrbitModels.plane.map (coreToNatural (Fin 6))) ∨
  (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6),
    (∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u)) ∧
    (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace ∧
    (sectionImage H V₃ V₁ V₃).map E.toLinearMap = OrbitModels.plane ∧
    (∀ v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap,
      v ≠ 0 → OrbitModels.weight v = 4))

/-- The constructed source marking, its A₄ residual image, actual parabolic
surjection and intrinsic two-core quotient. The coordinate conjugation is explicit. -/
@[expose] def MarkedParabolic (K V₂ : Subgroup G) (T : Sylow 2 G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
    ∃ φ : Source.Hstar H →* Equiv.Perm (Fin 6), Function.Injective φ ∧
      (∃ (eK : Source.starImage H K ≃* alternatingGroup (Fin 6)) (g : Equiv.Perm (Fin 6)),
        ∀ k : Source.starImage H K, φ k = g⁻¹ * (eK k).val * g) ∧
      ModelFlag V₂ ρ φ ∧
      ((Source.K2 H V₂).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.K ∧
      ParabolicSurjection (Source.K2 H V₂ ⊔ (T : Subgroup G)) ∧
      Nonempty (((Source.K2 H V₂ ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Source.K2 H V₂ ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))

/-- Combine the earlier point witness with the actual natural L-module.
Flag dimensions, weight-four generation and faithfulness are all discharged. -/
theorem compatible_marking_of_earlier [Finite G]
    {T : Sylow 2 G} {L V V₂ K : Subgroup G}
    (d : ComponentSetup T L V V₁ V₂ V₃)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (hKH : K ≤ H) (hLK : localResidual L V₁ ≤ K)
    (hHZ : H ≤ normalizer (V₁ : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hm : NaturalSection.SixPointMarking H K V₂ V₃ V₁ ρ) :
    MarkedParabolic K V₂ T ρ := by
  have ho := d.extend.flag_orders
  let _ : IsElementaryAbelian 2 V₁ := elementary_of_order_two V₁ ho.1
  have hV₂ : V₂ ≤ Source.UH H V₃ := d.extend.plane_le_seed.trans (le_conjugateSpanBy V₃ H)
  have hdim := sectionImage_seed_finrank (H := H)
    (d.extend.line_le_plane.trans d.extend.plane_le_seed) ho.1 ho.2.2
  have finish (φ : Source.Hstar H →* Equiv.Perm (Fin 6)) (hφ : Function.Injective φ)
      (hT : (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁)
      (hH : H ≤ centralizer (V₁ : Set G))
      (hi : ((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
        ((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1) :
      ((Source.K2 H V₂).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.K ∧
        ParabolicSurjection (Source.K2 H V₂ ⊔ (T : Subgroup G)) ∧
        Nonempty (((Source.K2 H V₂ ⊔ (T : Subgroup G) : Subgroup G) ⧸
          pCore 2 (Source.K2 H V₂ ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨himage, hquot⟩ := residual_and_quotient_of_marked_preimage T H V₂ V₁ hH hT φ hφ hi
    refine ⟨himage, ?_, hquot⟩
    apply parabolicSurjection_of_image H _
      (sup_le (Source.K2_le H V₂) (hT.trans (commutatorPreimage_le H V₂ V₁)))
      (φ.comp (QuotientGroup.mk' (pCore 2 H))) ?_ ?_
    · rw [source_coordinate_kernel H φ hφ]
      exact pCore_isPGroup
    · rwa [K2_sup_sylow T H V₂ V₁ hH hT]
  obtain ⟨eK, hm⟩ := hm
  rcases hm with ⟨E, he, hp⟩ | ⟨E, he, hp⟩
  · have hf := source_action_faithful H K T hK hprod ρ
      (alternatingNaturalRepresentation (Fin 6))
      ComponentSieve.SixAndG2.NaturalSix.alternatingAction_injective eK E he
    have hc := source_centralizer_bound ρ hρ hf hHZ
    obtain ⟨g, φ, hφ, hφK, hφE, hpoint, hplane, hT, hH, hi⟩ :=
      CompatibleFlags.natural_compatible_marking T K hK hprod ρ hρ hc eK E he hp
        d.plane_stable d.seed_stable hdim hV₂ hHZ ho.1
    let E' := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom g⁻¹))
    refine ⟨φ, hφ, ⟨eK, g, hφK⟩, Or.inl ⟨E', hφE, ?_, ?_⟩, finish φ hφ hT hH hi⟩
    · rw [← hpoint, ← Submodule.map_comp]; rfl
    · rw [← hplane, ← Submodule.map_comp]; rfl
  · have hf := source_action_faithful H K T hK hprod ρ
      (alternatingCoreRepresentation (Fin 6))
      (ComponentSieve.SixAndG2.NaturalSix.coreAction_injective.comp Subtype.val_injective) eK E he
    have hc := source_centralizer_bound ρ hρ hf hHZ
    have hg := d.flag_generation.1
    have hs : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2)
        {v | ∃ a ∈ Source.starImage H (localResidual L V₁),
          ∃ x ∈ sectionImage H V₃ V₁ V₂, ρ a x = v} := by
      calc
        sectionImage H V₃ V₁ V₃ = sectionImage H V₃ V₁
            (conjugateSpanBy V₂ (localResidual L V₁)) := congrArg _ hg
        _ = _ := CompatibleFlags.sectionImage_conjugateSpan ρ hρ V₂ _ hV₂ (hLK.trans hKH)
    obtain ⟨g, φ, hφ, hφK, hφE, hpoint, hplane, hw, _, _, hT, hH, hi⟩ :=
      CompatibleFlags.augmentation_compatible_marking T K hK hprod ρ hρ hc eK E he hp
        d.plane_stable d.seed_stable hdim (localResidual L V₁) hs hV₂ hHZ ho.1
    let r := coreRepresentation (Fin 6)
    let E' := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹))
    refine ⟨φ, hφ, ⟨eK, g, hφK⟩, Or.inr ⟨E', hφE, ?_, ?_, ?_⟩, finish φ hφ hT hH hi⟩
    · rw [← hpoint, ← Submodule.map_comp]; rfl
    · rw [← hplane, ← Submodule.map_comp]; rfl
    · intro v hv hv0
      have hv' : v ∈ ((sectionImage H V₃ V₁ V₃).map E.toLinearMap).map (r g⁻¹) := by
        rw [← Submodule.map_comp]
        exact hv
      obtain ⟨w, hw', rfl⟩ := hv'
      rw [CompatibleFlags.cover_weight_map]
      apply hw w hw'
      intro hz
      exact hv0 (by rw [hz, map_zero])

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
open TransvectionRecognition EarlierCore
variable {G : Type*} [Group G] [Finite G]

/-- The requested conditional prerequisite for 13.8.6, from its actual
module hypotheses and standing natural action. All additional marking,
faithfulness, flag-generation and earlier-applicability premises are proved.
Only the universal earlier 13.7.6(3) and 13.5.4 implications remain inputs. -/
theorem source_marking_and_core (T : Sylow 2 G) (L V V₁ V₂ V₃ M H K : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (s : StandingFlag T L V V₁ V₂ V₃)
    (natural : StandingNatural L V (le_sup_left.trans s.normalizes_V))
    (earlier1376 : NaturalSection.Earlier1376 L (localResidual L V₁) T
      (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (earlier1354 : Earlier1354 T L V)
    (hH : H ∈ Source.Hz (localResidual L V₁) T (normalizer (V₁ : Set G)) M)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (hmodel :
      (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
        ∀ (k : Source.starImage H K) u,
          E (ρ k u) = alternatingNaturalRepresentation (Fin 6) (eK k) (E u)) ∨
      (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6),
        ∀ (k : Source.starImage H K) u,
          E (ρ k u) = alternatingCoreRepresentation (Fin 6) (eK k) (E u))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ ∧ localResidual L V₁ ≤ K ∧
      MarkedParabolic K V₂ T ρ ∧
      residual ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)) = localResidual L V₁ ∧
      residual ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₂ : Set G)) = localResidual L V₂ ∧
      localI L V₁ V₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
        (normalizer (V₂ : Set G)) ∧
      residual (localI L V₁ V₂) = localResidual L V₂ ∧
      localI L V₁ V₂ ⊓ centralizer (V₂ : Set G) = (localI L V₁ V₂).pCoreIn 2 ∧
      localResidual L V₂ ≤ L ∧
      V = conjugateSpanBy V₃ (localResidual L V₂) ∧ V = ⁅V, localResidual L V₂⁆ ∧
      ⁅Source.K2 H V₂, localResidual L V₂⁆ ≤
        (Source.K2 H V₂).pCoreIn 2 ⊓ (localResidual L V₂).pCoreIn 2 ∧
      Source.U2 H V V₂ = ⁅Source.U2 H V V₂, localResidual L V₂⁆ ∧
      Source.U2 H V V₂ ≤ Source.UL L H V₃ := by
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k, hk, 1, (T : Subgroup G).one_mem, mul_one k⟩
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    change t ∈ (H : Set G)
    rw [hprod]
    exact ⟨1, K.one_mem, t, ht, one_mul t⟩
  have hV₁ : V₁ ≤ Source.UH H V₃ :=
    (s.line_le_plane.trans s.plane_le_seed).trans (le_conjugateSpanBy V₃ H)
  obtain ⟨hL, hgen, hLK, _, hm⟩ := NaturalSection.apply_earlier L (localResidual L V₁)
    T (normalizer (V₁ : Set G)) M H K V₂ V₃ V₁ earlier1376 hH hV₁ hKH hK ρ hρ eK hmodel
  let d := s.componentSetup (standing_natural_earlier natural) hL
  have hmark := compatible_marking_of_earlier d hK hprod hKH hLK hH.2.1 ρ hρ hm
  obtain ⟨hI, hIr, hIc, h2L, hVgen, hVcomm⟩ := d.extend.earlier_identities earlier1354
  have hcores := d.core_bounds_and_generation earlier1354 H hTH
  exact ⟨hL, hgen, hLK, hmark,
    residual_relative_normalizer_eq L T V₁ T.isPGroup' s.normalizes_L s.line_stable,
    residual_relative_normalizer_eq L T V₂ T.isPGroup' s.normalizes_L s.plane_stable,
    hI, hIr, hIc, h2L, hVgen, hVcomm, hcores⟩
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
