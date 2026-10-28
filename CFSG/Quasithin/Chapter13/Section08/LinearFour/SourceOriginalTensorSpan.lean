module
public import Theory.Representation.BinaryConjugationSection.ScalarGrowth
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedPlane
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalGeneration
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorTensor

/-!
# Exact first-tensor and exterior kernels in the original maximal quotient

Recover the four-element field from the selected quotient's faithful
covered-A₆ action. Its original U_H-image has field dimension one. If the
U₀-image were that same line, the actual point residual and relative plane
normalizer would preserve it; their proved generation and irreducibility
exclude this. The index |U₀:V|=16 forces field dimension two and U₀∩W=V.
The existing residual-cubic argument then gives field dimension three and
S∩W=V for S=⟨U₀^{L₁}⟩, using the same original quotient coordinates.

The final application constructs the tensor and exterior markings from the
original natural setup. It retains the selected maximal quotient, original
g, full kernel, faithful covered action, binary degree alternatives and
L₀ chief bound. Normalization by LT places the same-g tensor span inside
U_L without requiring the arbitrary supplied conjugator to lie in L.

Compatible second-tensor movement and exclusion of degree six remain
unproved. This does not establish nine chief factors or 13.8.28. The
original natural/F.9 setup and quotient-factor data remain with their
existing source producers; earlier 13.8.27(b) is owned by
qt-d-138-six-g2-source and final discharge by qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29--30, printed p.964.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare.PlaneSpan BinaryLinear.FlagCoordinates
open Representation.Hexacode Atlas.Codes
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The two successive source spans have exact kernel V on the original
maximal quotient. The field structure is recovered from its faithful action;
no additional shear or scalar-character placement is assumed. -/
theorem source_original_maximal_span_kernels
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane)
    (N : Subgroup G) (hN : L ≤ normalizer N) (hVN : V ≤ N)
    (hproper : ¬ Source.UL L H V₃ ≤ N)
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    (σ : Representation (ZMod 2) HexEvenAutomorphisms Z) [IsIrreducible σ]
    (hfaith : Function.Injective σ)
    (q : BinaryConjugationSection L (Source.UL L H V₃) N
      (σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (g : G) (hgLT : g ∈ L ⊔ (T:Subgroup G))
    (hproduct : U0 (Source.UH H V₃) V₂ =
      Source.UH H V₃ ⊔ (Source.UH H V₃).conjBy g⁻¹)
    (hVU : V ≤ U0 (Source.UH H V₃) V₂)
    (hindex : V.relIndex (U0 (Source.UH H V₃) V₂) = 16)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hUV : U0 (Source.UH H V₃) V₂ ≤ Source.VH H V)
    (hfirst : p.imageSpace (U0 (Source.UH H V₃) V₂) = firstSpace) :
    Source.UH H V₃ ⊓ N = V₃ ∧
      U0 (Source.UH H V₃) V₂ ⊓ N = V ∧
      conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁) ⊓ N = V ∧
      Nat.card (q.imageSpace (Source.UH H V₃)) = 4 ∧
      Nat.card (q.imageSpace (U0 (Source.UH H V₃) V₂)) = 16 ∧
      Nat.card (q.imageSpace
        (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁))) = 64 := by
  have hgen := source_original_local_generators s eL
  let : Finite Z := Finite.of_surjective
    (fun x : Source.UL L H V₃ => (q.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  let πL := eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let η := σ.comp πL
  let : IsIrreducible η := (irreducible_comp_surjective_iff πL
    (eL.surjective.comp (QuotientGroup.mk'_surjective _)) σ).mpr inferInstance
  have hquadratic := TwelveDimensional.scalar_quadratic σ hfaith
  let := TwelveDimensional.fieldModule σ hquadratic
  let := TwelveDimensional.fieldTower σ hquadratic
  let := TwelveDimensional.field_finite σ hquadratic
  let := TwelveDimensional.fieldRepresentation_irreducible σ hquadratic
  let τ := TwelveDimensional.fieldRepresentation σ hquadratic
  have hz := TwelveDimensional.fieldRepresentation_scalar σ hquadratic
  have hdegrees := TwelveDimensional.field_finrank_three_or_nine τ hz
  have hfactor := Section07.ModelExclusions.covered_factorization s ⟨eL⟩
  have h1L : sourceOne L T V₁ ≤ L :=
    LocalAction.one_le_L_of_factorization L T V₁ s.normalizes_L hfactor
  have hD1 : zero L ≤ sourceOne L T V₁ :=
    LocalAction.zero_le_one_of_factorization L T V₁ hfactor
  have h1H : sourceOne L T V₁ ≤ H := le_sup_left.trans hH.1.2
  have hDG : zero L ≤ G2 V₂ := by
    exact ((residual_le (centralPreimage L)).trans
      (Section07.ModelExclusions.NaturalModels.centralPreimage_centralizes s)).trans
      ((centralizer_le (s.plane_le_seed.trans s.seed_le)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hTUL : (T:Subgroup G) ≤ normalizer (Source.UL L H V₃) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (conjugateSpanBy (Source.UH H V₃) L).map _ = _
    have htU : t ∈ normalizer (Source.UH H V₃ : Set G) :=
      le_normalizer_conjugateSpanBy V₃ H (hH.1.2 (mem_sup_right ht))
    rw [map_conjugateSpanBy,mem_normalizer_iff_map_conj_eq.mp htU,
      mem_normalizer_iff_map_conj_eq.mp (s.normalizes_L ht)]
    rfl
  have hnspan : L ⊔ (T:Subgroup G) ≤ normalizer (Source.UL L H V₃) :=
    sup_le (le_normalizer_conjugateSpanBy _ _) hTUL
  have hSU : U0 (Source.UH H V₃) V₂ ≤ Source.UL L H V₃ := by
    rw [hproduct]
    refine sup_le (le_conjugateSpanBy _ _) ?_
    rintro _ ⟨u,hu,rfl⟩
    exact (mem_normalizer_iff.mp ((normalizer (Source.UL L H V₃ : Set G)).inv_mem
      (hnspan hgLT)) u).mp (le_conjugateSpanBy _ _ hu)
  have hc (x : zero L) : πL (inclusion (zero_le L) x) ∈ center HexEvenAutomorphisms := by
    rw [←source_zero_cover_image L eL]
    exact mem_map_of_mem πL x.property
  let c : zero L →* center HexEvenAutomorphisms :=
    (πL.comp (inclusion (zero_le L))).codRestrict _ hc
  let χ : zero L →* Fˣ := centerCharacter.toMonoidHom.comp c
  have hχ : Function.Surjective χ := by
    intro a
    have ha : (centerCharacter.symm a).val ∈ ((zero L).subgroupOf L).map πL := by
      rw [source_zero_cover_image L eL]
      exact (centerCharacter.symm a).property
    obtain ⟨x,hx,he⟩ := ha
    refine ⟨⟨x,hx⟩,?_⟩
    change centerCharacter (c ⟨x,hx⟩) = a
    have he' : c ⟨x,hx⟩ = centerCharacter.symm a := Subtype.ext he
    rw [he',centerCharacter.apply_symm_apply]
  have hscalar (x : zero L) (w : Z) :
      η (inclusion (zero_le L) x) w = (χ x : F) • w :=
    centerCharacter_action τ hz (c x) w
  have hDU : zero L ≤ normalizer (Source.UH H V₃) :=
    hDH.trans (le_normalizer_conjugateSpanBy _ _)
  have hD0 : zero L ≤ normalizer (U0 (Source.UH H V₃) V₂) :=
    hDG.trans (G2_normalizes_U0 _ _)
  obtain ⟨hk,hc4⟩ := source_original_maximal_seed_image s hab h hH hcentral hDH eL
    ρ d π hker honto hnatural hplane N hN hVN hproper η q
  have hd1 := source_field_image_dimension L (Source.UL L H V₃) N (Source.UH H V₃)
    (zero L) η q (zero_le L) χ hχ hscalar hDU (le_conjugateSpanBy _ _) 1 (by simpa using hc4)
  have hF : Nat.card F = 4 := (Nat.card_eq_fintype_card).trans field_card
  obtain ⟨hd2,hk2⟩ := q.scalar_growth_and_kernel (zero L) (zero_le L) χ hχ hscalar
    (Source.UH H V₃) (U0 (Source.UH H V₃) V₂) V (UH_le_U0 _ _) hSU hVU hVN hDU hD0
    ((sourceOne L T V₁).subgroupOf L) ((G2 V₂).subgroupOf L) hgen
    (fun j => le_normalizer_conjugateSpanBy _ _ (h1H j.property))
    (fun k => G2_normalizes_U0 _ _ k.property)
    1 (by decide) (by rw [hF]; decide) hd1 (by omega) (by rw [hF]; exact hindex)
  have hpker : IsPGroup 2 π.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 H).comap_subtype
  obtain ⟨hd3,hk3⟩ := source_span_kernel_of_original_seed s h hH hcentral ρ d π
    hpker honto hnatural hplane ξ p hexterior hUV hfirst hVU hindex
    (Source.UL L H V₃) N (zero L) η q h1L hgen hSU hVN (zero_le L) hD1 χ hχ hscalar hD0 hd2 τ hz
  refine ⟨hk,hk2,hk3,hc4,?_,?_⟩
  · change Nat.card (q.scalarImage (zero L) (zero_le L) χ hχ hscalar _ hD0) = 16
    rw [Module.natCard_eq_pow_finrank (K := F),hF,hd2]
    norm_num
  · change Nat.card (q.scalarImage (zero L) (zero_le L) χ hχ hscalar _
      (hD1.trans (le_normalizer_conjugateSpanBy _ _))) = 64
    rw [Module.natCard_eq_pow_finrank (K := F),hF,hd3]
    norm_num

/-- Choose the same original maximal quotient with all three literal kernel
intersections and image orders, retaining its degree alternatives and chief bound. -/
theorem exists_source_original_span_maximal_kernels
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane)
    (g : G) (hgLT : g ∈ L ⊔ (T:Subgroup G))
    (hproduct : U0 (Source.UH H V₃) V₂ =
      Source.UH H V₃ ⊔ (Source.UH H V₃).conjBy g⁻¹)
    (hVU : V ≤ U0 (Source.UH H V₃) V₂)
    (hindex : V.relIndex (U0 (Source.UH H V₃) V₂) = 16)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hUV : U0 (Source.UH H V₃) V₂ ≤ Source.VH H V)
    (hfirst : p.imageSpace (U0 (Source.UH H V₃) V₂) = firstSpace) :
    ∃ U W : NormalNode L,
      U.val.map L.subtype = Source.UL L H V₃ ∧
      V ≤ W.val.map L.subtype ∧ W ⋖ U ∧
      U.val ≤ W.val ⊔ (zero L).subgroupOf L ∧
      ∃ hbin : IsElementaryAbelian 2 (Section W U),
        let _ := hbin
        ∃ σ : Representation (ZMod 2) Atlas.Codes.HexEvenAutomorphisms
            (Additive (Section W U)),
          IsIrreducible σ ∧ Function.Injective σ ∧
          σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
            binarySectionRepresentation W U ∧
          (∃ q : BinaryConjugationSection L (Source.UL L H V₃)
            (W.val.map L.subtype)
            (σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))),
            Source.UH H V₃ ⊓ W.val.map L.subtype = V₃ ∧
              U0 (Source.UH H V₃) V₂ ⊓ W.val.map L.subtype = V ∧
              conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁) ⊓
                W.val.map L.subtype = V ∧
              Nat.card (q.imageSpace (Source.UH H V₃)) = 4 ∧
              Nat.card (q.imageSpace (U0 (Source.UH H V₃) V₂)) = 16 ∧
              Nat.card (q.imageSpace (conjugateSpanBy (U0 (Source.UH H V₃) V₂)
                (sourceOne L T V₁))) = 64) ∧
          (Module.finrank (ZMod 2) (Additive (Section W U)) = 6 ∨
            Module.finrank (ZMod 2) (Additive (Section W U)) = 18) ∧
          ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
            Module.finrank (ZMod 2) (Additive (Section W U)) ≤
              2 * t.noncentralTwoCount := by
  obtain ⟨U,W,hUm,hVW,hWU,hcover,hbin,σ,hirr,hfaith,hσ,⟨q⟩,hdegree,hcount⟩ :=
    exists_source_original_span_maximal_chief s hab h hH hF hcentral hDH eL
      ρ d π hker honto hnatural hplane
  let := hbin
  let := hirr
  have hN : L ≤ normalizer (W.val.map L.subtype) := by
    have hh := W.val.le_normalizer_map L.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hproper : ¬ Source.UL L H V₃ ≤ W.val.map L.subtype := by
    intro hh
    rw [←hUm] at hh
    exact hWU.lt.not_ge ((map_le_map_iff_of_injective L.subtype_injective).mp hh)
  have hk := source_original_maximal_span_kernels s hab h hH hcentral hDH eL
    ρ d π hker honto hnatural hplane (W.val.map L.subtype) hN hVW hproper
    σ hfaith q g hgLT hproduct hVU hindex ξ p hexterior hUV hfirst
  exact ⟨U,W,hUm,hVW,hWU,hcover,hbin,σ,hirr,hfaith,hσ,⟨q,hk⟩,hdegree,hcount⟩

open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The original first tensor and exterior construction discharge all span
markings and indices in the selected maximal quotient. The original factor
maps and conjugator are unchanged, and its possible degree six is retained. -/
theorem exists_source_original_span_kernels_from_original_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G))
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* HexEvenAutomorphisms) :
    ∃ U W : NormalNode L,
      U.val.map L.subtype = Source.UL L H V₃ ∧
      V ≤ W.val.map L.subtype ∧ W ⋖ U ∧
      U.val ≤ W.val ⊔ (zero L).subgroupOf L ∧
      ∃ hbin : IsElementaryAbelian 2 (Section W U),
        let _ := hbin
        ∃ σ : Representation (ZMod 2) Atlas.Codes.HexEvenAutomorphisms
            (Additive (Section W U)),
          IsIrreducible σ ∧ Function.Injective σ ∧
          σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
            binarySectionRepresentation W U ∧
          (∃ q : BinaryConjugationSection L (Source.UL L H V₃)
            (W.val.map L.subtype)
            (σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))),
            Source.UH H V₃ ⊓ W.val.map L.subtype = V₃ ∧
              U0 (Source.UH H V₃) V₂ ⊓ W.val.map L.subtype = V ∧
              conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁) ⊓
                W.val.map L.subtype = V ∧
              Nat.card (q.imageSpace (Source.UH H V₃)) = 4 ∧
              Nat.card (q.imageSpace (U0 (Source.UH H V₃) V₂)) = 16 ∧
              Nat.card (q.imageSpace (conjugateSpanBy (U0 (Source.UH H V₃) V₂)
                (sourceOne L T V₁))) = 64) ∧
          (Module.finrank (ZMod 2) (Additive (Section W U)) = 6 ∨
            Module.finrank (ZMod 2) (Additive (Section W U)) = 18) ∧
          ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
            Module.finrank (ZMod 2) (Additive (Section W U)) ≤
              2 * t.noncentralTwoCount := by
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (le_conjugateSpanBy V G₁)
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  obtain ⟨_,_,hVU,_,_,_,_,_,hprod,_,hindex⟩ := source_tensor_from_original_seed ds
    H (Source.UH H V₃) A L2 hHeq hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI (le_conjugateSpanBy _ _) hgen hdim g hg
  have hUV := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2 (T:Subgroup G)
    hK hG hV hgen s.seed_le
  obtain ⟨p,_,hfirst,_,_,_⟩ := source_exterior_geometry_from_original_seed
    s hab h hH hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane
    eU hcoords hUcard hu hgenerate
  exact exists_source_original_span_maximal_kernels s hab h hH hF hcentral hDH eL
    ρ d π₄ hker honto hnatural hplane g (hALT g.property) hprod hVU hindex
    (BinaryParabolicExteriorSquare.SingularPresentation.action π₄) p (fun _ _ => rfl) hUV hfirst

end CFSG.Quasithin.Chapter13.Section08.LinearFour
