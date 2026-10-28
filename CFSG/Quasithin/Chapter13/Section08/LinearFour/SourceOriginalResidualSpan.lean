module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalTensorSpan
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Original residual actors on the selected maximal quotient

A two-perfect subgroup of LT lies in L because T normalizes L and is a
2-group. Apply this to the literal definition of L₂,₊. The original g,
not a new cubic representative, therefore normalizes every L-normal
selected kernel. All its powers carry S intersect W = V to the same
intersection, since LT normalizes V. The original quotient maps give
all conjugate images order 64, with their exact linear action recorded.
The constructed first/exterior geometry also gives S intersect S^g = U₀
and strict movement of the literal S for this same g.

This removes actor-placement and translated-kernel premises from the
second-tensor comparison. It does not identify two conjugate images or
establish their inequality: exclusion of the maximal quotient of order
64, including the extra-line tensor row, remains to be proved.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29--30, printed p.964.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare.PlaneSpan BinaryLinear.FlagCoordinates
open Representation.Hexacode Atlas.Codes
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original two-residual subgroup lies in L. Its ambient defining
subgroup need not itself lie in L. -/
theorem source_original_residual_le_L
    (hn : (T:Subgroup G) ≤ normalizer (L:Set G))
    (A B P : Subgroup G) (hBA : B ≤ A)
    (hALT : A ≤ L ⊔ (T:Subgroup G))
    (hB : B = (pResidual 2 P).map P.subtype) : B ≤ L := by
  apply le_of_isPPerfect_of_le_sup_of_normalizes B L (T:Subgroup G)
    ?_ T.isPGroup' hn (hBA.trans hALT)
  rw [hB]
  exact isPPerfect_embedded_pResidual 2 P

omit [Finite G] in
private theorem conjugate_kernel_and_image
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    (UL N S V : Subgroup G) (η : Representation (ZMod 2) L Z)
    (q : BinaryConjugationSection L UL N η)
    (hSU : S ≤ UL) (hN : L ≤ normalizer N)
    (hSN : S ⊓ N = V) (g : L) (hgV : (g:G) ∈ normalizer V) :
    S.conjBy (g:G) ⊓ N = V ∧
      q.imageSpace (S.conjBy (g:G)) = (q.imageSpace S).map (η g) ∧
      Nat.card (q.imageSpace (S.conjBy (g:G))) = Nat.card (q.imageSpace S) := by
  have hNg : N.conjBy (g:G) = N := mem_normalizer_iff_map_conj_eq.mp (hN g.property)
  have hVg : V.conjBy (g:G) = V := mem_normalizer_iff_map_conj_eq.mp hgV
  have hUg : UL.conjBy (g:G) = UL := mem_normalizer_iff_map_conj_eq.mp (q.normalized g.property)
  have hSg : S.conjBy (g:G) ≤ UL := (map_mono hSU).trans hUg.le
  refine ⟨?_,q.imageSpace_conjBy S hSU g,?_⟩
  · rw [←hNg]
    change S.map _ ⊓ N.map _ = V
    rw [←map_inf _ _ _ (MulAut.conj (g:G)).injective,hSN]
    exact hVg
  · rw [q.imageSpace_card_eq_relIndex _ hSg,q.imageSpace_card_eq_relIndex _ hSU]
    calc
      N.relIndex (S.conjBy (g:G)) = (N.conjBy (g:G)).relIndex (S.conjBy (g:G)) :=
        congrArg (fun B : Subgroup G => B.relIndex (S.conjBy (g:G))) hNg.symm
      _ = N.relIndex S := relIndex_map_map_of_injective
        (f := (MulAut.conj (g:G)).toMonoidHom) N S (MulAut.conj (g:G)).injective

open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The selected original quotient retains the exact kernels and order-64
images of every original-g translate of the exterior span, together with
its actual intersection and strict movement before projection. The full degree
alternatives and chief bound are retained; no new kernel or actor placement
hypothesis is required. -/
theorem exists_source_original_residual_span_kernels
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
    (P : Subgroup G) (hL2def : L2 = (pResidual 2 P).map P.subtype)
    (hL2A : L2 ≤ A) (hgL2 : (g:G) ∈ L2)
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
    ∃ hgL : (g:G) ∈ L, ∃ U W : NormalNode L,
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
                (sourceOne L T V₁))) = 64 ∧
              (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) ⊓
                (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)).conjBy
                  ((g:G)⁻¹) = U0 (Source.UH H V₃) V₂ ∧
              ¬ (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)).conjBy
                  ((g:G)⁻¹) ≤ conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁) ∧
              ∀ n : ℤ,
                (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)).conjBy
                  ((g:G) ^ n) ⊓ W.val.map L.subtype = V ∧
                q.imageSpace ((conjugateSpanBy (U0 (Source.UH H V₃) V₂)
                  (sourceOne L T V₁)).conjBy ((g:G) ^ n)) =
                  (q.imageSpace (conjugateSpanBy (U0 (Source.UH H V₃) V₂)
                    (sourceOne L T V₁))).map
                    ((σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
                      ((⟨g,hgL⟩ : L) ^ n)) ∧
                Nat.card (q.imageSpace ((conjugateSpanBy (U0 (Source.UH H V₃) V₂)
                  (sourceOne L T V₁)).conjBy ((g:G) ^ n))) = 64) ∧
          (Module.finrank (ZMod 2) (Additive (Section W U)) = 6 ∨
            Module.finrank (ZMod 2) (Additive (Section W U)) = 18) ∧
          ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
            Module.finrank (ZMod 2) (Additive (Section W U)) ≤
              2 * t.noncentralTwoCount := by
  have hgL : (g:G) ∈ L :=
    source_original_residual_le_L s.normalizes_L A L2 P hL2A hALT hL2def hgL2
  obtain ⟨U,W,hUm,hVW,hWU,hcover,hbin,τ,hirr,hfaith,hτ,
      ⟨q,hk1,hk2,hk3,hc1,hc2,hc3⟩,hdegree,hcount⟩ :=
    exists_source_original_span_kernels_from_original_seed s hab h hH hcentral hHeq
      A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
      hF hDH eL
  let := hbin
  let := hirr
  have hN : L ≤ normalizer (W.val.map L.subtype) := by
    have hh := W.val.le_normalizer_map L.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (le_conjugateSpanBy V G₁)
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  obtain ⟨_,_,_,_,_,_,_,_,hprod,_,hindex⟩ := source_tensor_from_original_seed ds
    H (Source.UH H V₃) A L2 hHeq hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI (le_conjugateSpanBy _ _) hgen hdim g hg
  have h0U : U0 (Source.UH H V₃) V₂ ≤ Source.UL L H V₃ := by
    rw [hprod]
    apply sup_le (le_conjugateSpanBy _ _)
    have hnorm := mem_normalizer_iff_map_conj_eq.mp (q.normalized (L.inv_mem hgL))
    exact (map_mono (le_conjugateSpanBy (Source.UH H V₃) L)).trans hnorm.le
  have h1L : sourceOne L T V₁ ≤ L :=
    LocalAction.one_le_L_of_factorization L T V₁ s.normalizes_L
      (Section07.ModelExclusions.covered_factorization s ⟨eL⟩)
  have hSU : conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁) ≤
      Source.UL L H V₃ := conjugateSpanBy_le h0U (h1L.trans q.normalized)
  let S := conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)
  obtain ⟨p,_,_,_,hindexS,hinter⟩ := source_exterior_geometry_from_original_seed
    s hab h hH hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane
    eU hcoords hUcard hu hgenerate
  have h0V := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2
    (T:Subgroup G) hK hG hV hgen s.seed_le
  have hSV : S ≤ Source.VH H V := conjugateSpanBy_le h0V
    ((le_sup_left.trans hH.1.2).trans (le_normalizer_conjugateSpanBy _ _))
  have h0S : U0 (Source.UH H V₃) V₂ ≤ S := le_conjugateSpanBy _ _
  have h0g : (U0 (Source.UH H V₃) V₂).conjBy ((g:G)⁻¹) = U0 (Source.UH H V₃) V₂ :=
    mem_normalizer_iff_map_conj_eq.mp (G2_normalizes_U0 _ _ ((G2 V₂).inv_mem (hAG g.property)))
  have hSS : S ⊓ S.conjBy ((g:G)⁻¹) = U0 (Source.UH H V₃) V₂ := by
    apply le_antisymm
    · exact (inf_le_inf hSV (map_mono hSV)).trans hinter.le
    · exact le_inf h0S (h0g.ge.trans (map_mono h0S))
  have hproperS : ¬ S ≤ U0 (Source.UH H V₃) V₂ := by
    intro hh
    have he : S = U0 (Source.UH H V₃) V₂ := le_antisymm hh h0S
    change V.relIndex S = 64 at hindexS
    rw [he,hindex] at hindexS
    norm_num at hindexS
  have hmove : ¬ S.conjBy ((g:G)⁻¹) ≤ S := by
    intro hh
    have he : S.conjBy ((g:G)⁻¹) = S := eq_of_le_of_card_ge hh (by
      rw [conjBy,card_map_of_injective (MulAut.conj ((g:G)⁻¹)).injective])
    rw [he,inf_idem] at hSS
    exact hproperS hSS.le
  refine ⟨hgL,U,W,hUm,hVW,hWU,hcover,hbin,τ,hirr,hfaith,hτ,
    ⟨q,hk1,hk2,hk3,hc1,hc2,hc3,hSS,hmove,?_⟩,hdegree,hcount⟩
  intro n
  have hnV := (normalizer (V:Set G)).zpow_mem (s.normalizes_V (hALT g.property)) n
  obtain ⟨hk,ha,hc⟩ := conjugate_kernel_and_image (Source.UL L H V₃)
    (W.val.map L.subtype) (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) V
    (τ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) q hSU hN hk3
    ((⟨g,hgL⟩ : L) ^ n) hnV
  exact ⟨hk,ha,hc.trans hc3⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
