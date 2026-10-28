module
public import Theory.Representation.BinaryConjugationSection.Comparison
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalResidualSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondRows

/-!
# Both second tensor rows on the original maximal quotient

Keep the selected L-normal kernel W and the original residual conjugator g.
For S = ⟨U₀^{L₁}⟩ and D = ⟨S^{⟨g⟩}⟩, the canonical second section on
V₀/U₀ maps its image of D to (U_L/W)/image(U₀). This map is specified on
actual group elements, has exactly the image of D intersect W as kernel,
and intertwines every original g-power. It is injective on every S-translate.
Both complete second tensor rows, the V/V₂ marking, the V_H/U₀ slice and
the original factor maps are retained on this very same second section.

If the maximal quotient has order 64, the comparison is surjective onto a
quotient of order four. This constructs a common equivariant quotient for
the remaining invariant-kernel argument; it does not exclude that order.
In particular projection onto the extra trivial tensor summand can be
injective on each marked slice, so slice injectivity alone is not movement.
No pure second-factor scalar cubic or additional kernel premise is imposed.

The nine-factor bound, extra-line movement and terminal contradiction remain
with this owner. Earlier 13.8.27(b) remains with qt-d-138-six-g2-source and
final source discharge with qt-d-1381-source.

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
open Theory.LinearAlgebra BinaryFivePointStabilizer
open BinaryLinear.OuterCyclic
open scoped TensorProduct
open CyclicSeedTensor QuadraticFourGroup.TensorClassification
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- Construct both marked tensor rows and their comparison with the same
selected maximal quotient. The original g acts compatibly on both sides;
an order-64 quotient would leave an order-four common quotient. -/
theorem exists_source_original_second_comparison
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
    (hQA : H.pCoreIn 2 ≤ A) (hnA : G2 V₂ ≤ normalizer A)
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
      ∃ hbin : IsElementaryAbelian 2 (Section W U),
        let _ := hbin
        let _ : CommGroup (Section W U) := inferInstance
        let _ : AddCommGroup (Additive (Section W U)) := inferInstance
        let _ : Module (ZMod 2) (Additive (Section W U)) := inferInstance
        ∃ τ : Representation (ZMod 2) HexEvenAutomorphisms (Additive (Section W U)),
          IsIrreducible τ ∧ Function.Injective τ ∧
          τ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
            binarySectionRepresentation W U ∧
          (Module.finrank (ZMod 2) (Additive (Section W U)) = 6 ∨
            Module.finrank (ZMod 2) (Additive (Section W U)) = 18) ∧
          (∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
            Module.finrank (ZMod 2) (Additive (Section W U)) ≤ 2 * t.noncentralTwoCount) ∧
          ∃ q : BinaryConjugationSection L (Source.UL L H V₃) (W.val.map L.subtype)
            (τ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))),
            U0 (Source.UH H V₃) V₂ ⊓ W.val.map L.subtype = V ∧
            Nat.card (q.imageSpace (U0 (Source.UH H V₃) V₂)) = 16 ∧
            ∃ hn : ((U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)).Normal,
              let _ := hn
              ∃ he : IsElementaryAbelian 2 (V0 (Source.VH H V) V₂ ⧸
                (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)),
                let _ := he
                let Q₂ := V0 (Source.VH H V) V₂ ⧸
                  (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)
                let _ : CommGroup Q₂ := inferInstance
                let _ : AddCommGroup (Additive Q₂) := inferInstance
                let _ : Module (ZMod 2) (Additive Q₂) := inferInstance
                ∃ (e : Equiv.Perm (Fin 3) ≃* LinearGroup 2)
                  (τ₂ : Representation (ZMod 2) (K × Equiv.Perm (Fin 3))
                    (Additive (V0 (Source.VH H V) V₂ ⧸
                      (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))))
                  (p : BinaryConjugationSection (G2 V₂) (V0 (Source.VH H V) V₂)
                    (U0 (Source.UH H V₃) V₂) (τ₂.comp π)),
                  (∃ cV : BinaryConjugationSection A V V₂
                    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom).comp
                      (eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))),
                    cV.imageSpace V₃ = Submodule.span (ZMod 2) {first}) ∧
                  (∀ v : V0 (Source.VH H V) V₂, (p.coordinates v).toAdd =
                    Additive.ofMul (QuotientGroup.mk'
                      ((U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)) v)) ∧
                  (∃ i : σ.dual.IntertwiningMap (τ₂.comp (MonoidHom.inl K (Equiv.Perm (Fin 3)))),
                    Function.Injective i ∧ i.range.toSubmodule = p.imageSpace (Source.VH H V) ∧
                    ((∃ E : (externalTensor σ.dual
                        (TransitiveSeedCover.planeNatural e.toMonoidHom)).Equiv τ₂,
                      ∀ u, E (u ⊗ₜ[ZMod 2] first) = i u) ∨
                     (∃ E : (externalTensor σ.dual
                        ((TransitiveSeedCover.planeNatural e.toMonoidHom).prod
                          (Representation.trivial (ZMod 2) (Equiv.Perm (Fin 3)) (ZMod 2)))).Equiv τ₂,
                      ∀ u, E (u ⊗ₜ[ZMod 2] (first,(1 : ZMod 2))) = i u))) ∧
                  e (eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)) first = second ∧
                let S := conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)
                let D := conjugateSpanBy S (zpowers (g:G))
                let E := q.imageSpace (U0 (Source.UH H V₃) V₂)
                let η := τ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
                ∃ (hDA : D ≤ Source.UL L H V₃) (hDB : D ≤ V0 (Source.VH H V) V₂),
                ∃ f : p.imageSpace D →ₗ[ZMod 2] Additive (Section W U) ⧸ E,
                  (∀ x : D, f ⟨(p.coordinates (inclusion hDB x)).toAdd,
                    (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB x,x.property,rfl⟩⟩ =
                      E.mkQ (q.coordinates (inclusion hDA x)).toAdd) ∧
                  LinearMap.ker f = (p.imageSpace (D ⊓ W.val.map L.subtype)).comap
                    (p.imageSpace D).subtype ∧
                  (∀ (n : ℤ) (w : p.imageSpace D),
                    w.val ∈ p.imageSpace (S.conjBy ((g:G)^n)) → f w = 0 → w = 0) ∧
                  (∀ (n : ℤ) (w : p.imageSpace D),
                    f ⟨(τ₂.comp π) ⟨(g:G)^n,(G2 V₂).zpow_mem (hAG g.property) n⟩ w,
                      p.imageSpace_apply_mem D _
                        (le_normalizer_conjugateSpanBy S (zpowers (g:G)) (zpow_mem_zpowers _ _))
                        w w.property⟩ =
                    E.mapQ E (η ((⟨g,hgL⟩:L)^n))
                      (fun v hv => q.imageSpace_apply_mem _ _
                        (G2_normalizes_U0 _ _ ((G2 V₂).zpow_mem (hAG g.property) n)) v hv)
                      (f w)) ∧
                  (Nat.card (Additive (Section W U)) = 64 →
                    Function.Surjective f ∧ Nat.card (Additive (Section W U) ⧸ E) = 4) := by
  obtain ⟨hgL,U,W,hUm,hVW,hWU,hcover,hbin,τ,hirr,hfaith,hτ,
      ⟨q,hk1,hk2,hk3,hc1,hc2,hc3,hSS,hmove,hpowers⟩,hdegree,hcount⟩ :=
    exists_source_original_residual_span_kernels s hab h hH hcentral hHeq
      A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hALT hVA hAG hπI
      hgen hdim g hg P hL2def hL2A hgL2 ρ d π₄ hker honto hnatural hpoint hplane
      eU hcoords hUcard hu hgenerate hF hDH eL
  let := hbin
  let : CommGroup (Section W U) := inferInstance
  let : AddCommGroup (Additive (Section W U)) := inferInstance
  let : Module (ZMod 2) (Additive (Section W U)) := inferInstance
  obtain ⟨hn,he,e,τ₂,p,hseed,hp,hrows,hbound,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_tensor_rows_from_original_seed
    s hab h hH hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hQA hnA hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural
    hpoint hplane eU hcoords hUcard hu hgenerate
  let := hn
  let := he
  let Q₂ := V0 (Source.VH H V) V₂ ⧸
    (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)
  let : CommGroup Q₂ := inferInstance
  let : AddCommGroup (Additive Q₂) := inferInstance
  let : Module (ZMod 2) (Additive Q₂) := inferInstance
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (le_conjugateSpanBy V G₁)
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  obtain ⟨_,_,_,_,_,_,_,_,hprod,_,_⟩ := source_tensor_from_original_seed ds
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
  let S := conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)
  have hSU : S ≤ Source.UL L H V₃ := conjugateSpanBy_le h0U (h1L.trans q.normalized)
  have h0V := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2
    (T:Subgroup G) hK hG hV hgen s.seed_le
  have hSV : S ≤ Source.VH H V := conjugateSpanBy_le h0V
    ((le_sup_left.trans hH.1.2).trans (le_normalizer_conjugateSpanBy _ _))
  have hSB : S ≤ V0 (Source.VH H V) V₂ := hSV.trans (VH_le_V0 _ _)
  let D := conjugateSpanBy S (zpowers (g:G))
  have hgH : zpowers (g:G) ≤ L := zpowers_le.mpr hgL
  have hgJ : zpowers (g:G) ≤ G2 V₂ := zpowers_le.mpr (hAG g.property)
  have hDA : D ≤ Source.UL L H V₃ := conjugateSpanBy_le hSU (hgH.trans q.normalized)
  have hDB : D ≤ V0 (Source.VH H V) V₂ := conjugateSpanBy_le hSB (hgJ.trans p.normalized)
  have h0S : U0 (Source.UH H V₃) V₂ ≤ S := le_conjugateSpanBy _ _
  have hSD : S ≤ D := le_conjugateSpanBy _ _
  have h0D := h0S.trans hSD
  obtain ⟨f,hf⟩ := q.exists_image_quotient_comparison p D hDA hDB
  have hk := q.image_quotient_comparison_kernel p D hDA hDB f hf h0D
  refine ⟨hgL,U,W,hUm,hVW,hWU,hbin,τ,hirr,hfaith,hτ,hdegree,hcount,q,hk2,hc2,
    hn,he,e,τ₂,p,hseed,hp,hrows,ha,hDA,hDB,f,hf,hk,?_,?_,?_⟩
  · intro n w hw hz
    have h0n : (U0 (Source.UH H V₃) V₂).conjBy ((g:G)^n) = U0 (Source.UH H V₃) V₂ :=
      mem_normalizer_iff_map_conj_eq.mp
        (G2_normalizes_U0 _ _ ((G2 V₂).zpow_mem (hAG g.property) n))
    apply q.image_quotient_comparison_injective_on_slice p D hDA hDB f hf h0D
      (S.conjBy ((g:G)^n)) (h0n.ge.trans (map_mono h0S)) ?_ w hw hz
    rw [(hpowers n).1]
    exact hk2 ▸ inf_le_left
  · intro n w
    exact q.image_quotient_comparison_equivariant p D hDA hDB f hf
      ((⟨g,hgL⟩:L)^n) ((G2 V₂).zpow_mem (hAG g.property) n)
      (le_normalizer_conjugateSpanBy S (zpowers (g:G)) (zpow_mem_zpowers _ _))
      (G2_normalizes_U0 _ _ ((G2 V₂).zpow_mem (hAG g.property) n)) w
  · intro hc
    let : Finite (Additive (Section W U)) := inferInstance
    have hSfull : q.imageSpace S = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hs := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=q.imageSpace S)
      have ht := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (Section W U))
      rw [hc3,Nat.card_zmod] at hs
      rw [hc,Nat.card_zmod] at ht
      exact Nat.pow_right_injective (by decide : 1 < 2) (hs.symm.trans ht)
    have hDfull : q.imageSpace D = ⊤ := top_unique (hSfull ▸ q.imageSpace_mono hSD)
    refine ⟨q.image_quotient_comparison_surjective p D hDA hDB f hf hDfull,?_⟩
    have hh := (q.imageSpace (U0 (Source.UH H V₃) V₂)).card_eq_card_quotient_mul_card
    rw [hc,hc2] at hh
    omega

end CFSG.Quasithin.Chapter13.Section08.LinearFour
