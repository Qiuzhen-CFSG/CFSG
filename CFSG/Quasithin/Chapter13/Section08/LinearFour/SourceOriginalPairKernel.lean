module
public import Theory.Representation.BinaryConjugationSection.PairKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalResidualSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondAction

/-!
# The paired-span kernel in the original maximal quotient

Write S = ⟨U₀^{L₁}⟩ and R = S^g, retaining the original residual g and
inverse-conjugation convention. The second binary section makes S and R
normal in their join. Their known indices 64, 64 and 16 over V give
|SR:V| = 256. The same selected maximal quotient gives
|SR ∩ W:V| times |image(SR)| = 256. Consequently an order-64 maximal
quotient forces a kernel of order four modulo V on SR, escaping both S
and R. In the second section that kernel image has order four and is
disjoint from each span image.

The original-input application constructs the second section and applies
this calculation to the already selected quotient. It preserves the
original g, every translated kernel, the degree alternatives and chief
bound. This identifies the precise extra kernel that the movement argument
must exclude; it does not prove projected movement or exclude order 64.
Both tensor rows are covered by the calculation. In particular no pure
second-factor scalar cubic is assumed, and V₀ itself need not be abelian.

Compatible movement, the nine-factor lower bound and the terminal
contradiction remain obligations of the linear-four owner. Earlier
13.8.27(b) remains with qt-d-138-six-g2-source and final source discharge
with qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29--30, printed p.964.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G W Z : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z]

/-- The join of two original spans has index 256 over V. If the selected
quotient has order 64, its kernel on this join has index four over V and
contains an element outside both spans. -/
theorem source_pair_kernel_of_order64
    (L UL N J B U S R V : Subgroup G)
    (ρ : Representation (ZMod 2) L W) (q : BinaryConjugationSection L UL N ρ)
    (σ : Representation (ZMod 2) J Z) (p : BinaryConjugationSection J B U σ)
    (hSL : S ≤ UL) (hRL : R ≤ UL) (hSB : S ≤ B) (hRB : R ≤ B)
    (hSR : S ⊓ R = U) (hSN : S ⊓ N = V) (hRN : R ⊓ N = V)
    (hcS : Nat.card (q.imageSpace S) = 64)
    (hcR : Nat.card (q.imageSpace R) = 64)
    (hcU : Nat.card (q.imageSpace U) = 16) :
    V.relIndex (S ⊔ R) = 256 ∧
      V.relIndex ((S ⊔ R) ⊓ N) * Nat.card (q.imageSpace (S ⊔ R)) = 256 ∧
      (Nat.card W = 64 →
        V.relIndex ((S ⊔ R) ⊓ N) = 4 ∧
        Nat.card (p.imageSpace ((S ⊔ R) ⊓ N)) = 4 ∧
        Disjoint (p.imageSpace S) (p.imageSpace ((S ⊔ R) ⊓ N)) ∧
        Disjoint (p.imageSpace R) (p.imageSpace ((S ⊔ R) ⊓ N)) ∧
        ∃ x ∈ (S ⊔ R) ⊓ N, x ∉ S ∧ x ∉ R) := by
  have hVS : V ≤ S := hSN ▸ inf_le_left
  have hVR : V ≤ R := hRN ▸ inf_le_left
  have hVN : V ≤ N := hSN ▸ inf_le_right
  have hUS : U ≤ S := hSR ▸ inf_le_left
  have hUN : U ⊓ N = V := by
    rw [←hSR,inf_right_comm,hSN,inf_eq_left.mpr hVR]
  have hiS : V.relIndex S = 64 := by
    rw [←hSN,inf_relIndex_left,←q.imageSpace_card_eq_relIndex S hSL,hcS]
  have hiR : V.relIndex R = 64 := by
    rw [←hRN,inf_relIndex_left,←q.imageSpace_card_eq_relIndex R hRL,hcR]
  have hiU : V.relIndex U = 16 := by
    rw [←hUN,inf_relIndex_left,←q.imageSpace_card_eq_relIndex U (hUS.trans hSL),hcU]
  have hi := p.pair_relativeIndex S R V hSB hRB hUS hVS hVR
  rw [hSR,hiU,hiS,hiR] at hi
  have hk := q.pair_kernel_index p S R V hSL hRL hSB hRB hUS hVS hVR hVN
  rw [hSR,hiU,hiS,hiR] at hk
  have hj : V.relIndex (S ⊔ R) = 256 := by omega
  have hk' : V.relIndex ((S ⊔ R) ⊓ N) * Nat.card (q.imageSpace (S ⊔ R)) = 256 := by omega
  refine ⟨hj,hk',?_⟩
  intro hW
  let : Finite W := Finite.of_surjective (fun x : UL => (q.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  have hlo := Nat.card_le_card_of_injective
    (Submodule.inclusion (q.imageSpace_mono (show S ≤ S ⊔ R from le_sup_left)))
    (Submodule.inclusion_injective _)
  have hhi := Nat.card_le_card_of_injective (q.imageSpace (S ⊔ R)).subtype
    (q.imageSpace (S ⊔ R)).subtype_injective
  rw [hcS] at hlo
  rw [hW] at hhi
  have hc : Nat.card (q.imageSpace (S ⊔ R)) = 64 := by omega
  rw [hc] at hk'
  have hk4 : V.relIndex ((S ⊔ R) ⊓ N) = 4 := by omega
  have hC : (S ⊔ R) ⊓ N ≤ B := inf_le_left.trans (sup_le hSB hRB)
  have hUC : U ⊓ ((S ⊔ R) ⊓ N) = V := by
    rw [←inf_assoc,inf_eq_left.mpr (hUS.trans le_sup_left),hUN]
  have hp4 : Nat.card (p.imageSpace ((S ⊔ R) ⊓ N)) = 4 := by
    rw [p.imageSpace_card_eq_relIndex _ hC,←inf_relIndex_right,hUC]
    exact hk4
  have hdis (D : Subgroup G) (hUD : U ≤ D) (hDN : D ⊓ N = V) :
      Disjoint (p.imageSpace D) (p.imageSpace ((S ⊔ R) ⊓ N)) := by
    apply Submodule.disjoint_def.mpr
    intro w hw hwc
    obtain ⟨x,hx,rfl⟩ := (p.mem_imageSpace_iff _ w).mp hwc
    have hxD := (p.coordinates_mem_imageSpace_iff_of_kernel_le D hUD x).mp hw
    have hxV : (x:G) ∈ V := hDN ▸ ⟨hxD,hx.2⟩
    have hVU : V ≤ U := hSR ▸ le_inf hVS hVR
    exact congrArg Multiplicative.toAdd ((p.coordinates_eq_one_iff x).mpr (hVU hxV))
  refine ⟨hk4,hp4,hdis S hUS hSN,hdis R (hSR ▸ inf_le_right) hRN,?_⟩
  have hnle : ¬ (S ⊔ R) ⊓ N ≤ V := by
    intro hh
    have h1 := relIndex_eq_one.mpr hh
    rw [hk4] at h1
    contradiction
  obtain ⟨x,hx,hxV⟩ := SetLike.not_le_iff_exists.mp hnle
  exact ⟨x,hx,fun hxs => hxV (hSN ▸ ⟨hxs,hx.2⟩),
    fun hxr => hxV (hRN ▸ ⟨hxr,hx.2⟩)⟩
end CFSG.Quasithin.Chapter13.Section08.LinearFour

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

open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]


/-- The original selected quotient retains the paired-span index and the exact
order-four kernel obstruction to projected movement. No quotient movement
or exclusion of order 64 is assumed. -/
theorem exists_source_original_pair_kernel
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
              (let S := conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)
               let R := S.conjBy ((g:G)⁻¹)
               V.relIndex (S ⊔ R) = 256 ∧
                 V.relIndex ((S ⊔ R) ⊓ W.val.map L.subtype) *
                   Nat.card (q.imageSpace (S ⊔ R)) = 256 ∧
                 (Nat.card (Additive (Section W U)) = 64 →
                   V.relIndex ((S ⊔ R) ⊓ W.val.map L.subtype) = 4 ∧
                   ∃ x ∈ (S ⊔ R) ⊓ W.val.map L.subtype, x ∉ S ∧ x ∉ R)) ∧
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
  obtain ⟨hgL,U,W,hUm,hVW,hWU,hcover,hbin,τ,hirr,hfaith,hτ,
      ⟨q,hk1,hk2,hk3,hc1,hc2,hc3,hSS,hmove,hpowers⟩,hdegree,hcount⟩ :=
    exists_source_original_residual_span_kernels s hab h hH hcentral hHeq
      A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hALT hVA hAG hπI
      hgen hdim g hg P hL2def hL2A hgL2 ρ d π₄ hker honto hnatural hpoint hplane
      eU hcoords hUcard hu hgenerate hF hDH eL
  let := hbin
  obtain ⟨hn,he,τ₂,p,_,_,_,_,_⟩ := source_second_action_from_original_seed
    s hab h hH hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hQA hnA hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural
    hpoint hplane eU hcoords hUcard hu hgenerate
  let := hn
  let := he
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
  let R := S.conjBy ((g:G)⁻¹)
  have hSU : S ≤ Source.UL L H V₃ := conjugateSpanBy_le h0U (h1L.trans q.normalized)
  have hRU : R ≤ Source.UL L H V₃ := (map_mono hSU).trans
    (mem_normalizer_iff_map_conj_eq.mp (q.normalized (L.inv_mem hgL))).le
  have h0V := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2
    (T:Subgroup G) hK hG hV hgen s.seed_le
  have hSV : S ≤ Source.VH H V := conjugateSpanBy_le h0V
    ((le_sup_left.trans hH.1.2).trans (le_normalizer_conjugateSpanBy _ _))
  have hSB : S ≤ V0 (Source.VH H V) V₂ := hSV.trans (VH_le_V0 _ _)
  have hRB : R ≤ V0 (Source.VH H V) V₂ := (map_mono hSB).trans
    (mem_normalizer_iff_map_conj_eq.mp
      (p.normalized ((G2 V₂).inv_mem (hAG g.property)))).le
  have hRN : R ⊓ W.val.map L.subtype = V := by
    simpa only [zpow_neg_one] using (hpowers (-1)).1
  have hcR : Nat.card (q.imageSpace R) = 64 := by
    simpa only [zpow_neg_one] using (hpowers (-1)).2.2
  have hpair := source_pair_kernel_of_order64 L (Source.UL L H V₃)
    (W.val.map L.subtype) (G2 V₂) (V0 (Source.VH H V) V₂)
    (U0 (Source.UH H V₃) V₂) S R V
    (τ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) q (τ₂.comp π) p
    hSU hRU hSB hRB hSS hk3 hRN hc3 hcR hc2
  exact ⟨hgL,U,W,hUm,hVW,hWU,hcover,hbin,τ,hirr,hfaith,hτ,
    ⟨q,hk1,hk2,hk3,hc1,hc2,hc3,hSS,hmove,
      ⟨hpair.1,hpair.2.1,fun hc => ⟨(hpair.2.2 hc).1,(hpair.2.2 hc).2.2.2.2⟩⟩,
      hpowers⟩,hdegree,hcount⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
