module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalSecondComparison
public import Theory.Representation.BinaryConjugationSection.IntersectionComparison

/-!
# The original relative plane actors on the common quotient

The canonical intersection U_L ∩ V₀ is preserved by every element of
L ∩ G₂. The first kernel is L-normal, so its intersection with this domain
also has invariant second image. Compare the two original section maps on
this whole domain. This gives an intertwiner for all these actors, retaining
both tensor rows, the marked V_H/U₀ slice and the original conjugator.
It extends the preceding comparison on the cyclic span of S = ⟨U₀^{L₁}⟩.

For an order-64 maximal quotient the map is surjective onto an order-four
quotient; its invariant kernel has index four in the whole intersection
image, and is disjoint from every original-g translate of the marked
S-slice. These properties do not yet exclude that quotient, particularly
in the extra-line row. The remaining ambient exclusion, nine-factor bound
and terminal contradiction stay with the linear-four owner. No additional
normalization or movement hypothesis is imposed.

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

private theorem subspace_card_of_surjective
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (D N : Submodule (ZMod 2) X) (hND : N ≤ D)
    (f : D →ₗ[ZMod 2] Y) (hk : f.ker = N.comap D.subtype)
    (hs : Function.Surjective f) : Nat.card D = Nat.card Y * Nat.card N := by
  have hh := f.ker.card_eq_card_quotient_mul_card
  have hquot := Nat.card_congr (f.quotKerEquivOfSurjective hs).toEquiv
  rw [hquot,hk] at hh
  have hkc := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hND).toEquiv
  exact hh.trans ((congrArg (· * Nat.card Y) hkc).trans (Nat.mul_comm _ _))

/-- Construct the common quotient on the full intersection U_L ∩ V₀,
with the action of every original actor in L ∩ G₂. Both complete second
tensor rows and injectivity on every original-g slice are retained. -/
theorem exists_source_original_plane_comparison
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
    ∃ _hgL : (g:G) ∈ L, ∃ U W : NormalNode L,
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
                let D := Source.UL L H V₃ ⊓ V0 (Source.VH H V) V₂
                let E := q.imageSpace (U0 (Source.UH H V₃) V₂)
                ∃ (hDA : D ≤ Source.UL L H V₃) (hDB : D ≤ V0 (Source.VH H V) V₂),
                ∃ f : (q.intersectionSubrepresentation p).toRepresentation.IntertwiningMap
                    (q.otherKernelSubrepresentation p).quotientRepresentation,
                  (∀ x : D, f ⟨(p.coordinates (inclusion hDB x)).toAdd,
                    (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB x,x.property,rfl⟩⟩ =
                      E.mkQ (q.coordinates (inclusion hDA x)).toAdd) ∧
                  LinearMap.ker f.toLinearMap = (p.imageSpace (D ⊓ W.val.map L.subtype)).comap
                    (p.imageSpace D).subtype ∧
                  (∀ (n : ℤ) (w : p.imageSpace D),
                    w.val ∈ p.imageSpace (S.conjBy ((g:G)^n)) → f w = 0 → w = 0) ∧
                  (Nat.card (Additive (Section W U)) = 64 →
                    Function.Surjective f ∧ Nat.card (Additive (Section W U) ⧸ E) = 4 ∧
                    Nat.card (p.imageSpace D) =
                      4 * Nat.card (p.imageSpace (D ⊓ W.val.map L.subtype))) := by
  obtain ⟨hgL,U,W,hUm,hVW,hWU,hbin,τ,hirr,hfaith,hτ,hdegree,hcount,q,hk2,hc2,
      hn,he,e,τ₂,p,hseed,hp,hrows,ha,hCA,hCB,f,hf,hk,hinj,hact,hsurj⟩ :=
    exists_source_original_second_comparison s hab h hH hcentral hHeq
      A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA
      hALT hVA hAG hπI hgen hdim g hg P hL2def hL2A hgL2 ρ d π₄ hker honto hnatural
      hpoint hplane eU hcoords hUcard hu hgenerate hF hDH eL
  let := hbin
  let : CommGroup (Section W U) := inferInstance
  let : AddCommGroup (Additive (Section W U)) := inferInstance
  let : Module (ZMod 2) (Additive (Section W U)) := inferInstance
  let := hn
  let := he
  let Q₂ := V0 (Source.VH H V) V₂ ⧸
    (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)
  let : CommGroup Q₂ := inferInstance
  let : AddCommGroup (Additive Q₂) := inferInstance
  let : Module (ZMod 2) (Additive Q₂) := inferInstance
  let S := conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)
  let C := conjugateSpanBy S (zpowers (g:G))
  let D := Source.UL L H V₃ ⊓ V0 (Source.VH H V) V₂
  have hCD : C ≤ D := le_inf hCA hCB
  have h0C : U0 (Source.UH H V₃) V₂ ≤ C :=
    (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  obtain ⟨F,hFcoord,hFker,hFsurj⟩ := q.exists_intersection_intertwiner p (h0C.trans hCA)
  let i : p.imageSpace C →ₗ[ZMod 2] p.imageSpace D :=
    Submodule.inclusion (p.imageSpace_mono hCD)
  have hi (w : p.imageSpace C) : F (i w) = f w :=
    q.intersection_comparison_restrict p C hCA hCB f hf F.toLinearMap hFcoord w
  refine ⟨hgL,U,W,hUm,hVW,hWU,hbin,τ,hirr,hfaith,hτ,hdegree,hcount,q,hk2,hc2,
    hn,he,e,τ₂,p,hseed,hp,hrows,ha,inf_le_left,inf_le_right,F,hFcoord,hFker,?_,?_⟩
  · intro n w hw hz
    have hnC : (g:G)^n ∈ normalizer C :=
      le_normalizer_conjugateSpanBy S (zpowers (g:G)) (zpow_mem_zpowers _ _)
    have hSnC : S.conjBy ((g:G)^n) ≤ C :=
      (map_mono (le_conjugateSpanBy S (zpowers (g:G)))).trans
        (mem_normalizer_iff_map_conj_eq.mp hnC).le
    let wC : p.imageSpace C := ⟨w.val,p.imageSpace_mono hSnC hw⟩
    have hw' : i wC = w := Subtype.ext rfl
    have hz' : f wC = 0 := (hi wC).symm.trans (hw' ▸ hz)
    apply Subtype.ext
    exact congrArg (fun v : p.imageSpace C => v.val) (hinj n wC hw hz')
  · intro hc
    obtain ⟨hs,hfour⟩ := hsurj hc
    have hfs : Function.Surjective F := fun w => by
      obtain ⟨v,hv⟩ := hs w
      exact ⟨i v,(hi v).trans hv⟩
    refine ⟨hfs,hfour,?_⟩
    have hh := subspace_card_of_surjective (p.imageSpace D)
      (p.imageSpace (D ⊓ W.val.map L.subtype)) (p.imageSpace_mono inf_le_left)
      F.toLinearMap hFker hfs
    exact hh.trans (congrArg (· * Nat.card (p.imageSpace (D ⊓ W.val.map L.subtype))) hfour)

end CFSG.Quasithin.Chapter13.Section08.LinearFour
