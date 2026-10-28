module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Rigidity
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Reduction of an escaping characteristic normalizer to the marked five case

Let X = Ξ_p(L), R = O₂(XT), Y = N_L(R)^∞, and N = N_G(C), where
1 ≠ C char R. Genuine uniqueness for LT first gives N_G(L) = N_G(X).
The local embedding theorem constructs the containing C-component K, normal
in N. Its odd-core structure makes X nonnormal in K and excludes containment
in its solvable radical. The complete A.3.12 elimination therefore leaves
case (10). The actual SL₂(r) quotient of L and the nilpotent alternative
force p = r = 5; the residual comparison gives Y = N_L(C)^∞.

The conclusion preserves every chosen Sylow p-subgroup of X. Its images in
both N/O₂(N) and K/O₂(K) are elementary of order 25 and are the specified
kernels with quotient SL₂(5). No identification with a root plane is assumed.

The residual conclusions and the preceding radical-structure reductions are
explicit inputs. The only classification parameters are the full universal
A.3.6, A.3.8 and A.3.12 statements. The parent characteristic-normalizer proof
supplies these inputs and combines this reduction with the Thompson witness
and the independent marked parabolic-recognition theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed pp.512–513; A.3.12, printed pp.47–48.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
open Section02 Section02.LocalModels FiveCase
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine uniqueness of LT controls the two-core normalizer, and hence
the normalizer of X. The nontrivial two-core is a radical-structure input. -/
theorem normalizer_eq_of_LT_uniqueness (p : ℕ) (L T : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hcore : (XiP p L).pCoreIn 2 ≠ ⊥)
    (hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M → L ⊔ T ≤ M →
      M = normalizer (L : Set G)) :
    normalizer (L : Set G) = normalizer (XiP p L : Set G) := by
  have hNX := normalizer_le_normalizer_XiP p L
  have hXC : normalizer (XiP p L : Set G) ≤
      normalizer ((XiP p L).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (XiP p L) (pCore 2 (XiP p L))
  have hCM := normalizer_le_of_unique_maximalTwoLocal hunique
    (isPGroup_pCoreIn 2 (XiP p L)) hcore
    ((sup_le L.le_normalizer hTL).trans (hNX.trans hXC))
  exact le_antisymm hNX (hXC.trans hCM)

/-- The complete escaping-normalizer reduction on p.513. No containing
component, rigidity implication, selected alternative, prime identification,
residual equality, or marked extension is assumed. The source residual and
radical-structure inputs precede this reduction in the proof of 1.3.8. -/
theorem exists_marked_five_component
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → A36Conclusion B)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ (S : Sylow 2 A) (B : Subgroup A),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hA38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set A)).index = 2 ∧ NonnormalCComponentModel B)
    (p r : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hr : r.Prime)
    (L : Subgroup G) (T : Sylow 2 G)
    (hL : L ∈ LStar G T) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M → L ⊔ T ≤ M →
      M = normalizer (L : Set G))
    (hX : XiMember T (XiP p L))
    (hcore : (XiP p L).pCoreIn 2 ≠ ⊥)
    (hshape : XiOddQuotient p (XiQuotient (XiP p L)))
    (hfit : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hnil : A36Nilpotent (XiQuotient L))
    (hrmodel : IsSL (fittingQuotient L) 2 r)
    (hsecond : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hY : ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent)
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hYq : ¬ IsQuasisimple (XiQuotient (normalizerResidual L (radicalCore p L T))))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (hLC : normalizerResidual L (C.map (radicalCore p L T).subtype) ∈ Chapter1.L G T)
    (hcomm : ⁅normalizerResidual L (C.map (radicalCore p L T).subtype),
      normalizerResidual L (radicalCore p L T)⁆ =
        normalizerResidual L (C.map (radicalCore p L T).subtype))
    (hescape : ¬ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
      normalizer (L : Set G)) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let Y := normalizerResidual L (radicalCore p L T)
    let LC := normalizerResidual L (C.map (radicalCore p L T).subtype)
    normalizer (L : Set G) = normalizer (XiP p L : Set G) ∧
    ∃ K : Subgroup G, K ∈ cComponentsIn N ∧ Y ≤ K ∧
      (∀ D : Subgroup G, D ∈ cComponentsIn N → Y ≤ D → D = K) ∧
      (K.subgroupOf N).Normal ∧ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LC ≤ K ∧ ¬ ((XiP p L).subgroupOf K).Normal ∧
      ¬ XiP p L ≤ (solvableRadical K).map K.subtype ∧ Y < K ∧
      CaseTen (quotientImage Y N) (quotientImage K N) 5 ∧
      p = 5 ∧ r = 5 ∧
      Nonempty (XiQuotient K ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5)) ∧
      Y = LC ∧
      (∀ q : ℕ, q.Prime → Odd q →
        (q ∣ Nat.card (fittingSubgroup (XiQuotient LC)) ↔ q = 5)) ∧
      ∀ P : Sylow p (XiP p L),
        let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
        MarkedFiveExtension (quotientImage Y K) (quotientImage P₀ K) ∧
        MarkedFiveExtension (quotientImage Y N) (quotientImage P₀ N) ∧
        ∀ (U : Subgroup (quotientImage Y N)) [U.Normal],
          ElementaryModel 5 2 U →
          (quotientImage Y N ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) →
          (quotientImage P₀ N).subgroupOf (quotientImage Y N) = U := by
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hM := normalizer_eq_of_LT_uniqueness p L T hTL hcore hunique
  obtain ⟨K, hK, hYK, hu, hn, hTK, he, hXn, hXrad, hstrict⟩ :=
    exists_rigid_component hG hA36 hA312 hA38 hp3 L T hL hTL hX hshape
      hY hXY C hC hM hescape
  have hYL := Y_mem_L_of_cComponent p hL.1 hY
  obtain ⟨s, hs, _, hs3, hsmall, hlarge⟩ :=
    Alternatives.exists_case_ten hG hA36 p hp ho L T C hC K hK hstrict hYL
      hXY hYq hXrad he
  have hdata : SourceData 𝒦 p r L T C K :=
    { ambient := hG
      prime := hp
      large := hp3
      prime_r := hr
      maximal := hL
      invariant := hTL
      xi := hX
      xi_shape := hshape
      fitting_prime := hfit
      nilpotent := hnil
      quotient_r := hrmodel
      second_prime := hsecond
      characteristic := inferInstance
      nontrivial := hC
      normalizers := hM
      escape := hescape
      contains_xi := hXY
      local_Y := hYL
      nonsimple_Y := hYq
      local_LC := hLC
      commutator := hcomm
      component := hK
      contains_Y := hYK
      normal := hn
      nonnormal_xi := hXn
      radical_exclusion := hXrad }
  have hcase : CaseTen
      (quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) s :=
    ⟨hs, hs3, hsmall, hlarge⟩
  obtain ⟨hp5, hs5, hr5, hmodel, heq, hsupport, hmark⟩ :=
    hdata.caseTen_deduction hA36 hcase
  subst s
  refine ⟨hM, K, hK, hYK, hu, hn, hTK,
    residual_le_component L _ K C hK.1 hn hYK hcomm,
    hXn, hXrad, hstrict, hcase, hp5, hr5, hmodel, heq, hsupport, ?_⟩
  intro P
  refine ⟨hmark P, ?_, ?_⟩
  · exact (markedFiveExtension_componentQuotient_iff hYK
      ((map_subtype_le _).trans (hXY.trans hYK)) hK.1 hK.2).mp (hmark P)
  · intro U hU hmodel e
    exact hdata.caseTen_sylow_image_eq_kernel hcase P U hmodel e

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
