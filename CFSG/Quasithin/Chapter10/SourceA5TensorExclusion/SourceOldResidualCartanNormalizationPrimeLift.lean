module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationNoncentral
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanTwoCore.Residual
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer
public import Theory.GroupTheory.LocalSolvableCoreNormalizerSylow

/-!
# Lifting prime-linear recognition to the original Cartan

Put N = N_G(V₁) and K₀ = N_J(T ∩ O_{2,2′,2}(J))^∞. Retain the literal
image of K₀ in N/O₂(N). An SL₂(p) marking of that image gives a surjection
from K₀ with two-group kernel. The original T normalizes J, hence K₀ and
its two-core. The latter lies in T, so the rank-one perfect-subgroup lift
proves that the original Cartan normalizes K = O²(H).

The completed catalogue and invariant-core construction supply every other
input in the nonzero-core branch. The final application proves the old
residual side of the original Cartan two-core equality. A separate theorem
shows that normalization of V₁ by K forces O₂(H∨A) to be nontrivial.

The actual-image SL₂ recognition remains an explicit mathematical premise.
It is not part of the invariant-core theorem and is not proved here.
The zero-core line argument remains a separate source input.

Source: Aschbacher--Smith, Proposition 9.3.1 and Lemma 9.3.2,
printed pp.732--733 of the combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
open Theory.GroupTheory.LocalSolvableCoreNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original residual image under the actual ambient two-core quotient. -/
@[expose] def cartanNormalizerResidualImage (J : Subgroup G) :
    Subgroup ((normalizer (m.tensorLine : Set G)) ⧸
      pCore 2 (normalizer (m.tensorLine : Set G))) :=
  ((localNormalizerResidual J
    ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype)).subgroupOf
      (normalizer (m.tensorLine : Set G))).map
        (QuotientGroup.mk' (pCore 2 (normalizer (m.tensorLine : Set G))))

/-- The remaining recognition statement specifies an actual group isomorphism. -/
@[expose] def CartanNormalizerResidualPrimeModel (J : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ 3 < p ∧
    Nonempty (m.cartanNormalizerResidualImage J ≃* SL(2,ZMod p))

/-- The literal image marking supplies rank-one normalization and its perfect lift. -/
theorem cartan_normalizes_old_residual_of_oddCore_image
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hB3 : Nat.card B = 3) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hKK : (pResidual 2 H).map H.subtype ≤
      localNormalizerResidual J ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype))
    (hAK : A ≤ normalizer (localNormalizerResidual J
      ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype) : Set G))
    (hmodel : m.CartanNormalizerResidualPrimeModel J) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  let N := normalizer (m.tensorLine : Set G)
  let K := (pResidual 2 H).map H.subtype
  let K0 := localNormalizerResidual J
    ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype)
  have hK0N : K0 ≤ N := ((map_subtype_le _).trans inf_le_left).trans hJU
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    m.tensorLine_normalized.trans ((normal_subgroupOf_iff_le_normalizer hJU).mp hnJ)
  have hQT : K0.pCoreIn 2 ≤ (T : Subgroup G) :=
    localNormalizerResidual_core_le_sylow T J hTJ (twoOddTwoCore J)
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect
    (source_hstar_residual_mem_local_of_a5 hH eK)
  obtain ⟨p,hp,hp3,⟨a⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' (pCore 2 N)
  let a' : (K0.subgroupOf N).map q ≃* SL(2,ZMod p) := a
  let b : K0.subgroupOf N ≃* K0 := subgroupOfEquivOfLe hK0N
  let g := a'.toMonoidHom.comp (q.subgroupMap (K0.subgroupOf N))
  let f := g.comp b.symm.toMonoidHom
  have hf : Function.Surjective f :=
    (a'.surjective.comp (q.subgroupMap_surjective _)).comp b.symm.surjective
  have hg : IsPGroup 2 g.ker := by
    dsimp only [g]
    rw [MonoidHom.ker_comp_of_injective (q.subgroupMap (K0.subgroupOf N))
      a'.toMonoidHom a'.injective, ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (g.ker.comap b.symm.toMonoidHom)
    exact hg.comap_of_injective b.symm.toMonoidHom b.symm.injective
  exact Theory.PSL2.cartan_normalizes_of_primeSL2_cover K K0 A B hKK hAK hBA hBK
    (hQT.trans (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))) hB3 hp3 f hf hk

/-- The nonzero-core source reduction, retaining only actual-image recognition. -/
theorem nonzero_core_cartan_normalizes_of_oddCore_images
    (hrecognition : ∀ (J : Subgroup G),
      J ≤ normalizer (m.tensorLine : Set G) →
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent →
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal →
      (let N := normalizer (m.tensorLine : Set G)
       let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
       ¬ fittingSubgroup I ≤ center I) →
      m.CartanNormalizerResidualPrimeModel J)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,_,_,_,_,_,_,_,_,hn,_,hKK,hAK⟩ :=
    m.nonzero_core_cartan_normalization_invariant_oddCore hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore
  · exact hAK
  let := hAe
  exact m.cartan_normalizes_old_residual_of_oddCore_image hH hlarge A B J
    hB3 (hBC ▸ inf_le_left) hBK hJU hnJ hKK hAK
    (hrecognition J hJU hJ hnJ hn)

/-- The nontrivial tensor line lies in the actual Cartan overgroup two-core. -/
theorem cartan_core_ne_bot_of_old_residual_normalizes_line
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hKN : (pResidual 2 H).map H.subtype ≤ normalizer (m.tensorLine : Set G)) :
    pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥ := by
  have hHN : H ≤ normalizer (m.tensorLine : Set G) := by
    rw [← source_hstar_residual_sup_sylow hH]
    exact sup_le hKN m.tensorLine_normalized
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hc : m.tensorLine ≤ (H ⊔ A).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 2) m.card_tensorLine)
      (m.tensorLine_le_sylow.trans (hTH.trans le_sup_left))
      (sup_le hHN (hAB.trans m.borel_normalizes_tensorLine))
  intro he
  rw [pCoreIn,he,Subgroup.map_bot] at hc
  exact m.tensorLine_ne_bot (le_bot_iff.mp hc)

/-- Connect a source line-normalization proof to the Cartan normalization branch. -/
theorem cartan_normalizes_of_line_and_oddCore_images
    (hrecognition : ∀ (J : Subgroup G),
      J ≤ normalizer (m.tensorLine : Set G) →
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent →
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal →
      (let N := normalizer (m.tensorLine : Set G)
       let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
       ¬ fittingSubgroup I ≤ center I) →
      m.CartanNormalizerResidualPrimeModel J)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hKN : (pResidual 2 H).map H.subtype ≤ normalizer (m.tensorLine : Set G)) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) :=
  m.nonzero_core_cartan_normalizes_of_oddCore_images hrecognition hH hlarge
    A B hAB hA9 hAe hB3 hBK hBC
      (m.cartan_core_ne_bot_of_old_residual_normalizes_line hH A hAB hKN)

/-- Apply the normalization lift to the literal old-residual equality of 9.3.2. -/
theorem source_cartan_twoCore_of_nonzero_core_and_oddCore_images
    (hrecognition : ∀ (J : Subgroup G),
      J ≤ normalizer (m.tensorLine : Set G) →
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent →
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal →
      (let N := normalizer (m.tensorLine : Set G)
       let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
       ¬ fittingSubgroup I ≤ center I) →
      m.CartanNormalizerResidualPrimeModel J)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    (A ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype) ⊔ (H ⊔ A).pCoreIn 2 := by
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  exact source_old_residual_cartan_twoCore D hH eK A B hAB
    (hBC ▸ inf_le_left) hBK hB3
    (m.nonzero_core_cartan_normalizes_of_oddCore_images hrecognition hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
