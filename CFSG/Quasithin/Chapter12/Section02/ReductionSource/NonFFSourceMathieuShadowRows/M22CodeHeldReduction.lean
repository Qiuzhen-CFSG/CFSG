module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeSixSection
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeM11Wreath

/-!
# Only Held remains in the original inside-core component sieve

The original parabolic has full two-core quotient S₃ wr C₂. Its actual
two-residual lies in the same normal component as the original A₆
point residual. If that component's full two-core quotient were M₁₁,
the original Sylow and elementary-nine residual would give the forbidden
M₁₁ image of CodeM11Wreath. Restriction to the involution centralizer and
both original subgroup quotient markings are kept explicit.

Combining this with the binary-linear exclusions leaves Held on the same
original component. The projective A₆ residual and its possible covering
center remain. This is a reduction under hcore: the Held comparison,
removal of hcore, later M22-code exclusion and final same-orbit M24-cocode
selection remain unproved.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, refs/quasithin.pdf,
retaining the additional Held case of the adequate 1.3.4 interface.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.MathieuShadowRows Chapter1 Chapter1.XiEmbedding
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original full wreath quotient excludes the M₁₁ containing component. -/
theorem sourceOrbit_m22_code_inside_core_not_m11
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    {z : G} (hHC : H ≤ centralizer ({z} : Set G))
    {K : Subgroup G} (hK : K ∈ cComponentsIn (centralizer ({z} : Set G)))
    (hnK : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hXK : (pResidual 2 H).map H.subtype ≤ K)
    (eK : XiQuotient K ≃* M11) : False := by
  obtain ⟨_,_,⟨eH⟩⟩ := D.sourceOrbit_m22_code_inside_core_wreath h hmany hV hnon d hH hcore
  let w := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  let C := centralizer ({z} : Set G)
  let S := T.subtype (hH.1.1.2.trans hHC)
  let A := H.subgroupOf C
  let B := K.subgroupOf C
  let : B.Normal := normal_subgroupOf_of_le_normalizer hnK
  let a : A ≃* H := subgroupOfEquivOfLe hHC
  let b : B ≃* K := subgroupOfEquivOfLe hK.1
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hXB : (pResidual 2 A).map A.subtype ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    have hh : a x ∈ pResidual 2 H := by
      have hm := mem_map_of_mem a.toMonoidHom hx
      rwa [map_pResidual_of_surjective 2 a.toMonoidHom a.surjective] at hm
    exact hXK (mem_map_of_mem H.subtype hh)
  exact no_wreath_residual_in_normal_m11_component S A B (comap_mono hH.1.1.2)
    hK.2 hXB (bq.trans eK) (aq.trans (eH.trans w.symm))

/-- The only remaining inside-core component is Held, on the same original involution and A₆ projective residual. Its smaller covering center remains explicit. -/
theorem sourceOrbit_m22_code_inside_core_held_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P K : Subgroup G,
        LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)) ∧
        localResidual L z ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (XiQuotient K) ∧ center (XiQuotient K) = ⊥ ∧
        X ≤ K ∧ Nonempty (P ≃* Plane 3) ∧
        Nonempty (XiQuotient K ≃* Held.He) ∧
        IsQuasisimple (XiQuotient (localResidual L z)) ∧
        Nonempty ((XiQuotient (localResidual L z) ⧸
          center (XiQuotient (localResidual L z))) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,hm⟩ :=
    D.sourceOrbit_m22_code_inside_core_m11_or_held h hmany hV hnon d hH hcore
  have he := hm.resolve_left (fun hh => D.sourceOrbit_m22_code_inside_core_not_m11
    h hmany hV hnon d hH hcore hHC hK hnK hXK hh.1.some)
  have hz : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hHC (hH.1.1.2 ht))
  obtain ⟨hr,er⟩ := D.sourceOrbit_m22_code_centralizer_projective h.toHypothesis1221 d z hz hne
  exact ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,he,hr,er⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
