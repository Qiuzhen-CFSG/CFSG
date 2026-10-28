module
public import Theory.Representation.BinaryParabolicExteriorSquare.ComplementCore
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ComplementObstruction
public import Theory.GroupTheory.NoncentralChiefRefinement.OneNoncentralLayer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceCriticalGeometry

/-!
# Chief accounting in the original complementary-plane coordinates

The local image fixes the marked natural plane and rotates its complement.
It determines the actual two-core, radical action and quotient of order
three. Normality constructs the literal intersection strata. The common
cubic gives their counts 1, 2, 1 and 2, so a complete nine-factor lower
bound leaves at least three factors on the original H_C/V_H intersection.

The original-seed application constructs the exterior and dual sections,
then feeds this lower bound into the critical geometry and terminal
contradiction. The full H_C/V_H is not assumed elementary abelian.
The nine-factor bound and identification of the original local image
remain source obligations; these conditional results do not establish
13.8.28. Earlier 13.8.27(3) retains its existing producer.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.30--32, printed pp.964--966, and Notation 13.2.1 on p.877.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- The local matrix image identifies the actual radical, its kernel containment,
and its odd terminal quotient in the original ambient group. -/
theorem source_complement_matrix_twoCore
    (H D QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (himage : (D.subgroupOf H).map π = PlaneRadical.complementLocal) :
    ((D.pCoreIn 2).subgroupOf H).map π = PlaneRadical.radical ∧
      QH ⊓ D ≤ D.pCoreIn 2 ∧ Nat.card (D ⧸ pCore 2 D) = 3 ∧
      HasNoTwoChiefFactors (D ⧸ pCore 2 D) := by
  let πD := π.comp (inclusion hDH)
  have hk : πD.ker = QH.subgroupOf D := by
    ext x
    change inclusion hDH x ∈ π.ker ↔ (x:G) ∈ QH
    rw [hker]
    rfl
  have hp : IsPGroup 2 πD.ker := by rw [hk]; exact hQH.comap_subtype
  have hr : πD.range = PlaneRadical.complementLocal := by
    rw [←himage]
    ext x
    constructor
    · rintro ⟨d,rfl⟩
      exact mem_map_of_mem π d.property
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
  obtain ⟨hm,hcard⟩ := PlaneRadical.lifted_complement_twoCore πD hp hr
  have hmodel : ((D.pCoreIn 2).subgroupOf H).map π = (pCore 2 D).map πD := by
    ext x
    constructor
    · rintro ⟨r,⟨s,hs,he⟩,rfl⟩
      refine ⟨s,hs,?_⟩
      have hh : inclusion hDH s = r := Subtype.ext he
      change π (inclusion hDH s) = π r
      rw [hh]
    · rintro ⟨s,hs,rfl⟩
      exact ⟨inclusion hDH s,mem_map_of_mem D.subtype hs,rfl⟩
  refine ⟨hmodel.trans hm,?_,hcard,?_⟩
  · intro x hx
    have hcore : πD.ker ≤ pCore 2 D := le_sSup ⟨inferInstance,hp⟩
    have hxk : (⟨x,hx.2⟩ : D) ∈ πD.ker := by rw [hk]; exact hx.1
    exact mem_map_of_mem D.subtype (hcore hxk)
  · let : IsSimpleGroup (D ⧸ pCore 2 D) := isSimpleGroup_of_prime_card hcard
    apply noTwoChiefFactors_of_simple
    intro hp2
    have hh := hp2.card_eq_or_dvd
    rw [hcard] at hh
    norm_num at hh

/-- The compatible local image supplies all surrounding chief strata,
their actual two-core and the same complementary cubic. -/
theorem source_three_factors_of_complement_local_image
    (H D UH V1 VH HC QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH) (hVC : VH ≤ HC)
    (hQHD : QH ≤ normalizer (D : Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (ddual : BinaryConjugationSection H QH HC ρ.dual)
    (ξ : Representation (ZMod 2) H PlaneSpan.Six)
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h v, ρ h v = Matrix.mulVec (π h).val v)
    (hexterior : ∀ h v, ξ h v = exteriorMap (π h).val v)
    (himage : (D.subgroupOf H).map π = PlaneRadical.complementLocal)
    (hcentral : D ≤ centralizer (V1 : Set G))
    (hnine : ∀ t : ChiefSeries D, t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (s : ChiefSeries D) (hs0 : s.head.val = VH.subgroupOf D)
    (hs1 : s.last.val = HC.subgroupOf D) : 3 ≤ s.noncentralTwoCount := by
  let Z : NormalNode D := ⟨V1.subgroupOf D,normal_subgroupOf_of_le_normalizer
    (hDH.trans ((normal_subgroupOf_iff_le_normalizer
      (d.kernel_le.trans d.section_le)).mp d.kernel_normal_actor))⟩
  let U : NormalNode D := ⟨UH.subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans d.normalized)⟩
  let V : NormalNode D := ⟨VH.subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans dexterior.normalized)⟩
  let C : NormalNode D := ⟨HC.subgroupOf D,normal_subgroupOf_of_le_normalizer
    (hDH.trans ((normal_subgroupOf_iff_le_normalizer
      (ddual.kernel_le.trans ddual.section_le)).mp ddual.kernel_normal_actor))⟩
  let Q : NormalNode D := ⟨QH.subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans ddual.normalized)⟩
  let R : NormalNode D := ⟨pCore 2 D,(show (pCore 2 D).Normal from inferInstance)⟩
  have hRcore : R.val = pCore 2 D := rfl
  have hZ : IsCentral ⊥ Z := by
    rw [isCentral_iff_commutator_le,commutator_le]
    intro a _ b hb
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (hcentral a.property (b:G) hb).symm)
  obtain ⟨hradical,hQR,hcard,hterm⟩ := source_complement_matrix_twoCore H D QH hDH hQH π hker himage
  have hRdef : R.val = (D.pCoreIn 2).subgroupOf D := by
    rw [hRcore]
    exact (comap_map_eq_self_of_injective D.subtype_injective (pCore 2 D)).symm
  have hterminal : HasNoTwoChiefFactors (D ⧸ R.val) := by
    exact hterm.of_equiv (QuotientGroup.quotientMulEquivOfEq hRcore)
  have hcubic : complementElement ∈ (D.subgroupOf H).map π := by
    rw [himage]
    exact (show zpowers complementElement ≤ PlaneRadical.complementLocal from le_sup_right)
      (mem_zpowers complementElement)
  let f := QuotientGroup.mk' (pCore 2 D)
  have hp : IsPGroup 2 f.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hX : Nat.card (⊤ : Subgroup (D ⧸ pCore 2 D)) = 3 := by
    rw [card_top,hcard]
  have hq : IsPGroup 2 ((D ⧸ pCore 2 D) ⧸ (⊤ : Subgroup (D ⧸ pCore 2 D))) :=
    IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨A,hAD,a,hA,ha,hmat⟩ :=
    source_common_complement_cubic H D QH hDH hQH π hker hcubic
  have hAc : Nat.card (A.subgroupOf D) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv).trans hA
  have hAX := cubic_image_eq_normal_three f hp (A.subgroupOf D) hAc ⊤ hX hq
  have hDR : D ≤ normalizer (D.pCoreIn 2 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 D)).mp (by
      rw [←hRdef]
      exact R.property)
  obtain ⟨τ,dradical,hcoordinates,_⟩ := PlaneRadical.exists_section
    H D (D.pCoreIn 2) QH hDH (pCoreIn_le 2 D) hDR hQR π hker hradical
  exact source_three_factors_of_complement_sections
    H D UH V1 VH HC QH A hDH hAD hA hQH hVC hQHD ρ d ddual ξ dexterior
    a ha (fun v => (hnatural _ v).trans (by rw [hmat]))
    (fun v => (hexterior _ v).trans (by rw [hmat]))
    f (QuotientGroup.mk'_surjective _) hp ⊤ hX hq hAX Z U V C Q R
    rfl rfl rfl rfl rfl hZ hterminal (D.pCoreIn 2) hRdef (isPGroup_pCoreIn 2 D)
    τ dradical (section_complement_action H D (D.pCoreIn 2) (QH ⊓ D)
      hDH (pCoreIn_le 2 D) π τ dradical hcoordinates (inclusion hAD a) hmat)
    hnine s (Subtype.ext hs0) (Subtype.ext hs1)

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryLinear.OuterCyclic CriticalGeometry
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare SingularPresentation
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {G : Type*} [Group G] [Finite G]
variable {K U : Type*} [Group K]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The literal L₀ nine-factor bound and its complementary-plane image
supply the three-factor premise of the original terminal consumer.
The exterior, dual, radical and chief-stratum markings are constructed. -/
theorem source_linear_four_exclusion_from_original_nine_factors
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
    (c : CriticalPair L (T:Subgroup G) H V) (hb : 3 ≤ c.path.length)
    (Kc : Subgroup G) (hKcH : Kc ≤ H) (hKc : IsPPerfect 2 Kc)
    (hseedQ : ⁅V₃,Source.QH H⁆ ≠ ⊥)
    (hseed : ⁅centralizer (V₃:Set G),V⁆ ≤ V₁)
    (hcaseone : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∨
        Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃) →
      c.Aone V₁ ≤ Source.UH H V₃ ∧ ¬ c.Vgamma ≤ Source.QH H)
    (hDK : zero L ≤ Kc)
    (hlocal : ((zero L).subgroupOf H).map π₄ = PlaneRadical.complementLocal)
    (hnine : ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (Q R : Subgroup G) (hQR : Source.QH H ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ Source.QH H ≤ centralizer (V₃:Set G))
    (hQV : Q ≤ centralizer (V:Set G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (Kc.subgroupOf H).subtype)) : False := by
  let F := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  let : IsElementaryAbelian 2 (Source.VH F.H F.V) := inferInstanceAs
    (IsElementaryAbelian 2 (Source.VH H V))
  obtain ⟨p₆,_,_,_,_,_⟩ := source_exterior_geometry_from_original_seed s hab h hH hcentral hHeq
    A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hALT hVA hAG hπI
    hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  have hVC : Source.VH H V ≤ Source.HC H V₃ := le_inf p₆.section_le
    ((commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative (Source.VH H V)))).trans (centralizer_le p₆.kernel_le))
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) :=
    IsElementaryAbelian.of_le p₆.kernel_le
  obtain ⟨ddual,_⟩ := source_natural_core_duality F hF ρ d π₄ hker honto hnatural hseedQ
  let D := zero L
  have hDH : D ≤ H := hDK.trans hKcH
  have hQHD : Source.QH H ≤ normalizer (D:Set G) :=
    hF.QH_le_T.trans (ds.normalizes_L.trans (normalizer_le_zero_normalizer L))
  let Vn : NormalNode D := ⟨(Source.VH H V).subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans p₆.normalized)⟩
  let Cn : NormalNode D := ⟨(Source.HC H V₃).subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans
      ((normal_subgroupOf_iff_le_normalizer
        (ddual.kernel_le.trans ddual.section_le)).mp ddual.kernel_normal_actor))⟩
  have hthree (t : ChiefSeries D) (ht0 : t.head = Vn) (ht1 : t.last = Cn) :
      3 ≤ t.noncentralTwoCount := by
    apply source_three_factors_of_complement_local_image H D (Source.UH H V₃) V₁
      (Source.VH H V) (Source.HC H V₃) (Source.QH H) hDH (isPGroup_pCoreIn 2 H)
      hVC hQHD ρ d ddual (action π₄) p₆ π₄ hker hnatural (fun _ _ => rfl)
      hlocal (hDH.trans hF.H_centralizes) hnine t
    · exact congrArg Subtype.val ht0
    · exact congrArg Subtype.val ht1
  exact source_linear_four_exclusion_from_original_tensor_seed
    s hab h hH hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural hpoint
    hplane eU hcoords hUcard hu hgenerate hF c hb Kc hKcH hKc hseedQ hseed hcaseone
    D hDK Vn Cn rfl rfl hthree Q R hQR hindex hcent hQV hcover hKonto

end CFSG.Quasithin.Chapter13.Section08.LinearFour
