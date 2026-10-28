module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Closure
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetCoreFactors
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.Mathieu.M24.TwoLocalExtensions
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointClosure
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original cocode core factor and fixed subgroup modulo the central line

The original O₂(L_z)/V is marked by the native hexacode translation action.
The full perfect sextet residual acts irreducibly on it, retaining the cubic
center of 3.A₆. Thus every L_z-invariant subgroup between V and O₂(L_z) is
an endpoint of this interval.

For the original V, the subgroup fixed by O₂(L_z) modulo ⟨z⟩ is exactly V_z.
It is invariant under L_z and contains V_z. Irreducibility of V/V_z leaves
only V_z or V; the latter contradicts [V,O₂(L_z)]=V_z>⟨z⟩.

The native sign quotient determines the full O₂(L_z T) image through the
original action map. Its entire kernel is O₂(LT), so the lifted identity is
O₂(L_z T)=O₂(L_z)O₂(LT). In particular the original centralizer core and
normal closure lie in this product. These discharge the dual interval,
local-core containment and module fixed-subgroup inputs of 8.2.12.

The crossing of the selected pair, the whole LT-core intersection, extraspecial
structure, earlier whole-cocode marking, remaining Mathieu branches and ambient
J4 recognition remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher–Smith 8.2.11(4)–12, printed p.722, refs/quasithin.pdf.
The imported native calculations retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers.CoordinateTransport
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Stellmacher
open Chapter8.Section02.Centralizer
set_option backward.isDefEq.respectTransparency false
/-- A proper next commutator and an irreducible top factor determine the
fixed subgroup modulo the retained central line. -/
private theorem fixed_modulo_line {G M : Type*} [Group G] [AddCommGroup M] [Module (ZMod 2) M]
    (R X V W Z : Subgroup G) (ρ : Representation (ZMod 2) R M)
    [IsIrreducible ρ] (d : BinaryConjugationSection R V W ρ)
    (hXR : X ≤ R) (hRX : R ≤ normalizer (X : Set G))
    (hZR : R ≤ normalizer (Z : Set G)) (hZW : Z < W)
    (hVW : ⁅V,X⁆ = W) (hWZ : ⁅W,X⁆ ≤ Z) :
    ∀ v : V, (∀ x : X, ⁅(x : G),(v : G)⁆ ∈ Z) ↔ (v : G) ∈ W := by
  let ZR := Z.subgroupOf R
  let XR := X.subgroupOf R
  let : ZR.Normal := normal_subgroupOf_of_le_normalizer hZR
  let : XR.Normal := normal_subgroupOf_of_le_normalizer hRX
  let N := centralizerModulo (⊤ : Subgroup R) XR ZR
  let : N.Normal := centralizerModulo_top_normal XR ZR
  let A := N.map R.subtype
  have hRA : R ≤ normalizer (A : Set G) := by
    have hh := N.le_normalizer_map R.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hWA : W ≤ A := by
    intro w hw
    have hwR := d.section_le (d.kernel_le hw)
    refine ⟨⟨w,hwR⟩,mem_centralizerModulo_iff.mpr ⟨mem_top _,?_⟩,rfl⟩
    intro x hx
    rw [commutator_comm] at hWZ
    exact hWZ (commutator_mem_commutator hx hw)
  have hnot : ¬ V ≤ A := by
    intro hVA
    have hle : ⁅X,V⁆ ≤ Z := by
      apply commutator_le.mpr
      intro x hx v hv
      obtain ⟨v',hv',he⟩ := hVA hv
      have hc := (mem_centralizerModulo_iff.mp hv').2 ⟨x,hXR hx⟩ hx
      change ⁅x,(v' : G)⁆ ∈ Z at hc
      change (v' : G) = v at he
      rwa [he] at hc
    rw [commutator_comm,hVW] at hle
    exact hZW.not_ge hle
  have he : V ⊓ A = W := d.inf_eq_kernel_of_irreducible A hRA hWA hnot
  intro v
  constructor
  · intro hv
    apply he.le
    refine ⟨v.property,⟨⟨v,d.section_le v.property⟩,?_,rfl⟩⟩
    apply mem_centralizerModulo_iff.mpr
    exact ⟨mem_top _,fun x hx => hv ⟨x,hx⟩⟩
  · intro hv x
    rw [commutator_comm] at hWZ
    exact hWZ (commutator_mem_commutator x.property hv)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full original two-core quotient is the actual irreducible hexacode
translation module for L_z. Its denominator is exactly the original V. -/
theorem sourceOrbit_m24_centralizer_core_factor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ (S : Sextet) (r : localResidual L z →* sextetStabilizer S),
      E (Additive.ofMul z) = sextetVector S ∧
      r.range = solvableResidual (sextetStabilizer S) ∧
      Nonempty (BinaryConjugationSection (localResidual L z) (localTwoCore L z)
        D.sourceOrbit (MathieuSextet.coreAction S r)) ∧
      IsIrreducible (MathieuSextet.coreAction S r) := by
  obtain ⟨S,r,hS,hr,hker,hcore,_⟩ :=
    D.sourceOrbit_m24_centralizer_core_action h hmany hV hq hnon a E hE z hz hne
  have hWX := (D.sourceOrbit_m24_le_centralizer_residual h hmany hV hq hnon a E hE z hz hne).2.2
  have hRX := (show localResidual L z ≤ localResidual L z ⊔ (T : Subgroup G) from le_sup_left).trans
    (D.sourceOrbit_m24_centralizer_series_normalized h hmany hV hq hnon a E hE z hz hne).1
  have hX : ((localTwoCore L z).subgroupOf (localResidual L z)).map r =
      (nativeTranslation S).range := by
    change ((pCore 2 (localResidual L z)).map (localResidual L z).subtype |>.comap
      (localResidual L z).subtype).map r = _
    rw [comap_map_eq_self_of_injective (localResidual L z).subtype_injective,
      hcore,nativeQuotient_kernel]
  exact ⟨S,r,hS,hr,MathieuSextet.marked_core_section S (localResidual L z)
    (localTwoCore L z) D.sourceOrbit (localTwoCore_le L z) hWX hRX r hker hX,
    MathieuSextet.core_residual_irreducible S r hr⟩

/-- The full dual interval in source 8.2.11(4), on the original subgroups. -/
theorem sourceOrbit_m24_centralizer_core_interval
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (Y : Subgroup G) (hVY : D.sourceOrbit ≤ Y) (hYX : Y ≤ localTwoCore L z)
    (hRY : localResidual L z ≤ normalizer (Y : Set G)) :
    Y = D.sourceOrbit ∨ Y = localTwoCore L z := by
  obtain ⟨S,r,_,_,⟨d⟩,hirr⟩ :=
    D.sourceOrbit_m24_centralizer_core_factor h hmany hV hq hnon a E hE z hz hne
  let := hirr
  by_cases hXY : localTwoCore L z ≤ Y
  · exact Or.inr (le_antisymm hYX hXY)
  · exact Or.inl ((inf_eq_right.mpr hYX).symm.trans
      (d.inf_eq_kernel_of_irreducible Y hRY hVY hXY))

/-- The actual fixed subgroup modulo the original involution line is V_z.
Irreducibility of V/V_z and [V,O₂(L_z)]=V_z exclude a larger fixed subgroup. -/
theorem sourceOrbit_m24_centralizer_fixed_modulo_line
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∀ v : D.sourceOrbit, (∀ x : localTwoCore L z,
      ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G)) ↔
        (v : G) ∈ commutatorSpace L D.sourceOrbit z := by
  obtain ⟨S,r,_,_,_,⟨d⟩,_,hirr,_⟩ :=
    D.sourceOrbit_m24_centralizer_factors h hmany hV hq hnon a E hE z hz hne
  let := hirr
  obtain ⟨_,_,hc,hZW,_⟩ :=
    D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne
  have hRX := (show localResidual L z ≤ localResidual L z ⊔ (T : Subgroup G) from le_sup_left).trans
    (D.sourceOrbit_m24_centralizer_series_normalized h hmany hV hq hnon a E hE z hz hne).1
  have hRZ : localResidual L z ≤ normalizer (zpowers (z : G) : Set G) := by
    apply ((localResidual_le L z).trans inf_le_right).trans
    apply le_trans ?_ (centralizer_le_normalizer (zpowers (z : G) : Set G))
    rw [zpowers_eq_closure,centralizer_closure]
  exact fixed_modulo_line (localResidual L z) (localTwoCore L z) D.sourceOrbit
    (commutatorSpace L D.sourceOrbit z) (zpowers (z : G)) _ d (localTwoCore_le L z)
    hRX hRZ hZW rfl hc.le

/-- The full local core product, retaining the original Sylow and LT core. -/
theorem sourceOrbit_m24_centralizer_local_core_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 =
      localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let R := localResidual L z
  let X := localTwoCore L z
  let A := R ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hRJ : R ≤ J := ((localResidual_le L z).trans inf_le_left).trans le_sup_left
  have hAJ : A ≤ J := sup_le hRJ le_sup_right
  have hXR : X ≤ R := localTwoCore_le L z
  have hXA : X ≤ A := hXR.trans le_sup_left
  have hXN := (D.sourceOrbit_m24_centralizer_series_normalized h hmany hV hq hnon a E hE z hz hne).1
  have hJN : J ≤ normalizer (D.sourceOrbit : Set G) :=
    sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
  let f : J →* M24 := a.toMonoidHom.comp
    (D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp (inclusion hJN))
  let q := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hfL (l : L) : f (inclusion le_sup_left l) = q l := rfl
  have hqk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq)]
  have hqs : Function.Surjective q := a.surjective.comp
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq))
  have hfs : Function.Surjective f := fun y => by
    obtain ⟨l,hl⟩ := hqs y
    exact ⟨inclusion le_sup_left l,hl⟩
  let K := L.subgroupOf J
  let P := (T : Subgroup G).subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hfK : IsPGroup 2 (f.comp K.subtype).ker := by
    let j : (f.comp K.subtype).ker →* pCore 2 L := {
      toFun x := ⟨⟨x.val.val,x.val.property⟩,hqk ▸ x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective j
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun t : pCore 2 L => (t.val : G)) he)))
  have hfp : IsPGroup 2 f.ker := f.kernel_isPGroup_of_normal_supplement K P
    T.isPGroup'.comap_subtype (by
      rw [←subgroupOf_sup (show L ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right),subgroupOf_self]) hfK
  have hfk : f.ker = pCore 2 J := ker_eq_twoCore_of_surjective_m24 f hfs hfp
  obtain ⟨S,r,hS,hr,_,hcore,hrval⟩ :=
    D.sourceOrbit_m24_centralizer_core_action h hmany hV hq hnon a E hE z hz hne
  have hAC : A ≤ centralizer ({(z : G)} : Set G) :=
    sup_le ((localResidual_le L z).trans inf_le_right)
      (fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht))
  have hfix (g : A) : f (inclusion hAJ g) ∈ sextetStabilizer S := by
    rw [←sextetVector_stabilizer S]
    change cocodeRepresentation (f (inclusion hAJ g)) (sextetVector S) = sextetVector S
    rw [←hS]
    have he := hE (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
      (inclusion hJN (inclusion hAJ g))) (Additive.ofMul z)
    change E _ = cocodeRepresentation (f (inclusion hAJ g)) (E (Additive.ofMul z)) at he
    rw [←he]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g : G) * (z : G) * (g : G)⁻¹ = (z : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.mp (hAC g.property)
  let b : A →* sextetStabilizer S := (f.comp (inclusion hAJ)).codRestrict _ hfix
  have hbR (x : R) : b (inclusion le_sup_left x) = r x := by
    apply Subtype.ext
    exact (hrval x).symm
  have hbr : solvableResidual (sextetStabilizer S) ≤ b.range := by
    rw [←hr]
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion le_sup_left x,hbR x⟩
  have hbk : IsPGroup 2 b.ker := by
    have he : b.ker = f.ker.comap (inclusion hAJ) := by
      rw [←MonoidHom.ker_comp_of_injective b (sextetStabilizer S).subtype
        (sextetStabilizer S).subtype_injective]
      rfl
    rw [he]
    exact hfp.comap_of_injective _ (inclusion_injective hAJ)
  have hbcore : (pCore 2 A).map b = (nativeTranslation S).range := by
    have hk : IsPGroup 2 b.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hbk
    have he := b.rangeRestrict.comap_pCore_of_ker_isPGroup b.rangeRestrict_surjective hk
    have hm : (pCore 2 A).map b.rangeRestrict = pCore 2 b.range := by
      rw [←he,map_comap_eq_self]
      rw [MonoidHom.range_eq_top_of_surjective _ b.rangeRestrict_surjective]
      exact le_top
    have hh := congrArg (Subgroup.map b.range.subtype) hm
    rw [map_map] at hh
    exact hh.trans (MathieuSextet.residual_overgroup_core S b.range hbr)
  apply le_antisymm
  · rintro x ⟨u,hu,rfl⟩
    have huim := mem_map_of_mem b hu
    rw [hbcore,←nativeQuotient_kernel,←hcore] at huim
    obtain ⟨y,hy,he⟩ := huim
    have hyX : (y : G) ∈ X := mem_map_of_mem R.subtype hy
    have hxy : (inclusion hAJ u) * (inclusion hRJ y)⁻¹ ∈ pCore 2 J := by
      rw [←hfk]
      change f ((inclusion hAJ u) * (inclusion hRJ y)⁻¹) = 1
      rw [map_mul,map_inv]
      have he' : f (inclusion hRJ y) = f (inclusion hAJ u) := by
        exact (congrArg Subtype.val (hbR y)).trans (congrArg Subtype.val he)
      rw [he',mul_inv_cancel]
    have hxyQ : (u : G) * (y : G)⁻¹ ∈ Q := mem_map_of_mem J.subtype hxy
    have hp := (X ⊔ Q).mul_mem (mem_sup_right hxyQ) (mem_sup_left hyX)
    change (u : G) * (y : G)⁻¹ * (y : G) ∈ X ⊔ Q at hp
    change (u : G) ∈ X ⊔ Q
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hp
  · apply sup_le
    · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 R) hXA hXN
    · have hQT : Q ≤ (T : Subgroup G) := by
        simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
          (show (T : Subgroup G) ≤ J from le_sup_right)] using
          pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
      intro x hx
      exact inf_pCoreIn_le_of_le 2 hAJ ⟨mem_sup_right (hQT hx),hx⟩

/-- The whole centralizer core and the original normal closure lie in the
full local core product. No crossing or core-equality premise is assumed. -/
theorem sourceOrbit_m24_centralizer_closure_local_containment
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (centralizer ({(z : G)} : Set G)).pCoreIn 2 ≤
      localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ≤
        localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) :=
    fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  have hC := Chapter8.Section02.HermitianSource.point_centralizer_core_le_local_core L T (z : G) hTC
  rw [D.sourceOrbit_m24_centralizer_local_core_product h hmany hV hq hnon a E hE z hz hne] at hC
  have hEcore := (D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne).1
  exact ⟨hC,(map_mono (f := (centralizer ({(z : G)} : Set G)).subtype) hEcore).trans hC⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
