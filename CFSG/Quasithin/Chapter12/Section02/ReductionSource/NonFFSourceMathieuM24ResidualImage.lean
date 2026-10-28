module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Extraspecial
public import Theory.GroupTheory.ExtraspecialSquare
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryContaining
public import Theory.ElementaryAbelian.PrimeRankCard
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Quotient
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerAction
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerQuotient

/-!
# The original point residual in the full centralizer quotient

For B, the image of the original L_z in C_G(z)/O₂(C_G(z)), the cocode
marking identifies O₂(B) equivariantly with the natural binary four-space
on the same six tetrads. Thus |B|=17280 and B/O₂(B) is the full 3·A₆.
The actual ambient Sylow image normalizes B. A normal quasisimple component
strictly contains B; its full simple/three-cover catalogue is retained.
The identification with 3·M₂₂ remains with qt-d-1222-nonff-mathieu.

Source: Aschbacher–Smith 8.2.13, printed pp.722–723, using A.3.6 and A.3.12.
The full quotient action and its conditional identification are in
NonFFSourceMathieuM24FullQuotient.
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open scoped IsMulCommutative commutatorElement

public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem quasisimple_component_models {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsSQTK KnownSimple.IsKnownSimple Q) (hO : pCore 2 Q = ⊥)
    (K : Subgroup Q) (hK : K.IsCComponent) [IsQuasisimple K] :
    (IsSimpleGroup K ∧ Chapter1.Section02.LocalModels.TheoremCModel K) ∨
      (Nonempty (center K ≃* Multiplicative (ZMod 3)) ∧
        Chapter1.Section02.LocalModels.ThreeCoverModel K) := by
  have hfit : generalizedFitting K ≠ fittingSubgroup K := by
    intro heq
    have hf : fittingSubgroup K = ⊤ := heq.symm.trans generalizedFitting_eq_top_of_quasisimple
    let : Group.IsSolvable (⊤ : Subgroup K) := hf ▸
      (inferInstance : Group.IsSolvable (fittingSubgroup K))
    exact hK.not_isSolvable
      (Group.isSolvable_of_surjective (f := (topEquiv (G := K)).toMonoidHom)
        (topEquiv (G := K)).surjective)
  have hsource := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    Q hQ hO K hK
  cases hsource.1 with
  | simple _ hs hm => exact .inl ⟨hs,hm⟩
  | cover _ hc hm => exact .inr ⟨hc,hm⟩
  | natural hs => exact (hfit hs.1).elim
  | nilpotent hs => exact (hfit hs.1).elim

/-- The full core of the original residual image is the four-dimensional
natural module on the six tetrads, with the original conjugation action. -/
theorem sourceOrbit_m24_centralizer_quotient_core_coordinates
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
    ∃ (S : Sextet) (r : localResidual L z →* sextetStabilizer S)
      (e : pCore 2 (MathieuSextet.pointResidualImage L z) ≃*
        Multiplicative (BinaryPermutation.natural (SextetPart S))),
      E (Additive.ofMul z) = sextetVector S ∧
      r.range = solvableResidual (sextetStabilizer S) ∧
      ∀ (x : localResidual L z) (v : pCore 2 (MathieuSextet.pointResidualImage L z)),
        (e (MulAut.conjNormal (MathieuSextet.pointResidualProjection L z x) v)).toAdd =
          MathieuSextet.topAction S r x (e v).toAdd := by
  let C := centralizer ({(z : G)} : Set G)
  let R := localResidual L z
  let X := localTwoCore L z
  let F := C.pCoreIn 2
  let W := commutatorSpace L D.sourceOrbit z
  let B := MathieuSextet.pointResidualImage L (z : G)
  let f := MathieuSextet.pointResidualProjection L (z : G)
  have hf := MathieuSextet.pointResidualProjection_surjective L (z : G)
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hXR : X ≤ R := localTwoCore_le L z
  have hVX : D.sourceOrbit ≤ X :=
    (D.sourceOrbit_m24_le_centralizer_residual h hmany hV hq hnon a E hE z hz hne).2.2
  have hVR := hVX.trans hXR
  have hprod : F ⊔ D.sourceOrbit = X := by
    change (centralizer ({(z : G)} : Set G)).pCoreIn 2 ⊔ D.sourceOrbit = X
    rw [D.sourceOrbit_m24_centralizer_core_eq_closure h hmany hV hq hnon a E hE z hz hne]
    exact D.sourceOrbit_m24_centralizer_closure_join_module h hmany hV hq hnon a E hE z hz hne
  have hFR : F ≤ R := (le_sup_left.trans hprod.le).trans hXR
  have hcap : D.sourceOrbit ⊓ F = W :=
    (D.sourceOrbit_m24_centralizer_module_core_intersections h hmany hV hq hnon a E hE z hz hne).2.1
  have hfk : f.ker = F.subgroupOf R := MathieuSextet.pointResidualProjection_kernel L z
  have hk : IsPGroup 2 f.ker := hfk.symm ▸ (isPGroup_pCoreIn 2 C).comap_subtype
  have hX : X.subgroupOf R = pCore 2 R := comap_map_eq_self_of_injective R.subtype_injective _
  have hmap : (D.sourceOrbit.subgroupOf R).map f = pCore 2 B := by
    have hh := congrArg (Subgroup.map f)
      (congrArg (fun A : Subgroup G => A.subgroupOf R) hprod)
    have hkmap : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff f.ker).mpr le_rfl
    rw [subgroupOf_sup hFR hVR,Subgroup.map_sup,hX,←hfk,hkmap,bot_sup_eq] at hh
    have hm : (pCore 2 R).map f = pCore 2 B := by
      rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self_of_surjective hf]
    exact hh.trans hm
  let g : D.sourceOrbit →* pCore 2 B := {
    toFun v := ⟨f (inclusion hVR v),hmap ▸ mem_map_of_mem f v.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' v w := Subtype.ext (map_mul (f.comp (inclusion hVR)) v w) }
  have hg : Function.Surjective g := by
    intro v
    obtain ⟨r,hr,he⟩ := hmap.ge v.property
    exact ⟨⟨r,hr⟩,Subtype.ext he⟩
  obtain ⟨S,r,hS,hr,_,⟨d⟩,_,_,_⟩ :=
    D.sourceOrbit_m24_centralizer_factors h hmany hV hq hnon a E hE z hz hne
  have hgker : g.ker = d.coordinates.ker := by
    rw [d.kernel_eq]
    ext v
    change g v=1 ↔ (v : G) ∈ W
    rw [Subtype.ext_iff]
    change f (inclusion hVR v)=1 ↔ (v : G) ∈ W
    change inclusion hVR v ∈ f.ker ↔ _
    rw [hfk]
    exact ⟨fun hv => hcap.le ⟨v.property,hv⟩,fun hv => (hcap.ge hv).2⟩
  obtain ⟨e,_,he⟩ := MathieuSextet.core_coordinates R D.sourceOrbit W d f g hg (fun _ => rfl) hgker
  exact ⟨S,r,e,hS,hr,he⟩

/-- The original residual image has elementary core of order sixteen and the
full nonsplit triple-six quotient. -/
theorem sourceOrbit_m24_centralizer_quotient_residual_structure
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
    let B := MathieuSextet.pointResidualImage L (z : G)
    IsElementaryAbelian 2 (pCore 2 B) ∧ Nat.card (pCore 2 B) = 16 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nat.card B = 17280 := by
  let B := MathieuSextet.pointResidualImage L (z : G)
  let f := MathieuSextet.pointResidualProjection L (z : G)
  obtain ⟨S,r,e,_,_,_⟩ :=
    D.sourceOrbit_m24_centralizer_quotient_core_coordinates h hmany hV hq hnon a E hE z hz hne
  let : Finite (BinaryPermutation.natural (SextetPart S)) :=
    Finite.of_equiv (pCore 2 B) e.toEquiv
  let : IsElementaryAbelian 2 (Multiplicative (BinaryPermutation.natural (SextetPart S))) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      change 2 • x.toAdd = 0
      rw [←Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_self,zero_smul]) }
  have hel : IsElementaryAbelian 2 (pCore 2 B) := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hd : Module.finrank (ZMod 2) (BinaryPermutation.natural (SextetPart S)) = 4 := by
    rw [BinaryPermutation.finrank_natural_even (SextetPart S) (by rw [card_sextetPart]; decide),card_sextetPart]
  have hc : Nat.card (pCore 2 B) = 16 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (BinaryPermutation.natural (SextetPart S)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    norm_num
  obtain ⟨_,_,_,_,_,_,⟨eqR⟩,_,_⟩ :=
    D.sourceOrbit_m24_centralizer_residual h hmany hV hq hnon a E hE z hz hne
  let eB := (f.pCoreQuotientEquiv
    (MathieuSextet.pointResidualProjection_surjective L z)
    (MathieuSextet.pointResidualProjection_kernel_isTwoGroup L z)).symm.trans eqR
  refine ⟨hel,hc,⟨eB⟩,?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),Nat.card_congr eB.toEquiv,
    Atlas.Codes.hexEven_card,hc]

/-- The actual Sylow image normalizes the original local residual image. -/
theorem sourceOrbit_m24_centralizer_quotient_local
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
    let C := centralizer ({(z : G)} : Set G)
    let B := MathieuSextet.pointResidualImage L (z : G)
    ∃ P : Sylow 2 (C ⧸ pCore 2 C),
      (P : Subgroup (C ⧸ pCore 2 C)) =
        ((T : Subgroup G).subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ∧
      B ∈ ChapterA.Section03.localCComponents P ∧
      (P : Subgroup (C ⧸ pCore 2 C)) ≤ normalizer (B : Set (C ⧸ pCore 2 C)) := by
  let C := centralizer ({(z : G)} : Set G)
  let R := localResidual L z
  let π := QuotientGroup.mk' (pCore 2 C)
  have hTC : (T : Subgroup G) ≤ C := fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  let S := T.subtype hTC
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  obtain ⟨_,_,_,_,_,_,_,hcomp,hTR⟩ :=
    D.sourceOrbit_m24_centralizer_residual h hmany hV hq hnon a E hE z hz hne
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hRM : R ≤ normalizer (L : Set G) ⊓ C :=
    (localResidual_le L z).trans (inf_le_inf_right _ L.le_normalizer)
  have hlocal : R ∈ ChapterA.Section03.localCComponents (T : Subgroup G) :=
    hcomp.subgroupOf_of_le le_sup_left (sup_le hRM (le_inf D.sylow_normalizes_component hTC))
  have hlocalC : R.subgroupOf C ∈ ChapterA.Section03.localCComponents S :=
    ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hRC
  let : Group.IsSolvable π.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 C)).ker
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
    infer_instance
  have hnormC : (S : Subgroup C) ≤ normalizer (R.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hRC]
    exact comap_mono hTR
  exact ⟨P,rfl,Chapter1.Section02.localCComponents_map_of_solvable_ker hlocalC π,
    (map_mono hnormC).trans (le_normalizer_map π)⟩

/-- In the original centralizer quotient the containing component is normal,
quasisimple, and strictly larger than the local residual image. The full source
catalogue is retained until the M22 identification. -/
theorem sourceOrbit_m24_centralizer_quotient_containing
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
    let C := centralizer ({(z : G)} : Set G)
    let B := MathieuSextet.pointResidualImage L (z : G)
    ∃ K : Subgroup (C ⧸ pCore 2 C),
      K.IsCComponent ∧ K.Normal ∧ B < K ∧ IsQuasisimple K ∧
      ((IsSimpleGroup K ∧ Chapter1.Section02.LocalModels.TheoremCModel K) ∨
        (Nonempty (center K ≃* Multiplicative (ZMod 3)) ∧
          Chapter1.Section02.LocalModels.ThreeCoverModel K)) := by
  let C := centralizer ({(z : G)} : Set G)
  let B := MathieuSextet.pointResidualImage L (z : G)
  let π := QuotientGroup.mk' (pCore 2 C)
  obtain ⟨J,hJC,hJ,hRJ,hCJ⟩ :=
    D.sourceOrbit_m24_centralizer_containing_component h hmany hV hq hnon a E hE z hz hne
  let Jc := J.subgroupOf C
  let K := Jc.map π
  let : Jc.Normal := normal_subgroupOf_of_le_normalizer hCJ
  let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
  have hK : K.IsCComponent := hJ.map_quotient (pCore 2 C)
  have hn : K.Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hBK : B ≤ K := map_mono (subgroupOf_mono C hRJ)
  have hO : pCore 2 (C ⧸ pCore 2 C) = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hKcore : pCore 2 K = ⊥ := by
    rw [←hK.subnormal.pCore_subgroupOf 2,hO,bot_subgroupOf]
  obtain ⟨he,hcard,_,_⟩ :=
    D.sourceOrbit_m24_centralizer_quotient_residual_structure h hmany hV hq hnon a E hE z hz hne
  let := he
  have hproper : B ≠ K := by
    intro heq
    have hh := congrArg (fun A : Subgroup (C ⧸ pCore 2 C) => Nat.card (pCore 2 A)) heq
    rw [hcard,hKcore] at hh
    norm_num at hh
  have hr : 4 ≤ primeRank 2 K := by
    have hh := IsElementaryAbelian.log_card_eq_primeRank (p := 2) (pCore 2 B)
    rw [hcard] at hh
    have hfour : primeRank 2 (pCore 2 B) = 4 := by norm_num at hh; omega
    rw [←hfour]
    exact (Theory.GroupTheory.primeRank_le_of_injective 2 (pCore 2 B).subtype
      (pCore 2 B).subtype_injective).trans
        (Theory.GroupTheory.primeRank_le_of_injective 2 (inclusion hBK) (inclusion_injective hBK))
  have hCH : C ∈ Chapter1.H G := by
    change C.pCoreIn 2 ≠ ⊥
    intro hc
    have hh := D.sourceOrbit_m24_centralizer_extraspecial h hmany hV hq hnon a E hE z hz hne
    have hcore : pCore 2 C = sourceClosure L D.sourceOrbit z := by
      apply map_injective C.subtype_injective
      exact D.sourceOrbit_m24_centralizer_core_eq_closure h hmany hV hq hnon a E hE z hz hne
    have hzcore : pCore 2 C = ⊥ :=
      (map_eq_bot_iff_of_injective (pCore 2 C) C.subtype_injective).mp hc
    have hn := hh.2.1
    rw [←hcore,hzcore] at hn
    norm_num at hn
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hCH
  have hqs := ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank hQ hO hK
    ((by decide : 2 ≤ 4).trans hr)
  let := hqs
  exact ⟨K,hK,hn,lt_of_le_of_ne hBK hproper,hqs,quasisimple_component_models hQ hO K hK⟩



end CFSG.Quasithin.Chapter12.Section02.ChosenModule
