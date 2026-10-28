module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Normalizers
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSylowGeometry

/-!
# The actual M24 cocode fixed-space two-local

Choose an original w-offender whose full normalizer lies in T. The native
E64 classification makes its fixed three-space U invariant under T, so
N_G(U) is an actual two-local of characteristic two. Both original conjugate
modules centralize U; the second does not normalize the original module.
TI then makes C_G(U) escape N_G(L). Finite minimal descent inside C_G(U)T
constructs an original H-star subgroup H, with n(H)=2 and O^2(H) centralizing U.

The full N_L(U) action constructed earlier extends to N_G(U), preserving the
native plane coordinates and identifying its kernel with the literal relative
centralizer. Thus N_G(U)=C_G(U)N_L(U). The residual seed-generation theorem
also places U in the center of the ambient two-core of N_G(U).

The chosen H need not contain the two-conjugate pair displayed here. No
canonical E.2 pair, component identity, or ambient J4 recognition is asserted.
The only external premise is the exact central-two-cover rigidity owned by
qt-model-j4-two-primary-covers. Final discharge, all remaining M22/M24 source
branches and ambient recognition remain with qt-d-1222-nonff-mathieu;
qt-d-1222-normalized-nonff retains the independent model safeguard as well.
Source: Aschbacher--Smith 8.2.5--8, printed pp.716--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
private theorem residual_le_centralizer_of_supplement
    (U H : Subgroup G) (hT : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hH : H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G)) :
    (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) := by
  let C := centralizer (U : Set G)
  let J := C ⊔ (T : Subgroup G)
  let N := C.subgroupOf J
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le C.le_normalizer (hT.trans (normalizer_le_normalizer_centralizer U)))
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show C ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype hgen
  have hr : pResidual 2 J ≤ N := sInf_le ⟨inferInstance,hquot⟩
  have hi := (map_pResidual_le 2 (inclusion hH)).trans hr
  rintro x ⟨y,hy,rfl⟩
  exact hi (mem_map_of_mem (inclusion hH) hy)

/-- A Sylow-positioned original offender constructs the actual fixed-space
two-local and an outside H-star subgroup in its centralizer joined with T.
The same original U is centralized by both conjugate modules and by the
selected H-star subgroup's two-residual. -/
theorem sourceOrbit_m24_fixedPlane_local_of_offender
    (hcover : ∀ (K : Type u) [Group K] [Finite K] [Group.IsPerfect K],
      (K ⧸ center K) ≃* Janko4.Model → IsPGroup 2 (center K) → center K = ⊥)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    rank U = 3 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsTwoLocal (normalizer (U : Set G)) ∧
      HasCharacteristicTwo (normalizer (U : Set G)) ∧
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) ∧
      ∃ H : Subgroup G,
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
        H ≤ normalizer (U : Set G) ∧
        (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
        generationParameter H = 2 := by
  let W := D.sourceOrbit
  let A := offenderNormalizer W g
  let U := W ⊓ centralizer (A : Set G)
  let M := normalizer (L : Set G)
  obtain ⟨hr,hw,hi,hk,hgen,c,hc,hp,hu,huf⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_janko_two_cover hcover h hmany hV hq hnon a E hE hg
  have hAn : A ≤ normalizer (W : Set G) := inf_le_right
  let : IsElementaryAbelian 2 (W.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := offender_elementary_of_le
    (show A ≤ W.map (MulAut.conj g).toMonoidHom from inf_le_left)
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    MathieuSylow.fixed_normalized W A T T.isPGroup'
      D.sourceOrbit_weakClosure_setup.normalizes hAT inferInstance a hi
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 3 at hu
    rw [hz] at hu
    norm_num [rank] at hu
  have hU2 : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 W).to_le inf_le_left
  have hlocal : IsTwoLocal (normalizer (U : Set G)) := ⟨U,hUne,hU2,rfl⟩
  have hlocalOver : normalizer (U : Set G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hlocal,hTU⟩
  have hchar : HasCharacteristicTwo (normalizer (U : Set G)) :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h.simpleQTKE.evenCharacteristic T) hlocalOver)
  have hWgC : W.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    rw [show U = W ⊓ centralizer (W.map (MulAut.conj g).toMonoidHom : Set G) from huf]
    exact inf_le_right
  have hWC : W ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    exact (show U ≤ W from inf_le_left).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hout : ¬ centralizer (U : Set G) ≤ M := by
    intro hcM
    have hcn := (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).centralizer_le_iff
      hUne (show U ≤ W from inf_le_left)
    have hnorm : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G) :=
      hWgC.trans (hcn.mp hcM)
    have hAeq : A = W.map (MulAut.conj g).toMonoidHom := inf_eq_left.mpr hnorm
    have hcor : subgroupCorank (W.map (MulAut.conj g).toMonoidHom) A = 0 := by
      rw [hAeq,subgroupCorank,relIndex_self]
      rfl
    have he := hg.2
    rw [hcor,hw] at he
    norm_num at he
  let J := centralizer (U : Set G) ⊔ (T : Subgroup G)
  have hJN : J ≤ normalizer (U : Set G) := sup_le (Subgroup.centralizer_le_normalizer _) hTU
  have hUJ : U ≤ J := (show U ≤ W from inf_le_left).trans (hWC.trans le_sup_left)
  have hcore : U ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hU2 hUJ hJN
  have hJ : J ∈ Chapter1.HOver G (T : Set G) :=
    ⟨fun he => hUne (le_bot_iff.mp (he ▸ hcore)),fun _ ht => mem_sup_right ht⟩
  have hJM : ¬ J ≤ M := fun hj => hout (le_sup_left.trans hj)
  let S : Set (Subgroup G) := {Y | (Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M) ∧ Y ≤ J}
  obtain ⟨H,hmin⟩ := (Set.toFinite S).exists_minimalFor id S ⟨J,⟨hJ,hJM⟩,le_rfl⟩
  have hHJ : H ≤ J := hmin.1.2
  have hH : H ∈ Chapter3.HStar (T : Subgroup G) M :=
    ⟨hmin.1.1,fun Y hY hYH => hmin.2 ⟨hY,hYH.trans hHJ⟩ hYH⟩
  refine ⟨hu,hTU,hlocal,hchar,hout,sup_le hWC hWgC,H,hH,hHJ,hHJ.trans hJN,?_,hgen H hH⟩
  exact residual_le_centralizer_of_supplement U H hTU hHJ

open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
/-- The original M24 cocode admits a Sylow-positioned offender. Its fixed
three-space has an actual two-local normalizer with full GL(3,2) quotient,
and an outside H-star subgroup whose two-residual centralizes that space.
Only the named independent J4 central-cover theorem remains explicit. -/
theorem sourceOrbit_m24_exists_fixedPlane_local
    (hcover : ∀ (K : Type u) [Group K] [Finite K] [Group.IsPerfect K],
      (K ⧸ center K) ≃* Janko4.Model → IsPGroup 2 (center K) → center K = ⊥)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v)) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      offenderNormalizer D.sourceOrbit g ≤ T ∧
      let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
      let N := normalizer (U : Set G)
      rank U = 3 ∧ (T : Subgroup G) ≤ N ∧ IsTwoLocal N ∧ HasCharacteristicTwo N ∧
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) ∧
      (∃ H : Subgroup G,
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧ H ≤ N ∧
        (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧ generationParameter H = 2) ∧
      ∃ (c : M24) (e : U ≃* Multiplicative Vector) (qN : N →* BinaryLinear.GL Vector),
        Function.Surjective qN ∧
        qN.ker = (centralizer (U : Set G)).subgroupOf N ∧
        (∀ u : U, MathieuCode.TrioCalculation.standardPlaneMap (e u).toAdd =
          MathieuCode.cocodeRepresentation c (E (Additive.ofMul (inclusion inf_le_left u)))) ∧
        (∀ (n : N) (u : U),
          (e (U.normalizerMonoidHom n u)).toAdd = qN n (e u).toAdd) ∧
        N = centralizer (U : Set G) ⊔ (L ⊓ N) ∧
        U ≤ N.pCoreIn 2 ∧ N.pCoreIn 2 ≤ centralizer (U : Set G) ∧
        ∀ B : Subgroup G, B ≤ U → B ≠ ⊥ →
          conjugateSpanBy B ((solvableResidual (L ⊓ N : Subgroup G)).map
            (L ⊓ N : Subgroup G).subtype) = U := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  have hw := D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon
  obtain ⟨g,hg,hAT⟩ := MathieuSylow.exists_offender_le_sylow D.sourceOrbit_weakClosure_setup
    (ne_top_of_le_ne_top (by simp) hw)
  obtain ⟨hu,hTU,hlocal,hchar,hout,hpair,hH⟩ :=
    D.sourceOrbit_m24_fixedPlane_local_of_offender hcover h hmany hV hq hnon a E hE hg hAT
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  let N := normalizer (U : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨c,e,π,hπ,_,hker,he,hact,hspan⟩ :=
    D.sourceOrbit_m24_fixedPlane_normalizer_action hcover h hmany hV hq hnon a E hE hg
  obtain ⟨qN,hqN,_,hqNker,hqNact,hgen⟩ :=
    MathieuSylow.full_normalizer_action U (L ⊓ N) inf_le_right e π hπ hact
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 3 at hu
    rw [hz] at hu
    norm_num [rank] at hu
  obtain ⟨hUcore,hcoreC⟩ := MathieuSylow.core_centralizes_of_seed_generation U _
    (IsElementaryAbelian.isPGroup 2 U) hUne ((map_subtype_le _).trans inf_le_right) hspan
  exact ⟨g,hg,hAT,hu,hTU,hlocal,hchar,hout,hpair,hH,c,e,qN,hqN,hqNker,he,hqNact,hgen,
    hUcore,hcoreC,hspan⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
