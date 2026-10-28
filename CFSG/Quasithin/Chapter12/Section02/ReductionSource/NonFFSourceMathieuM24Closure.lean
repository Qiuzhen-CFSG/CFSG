module
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Fusion
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Factors
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.ReducedNormal.SectionClosureCore
public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# The original cocode normal closure and its fusion witness

The original Sylow normalizes V_z, and the actual section V_z/⟨z⟩ is
irreducible for L_z. Characteristic two in the original involution centralizer
therefore puts E=⟨V_z^{C_G(z)}⟩ in its two-core. The same irreducible-section
closure theorem puts [E,O₂(C_G(z))] and every square of E in the retained
central line. In particular E/Z(E) is elementary abelian.

Native M24 four-transitivity gives a distinct conjugate of the sextet tetrad
class in its seven-space. The original component surjection and cocode marking
lift this to an actual L-conjugate of z in E. Thus z is not weakly closed in E.
No normal-closure or fusion premise is added to the marked source branch.

These prove the first paragraph of 8.2.12 and the fusion premise of 8.2.14.
The exact equality E=O₂(C_G(z)), its extraspecial plus type and order, the
centralizer quotient, the earlier cocode marking, remaining Mathieu branches,
and ambient J4 recognition remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher–Smith 8.2.12–14, printed pp.722–723, refs/quasithin.pdf.
The imported native cocode calculations retain their ATLAS attribution.
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
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- For the original cocode, the actual closure E=⟨V_z^{C_G(z)}⟩ lies in
O₂(C_G(z)); its commutators with that whole core and all its squares lie
in the original central involution line. Thus E/Z(E) is elementary abelian. -/
theorem sourceOrbit_m24_centralizer_closure_core
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
    sourceClosure L D.sourceOrbit z ≤ pCore 2 (centralizer ({(z : G)} : Set G)) ∧
      ⁅sourceClosure L D.sourceOrbit z,pCore 2 (centralizer ({(z : G)} : Set G))⁆ ≤
        (zpowers (z : G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
      (∀ x : sourceClosure L D.sourceOrbit z, ((x.val : G)^2) ∈ zpowers (z : G)) ∧
      IsElementaryAbelian 2 ((sourceClosure L D.sourceOrbit z) ⧸
        center (sourceClosure L D.sourceOrbit z)) := by
  obtain ⟨s,r,_,_,⟨dmid⟩,_,hi,_,_⟩ :=
    D.sourceOrbit_m24_centralizer_factors h hmany hV hq hnon a E hE z hz hne
  let := hi
  obtain ⟨_,_,_,hZW,_⟩ :=
    D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne
  have hNW := (D.sourceOrbit_m24_centralizer_series_normalized h hmany hV hq hnon a E hE z hz hne).2
  let C := centralizer ({(z : G)} : Set G)
  let W := commutatorSpace L D.sourceOrbit z
  let Z := zpowers (z : G)
  let R := localResidual L z
  let A := R ⊔ (T : Subgroup G)
  have hWC : W ≤ C := commutatorSpace_le_centralizer L D.sourceOrbit z z.property
    D.sourceOrbit_component_normalizes
  have hWV : W ≤ D.sourceOrbit := commutatorSpace_le L D.sourceOrbit z D.sourceOrbit_component_normalizes
  have hZC : Z ≤ C := hZW.le.trans hWC
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hTC : (T : Subgroup G) ≤ C := fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  have hAC : A ≤ C := sup_le hRC hTC
  have hCZ : C ≤ normalizer (Z : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer (Z : Set G))
    rw [show Z = zpowers (z : G) from rfl,zpowers_eq_closure,centralizer_closure]
  let Zc := Z.subgroupOf C
  let Wc := W.subgroupOf C
  let Ac := A.subgroupOf C
  let P := T.subtype hTC
  let : Zc.Normal := normal_subgroupOf_of_le_normalizer hCZ
  have hZWc : Zc < Wc := by
    apply lt_of_le_of_ne (subgroupOf_mono C hZW.le)
    intro he
    apply hZW.ne
    have hh := congrArg (Subgroup.map C.subtype) he
    exact (map_subgroupOf_eq_of_le hZC).symm.trans
      (hh.trans (map_subgroupOf_eq_of_le hWC))
  have hz2 : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property)
    (fun he => hne (Subtype.ext he))
  have hchar : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) (isTwoLocal_involution_centralizer hz2) hTC)
  have hWc : IsElementaryAbelian 2 Wc := by
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
    exact IsElementaryAbelian.subgroupOf hWC
  have hAW : Ac ≤ normalizer (Wc : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    exact subgroupOf_mono C hNW
  have hirr (U : Subgroup C) (hZU : Zc ≤ U) (hUW : U ≤ Wc)
      (hAU : Ac ≤ normalizer (U : Set C)) : U = Zc ∨ U = Wc := by
    have hZU' : Z ≤ U.map C.subtype := by
      simpa only [Zc,map_subgroupOf_eq_of_le hZC] using map_mono (f := C.subtype) hZU
    have hUW' : U.map C.subtype ≤ W := by
      simpa only [Wc,map_subgroupOf_eq_of_le hWC] using map_mono (f := C.subtype) hUW
    have hAU' : A ≤ normalizer (U.map C.subtype : Set G) := by
      have hh := (map_mono (f := C.subtype) hAU).trans (U.le_normalizer_map C.subtype)
      simpa only [Ac,map_subgroupOf_eq_of_le hAC] using hh
    have hdec : U.map C.subtype = Z ∨ U.map C.subtype = W := by
      by_cases hw : W ≤ U.map C.subtype
      · exact Or.inr (le_antisymm hUW' hw)
      · have he := dmid.inf_eq_kernel_of_irreducible (U.map C.subtype)
          (le_sup_left.trans hAU') hZU' hw
        exact Or.inl ((inf_eq_right.mpr hUW').symm.trans he)
    rcases hdec with he|he
    · left
      apply map_injective C.subtype_injective
      simpa only [Zc,map_subgroupOf_eq_of_le hZC] using he
    · right
      apply map_injective C.subtype_injective
      simpa only [Wc,map_subgroupOf_eq_of_le hWC] using he
  have hh := normalClosure_core_of_irreducible_section Zc Wc Ac P hchar hWc hZWc
    (fun _ hx => D.sourceOrbit_weakClosure_setup.le_sylow (hWV hx))
    (fun _ ht => (show (T : Subgroup G) ≤ A from le_sup_right) ht) hAW hirr
  let q := QuotientGroup.mk' Zc
  let X := sourceClosure L D.sourceOrbit z
  let : IsElementaryAbelian 2 (X.map q) := hh.1.elementary
  have hsq : ∀ x : X, ((x.val : G)^2) ∈ Z := by
    intro x
    have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) (q x.val)
      (mem_map_of_mem q x.property : q x.val ∈ X.map q)
    have hm : x.val^2 ∈ Zc := (QuotientGroup.eq_one_iff _).mp (by
      change q (x.val^2)=1
      rw [map_pow]
      exact hp)
    exact hm
  refine ⟨hh.2.1,hh.2.2,hsq,?_⟩
  have hZ : Zc ≤ center C := by
    intro b hb
    apply mem_center_iff.mpr
    intro c
    apply Subtype.ext
    have hc : (c : G) ∈ centralizer (Z : Set G) := by
      simpa only [Z,zpowers_eq_closure,centralizer_closure] using c.property
    exact (hc b hb).symm
  let : IsMulCommutative (X ⧸ center X) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      apply Subgroup.commutator_le.mpr
      intro x _ y _
      have hc : ⁅x.val,y.val⁆ ∈ center C := hZ
        (hh.2.2 (commutator_mem_commutator x.property (hh.2.1 y.property)))
      apply mem_center_iff.mpr
      intro t
      exact Subtype.ext (mem_center_iff.mp hc t.val))
  refine { exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro b
  induction b using QuotientGroup.induction_on with
  | H x =>
    rw [←QuotientGroup.mk_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (mem_center_iff.mp (hZ (hsq x)) t.val)

/-- The original central involution has a distinct L-conjugate in the
literal closure E. This discharges the fusion premise of source 8.2.14. -/
theorem sourceOrbit_m24_not_weakly_closed_in_closure
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
    (∃ l : L, (l : G) * (z : G) * (l : G)⁻¹ ∈
        (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ∧
      (l : G) * (z : G) * (l : G)⁻¹ ≠ (z : G)) ∧
    ¬ (∀ t ∈ (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype,
      IsConj (z : G) t → t = (z : G)) := by
  obtain ⟨S,hS,hpair,_⟩ :=
    D.sourceOrbit_m24_centralizer_commutator_marking h hmany hV hq hnon a E hE z hz hne
  let q := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hsur : Function.Surjective q := a.surjective.comp
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq))
  obtain ⟨g,hg,hne'⟩ := exists_distinct_sextet_conjugate S
  obtain ⟨l,hl⟩ := hsur g
  let w : D.sourceOrbit := D.sourceOrbit.normalizerMonoidHom
    ⟨l,D.sourceOrbit_component_normalizes l.property⟩ z
  have he : E (Additive.ofMul w) = cocodeRepresentation g (sextetVector S) := by
    exact (hE (D.mathieuComponentAutomizer l) (Additive.ofMul z)).trans (by rw [hS]; rw [←hl]; rfl)
  have hw : (w : G) ∈ commutatorSpace L D.sourceOrbit z := (hpair w).mpr (he.symm ▸ hg)
  have hwE := commutatorSpace_le_sourceClosure L D.sourceOrbit z z.property
    D.sourceOrbit_component_normalizes hw
  have hwne : (w : G) ≠ (z : G) := by
    intro hwz
    have hwe : w = z := Subtype.ext hwz
    exact hne' (he.symm.trans ((congrArg (fun v => E (Additive.ofMul v)) hwe).trans hS))
  refine ⟨⟨l,hwE,hwne⟩,?_⟩
  intro hweak
  exact hwne (hweak _ hwE (isConj_iff.mpr ⟨(l : G),rfl⟩))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
