module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuOrdinary
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Bounds
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM24Equality

/-!
# Point containment and the marked M24 cocode equality row

An escaping distinguished-point centralizer has the original perfect component
with nontrivial two-group center and central quotient J4. The independent J4
central-two-cover theorem therefore gives source 8.1.1 containment. Applying
it to the original escaping-space and pushing-up consumers yields r=8, w=2,
image rank six, action-kernel rank three, and n(H)=2.

The native sextet fixed-space calculation excludes that kernel. The surviving
image is an actual conjugate of the trio kernel, and the same conjugator carries
the fixed space to the native affine-plane three-space. The original relative
centralizer consequently has rank three and equals C_V(V^g).

The explicit `hcover` is exactly the center-quotient corollary owned by
qt-model-j4-two-primary-covers. Its discharge, the other Mathieu source branches
and ambient J4 recognition remain with qt-d-1222-nonff-mathieu; the final
qt-d-1222-normalized-nonff assembly also retains that model dependency.
These conditional source results do not assert ambient J4 recognition.

Source: Aschbacher--Smith 8.1.1--3 and 7.5.3, printed pp.700,712--714,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open CFSG.Quasithin.ChapterH.Section13To16
open scoped IsMulCommutative
universe u
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
variable (hcover : ∀ (K : Type u) [Group K] [Finite K] [Group.IsPerfect K],
    (K ⧸ center K) ≃* Janko4.Model → IsPGroup 2 (center K) → center K = ⊥)
include hcover
/-- Source 8.1.1 on the original M24 cocode, with precisely the independent
J4 central-two-cover theorem retained. The actual escaping component is perfect
and has nontrivial two-group center, contradicting that theorem. -/
theorem sourceOrbit_m24_pair_control_of_janko_two_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨K,hK,_,_,_,_,_,hp,hz,_,⟨e⟩⟩ :=
    D.sourceOrbit_m24_escaping_janko_cover_of_many h hmany hV hq hnon a E hE x hx hout
  let := hK.2
  exact hz (hcover K e hp)

/-- The complete M24 equality row on every original w-offender: numerical
equalities, the literal trio-kernel marking and its fixed three-space. The
only external input is the named J4 cover theorem, not pair containment. -/
theorem sourceOrbit_m24_cocode_geometry_of_janko_two_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    globalR D.sourceOrbit = 8 ∧ globalW D.sourceOrbit (T : Subgroup G) = 2 ∧
      rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) = 6 ∧
      rank (offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G)) = 3 ∧
      (∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        generationParameter H = 2) ∧
      ∃ c : M24,
        ((inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)).map
          a.toMonoidHom).map (MulAut.conj c).toMonoidHom =
            trioKernel PairOvergroups.standardTrio ∧
        ((fixedSpace (automizerRepresentation D.sourceOrbit)
          (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g))).map
            E.toLinearMap).map (cocodeRepresentation c) = TrioCalculation.standardPlaneMap.range ∧
        rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) = 3 ∧
        D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
          D.sourceOrbit ⊓ centralizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hpair := D.sourceOrbit_m24_pair_control_of_janko_two_cover hcover h hmany hV hq hnon a E hE
  obtain ⟨hr,hw,hi,hk⟩ := D.sourceOrbit_m24_cocode_equalities_of_pair_control
    h hmany hV hq hnon a E hE hpair hg
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  have hcore := Chapter8.m24_row_dualCore_proper D.sourceOrbit_weakClosure_setup
    (Or.inr (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)) hg
    (by rw [hr]) (by rw [hw])
    (D.sourceOrbit_m24_automizer_twoRank_le_six h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq)
    ((Chapter7.log_card_eq_finrank D.sourceOrbit).trans (E.finrank_eq.trans finrank_cocode))
  let I := inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)
  let : IsElementaryAbelian 2 I := offender_inducedAutomizer_elementary D.sourceOrbit g
  obtain ⟨c,hc⟩ := MathieuEquality.marked_rank_six_trio D.sourceOrbit a E hE I hi hcore
  obtain ⟨hplane,hfixed⟩ := MathieuEquality.marked_trio_fixedSpace D.sourceOrbit a E hE I c hc
  refine ⟨hr,hw,hi,hk,?_,c,hc,hplane,?_,?_⟩
  · intro H hH
    exact D.sourceOrbit_m24_generation_eq_two_of_pair_control h hmany hV hq hnon a E hE hpair hH
  · have he : Chapter7.ambientSubmodule D.sourceOrbit
        (fixedSpace (automizerRepresentation D.sourceOrbit) I) =
        D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) := by
      ext x
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact ⟨v.property,(mem_fixedSpace_inducedAutomizer D.sourceOrbit
          (offenderNormalizer D.sourceOrbit g) inf_le_right (Additive.ofMul v)).mp hv⟩
      · intro hx
        refine ⟨⟨x,hx.1⟩,?_,rfl⟩
        exact (mem_fixedSpace_inducedAutomizer D.sourceOrbit
          (offenderNormalizer D.sourceOrbit g) inf_le_right _).mpr hx.2
    rw [←he]
    exact (Chapter7.ambientSubmodule_log_card D.sourceOrbit _).trans hfixed
  · have hs := (D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon).2.2
    exact (offender_fixedSpaceFamily_of_lt_globalS hg (by rwa [hw])).1

/-- An original w-offender exists, and has the actual trio marking and the
specified fixed three-space. Its existence is supplied by the finite minimum. -/
theorem sourceOrbit_m24_cocode_marked_offender_of_janko_two_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v)) :
    ∃ (g : G) (c : M24), IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      ((inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)).map
        a.toMonoidHom).map (MulAut.conj c).toMonoidHom =
          trioKernel PairOvergroups.standardTrio ∧
      ((fixedSpace (automizerRepresentation D.sourceOrbit)
        (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g))).map
          E.toLinearMap).map (cocodeRepresentation c) = TrioCalculation.standardPlaneMap.range ∧
      rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) = 3 := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  have hw := D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top D.sourceOrbit_weakClosure_setup
    (ne_top_of_le_ne_top (by simp) hw)
  obtain ⟨_,_,_,_,_,c,hc,hp,hf,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_janko_two_cover hcover h hmany hV hq hnon a E hE hg
  exact ⟨g,c,hg,hc,hp,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
