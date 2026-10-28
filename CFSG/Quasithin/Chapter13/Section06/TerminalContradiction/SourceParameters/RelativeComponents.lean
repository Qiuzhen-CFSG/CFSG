module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Residual
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Relative C-component exclusion in 13.6.26(1)

Let H be an actual member of Hz and K a member of C(H). Work first in H:
Proposition 1.2.1(3), applied to K.subgroupOf H, makes its normalizer have
index at most two. The restriction of the ambient Sylow two-subgroup T
therefore generates a normal conjugate span. Mapping this span through
H's inclusion gives precisely Y = conjugateSpanBy K T in G. Perfectness
of K makes Y perfect, hence Y = O²(Y).

If K ≤ M = N_G(L), the T-invariance of L from 13.3.2(2) gives Y ≤ M.
The source family Hz supplies H ∈ H(T,M), so 13.3.8(2), with L, M and Y
in the source roles, makes Y a {2,3}-group. Burnside's two-prime theorem
then makes K solvable, contradicting its relative C-component property.

This proves the entire application from universal earlier-source inputs;
none of the target-specific normality, residual or containment conditions
is assumed. In the A₅ case of Hypothesis 13.3.1, `qt-13-03-preliminaries`
must supply 13.3.2(2) and the exact `Earlier1338Two` defined in `Residual`.
The producer of the universal A.3.8(3) input is `qt-a03-sqtk-structure`.
The known-simple catalogue is complete, and SQTK of H/O₂(H) is derived
from the ambient simple QTKE hypothesis and the actual nontrivial core.
The exclusions and uniform A₅ clause of Hypothesis 13.3.1 are used by the
earlier results; this deduction requires no further module calculation.
Until those universal inputs are discharged, the last theorem is a
conditional source deduction, not an unconditional assertion of 13.6.26.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.2.1(3), 13.3.2(2), 13.3.8(2), and 13.6.26(1), printed pp.504, 884,
886–887, and 934. The assembly consumer is SourceParameters in the
terminal A₅ argument. Legacy Parameters and its public API are preserved.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem relative_span_normal (T : Sylow 2 G) {H K : Subgroup G}
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    H ≤ normalizer (conjugateSpanBy K T : Set G) := by
  let S := T.subtype hTH
  let D := conjugateSpanBy (K.subgroupOf H) (S : Subgroup H)
  have hn : D.Normal := conjugateSpanBy_sylow_normal _ S hK
  have he : D.map H.subtype = conjugateSpanBy K T := by
    rw [map_conjugateSpanBy]
    simp only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le hTH]
  have hd : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective D
  have hrel : ((conjugateSpanBy K T).subgroupOf H).Normal := by
    rw [← he, hd]
    exact hn
  exact (normal_subgroupOf_iff_le_normalizer
    (conjugateSpanBy_le hKH (hTH.trans H.le_normalizer))).mp hrel

private theorem perfect_twoPerfect {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] : IsPPerfect 2 Y := by
  intro N hN hq
  let := hN
  by_contra hne
  let : Nontrivial (Y ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (Y ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isNilpotent (Y ⧸ N) hq.isNilpotent

/-- The complete universal A.3.8(3) input, with genuine model isomorphisms.
Its source producer is `qt-a03-sqtk-structure`. -/
def EarlierA38Three : Prop :=
  ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ B : Subgroup X, B.IsCComponent →
        B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
          Chapter1.Section02.NonnormalCComponentModel B

/-- Every relative C-component has a normal, perfect Sylow-conjugate span
inside the actual local overgroup. -/
theorem relative_component_span_properties
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u}) (T : Sylow 2 G)
    {H K : Subgroup G} (hH : H ∈ Chapter1.H G)
    (hTH : (T : Subgroup G) ≤ H) (hK : K ∈ Chapter1.cComponentsIn H) :
    conjugateSpanBy K T ≤ H ∧
      H ≤ normalizer (conjugateSpanBy K T : Set G) ∧
      Group.IsPerfect (conjugateSpanBy K T) ∧ IsPPerfect 2 (conjugateSpanBy K T) := by
  have horbit := Chapter1.Section02.proposition_1_2_1_three_index_of_A_3_8 hA38
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH) hK.2
  let := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  let hperfect := conjugateSpanBy_isPerfect K (T : Subgroup G)
  exact ⟨conjugateSpanBy_le hK.1 (hTH.trans H.le_normalizer),
    relative_span_normal T hK.1 hTH (horbit.imp_right And.left),
    hperfect, perfect_twoPerfect⟩

/-- All target-specific premises of 13.3.8(2), for L, N(L), and the
T-conjugate span of the relative component in the source roles. The
normalization input is precisely the earlier 13.3.2(2) conclusion. -/
theorem relative_component_1338_applicability
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u}) (T : Sylow 2 G) (L L₁ G₁ M : Subgroup G)
    (hM : M = normalizer (L : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {H K : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ T G₁ M)
    (hK : K ∈ Chapter1.cComponentsIn H) (hKM : K ≤ M) :
    H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G) ∧
      conjugateSpanBy K T ≤ H ∧
      H ≤ normalizer (conjugateSpanBy K T : Set G) ∧
      IsPPerfect 2 (conjugateSpanBy K T) ∧
      conjugateSpanBy K T ≤ normalizer (L : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨hle, hn, _, hp⟩ := relative_component_span_properties hG hA38 T hH.1.1 hTH hK
  refine ⟨?_, hle, hn, hp, ?_⟩
  · rw [← hM]
    exact ⟨⟨hH.1.1, hTH⟩, hH.2.2⟩
  · rw [← hM]
    exact conjugateSpanBy_le hKM ((hTL.trans_eq hM.symm).trans M.le_normalizer)

/-- The source component-exclusion argument from the universal earlier
results. No containment, normality or residual condition on the chosen
span is assumed. -/
theorem source_13_6_26_1_of_earlier
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u})
    (T : Sylow 2 G) (L L₁ G₁ M : Subgroup G)
    (hL : L ∈ MainForward.faithfulLocalComponents T)
    (hM : M = normalizer (L : Set G))
    (h1332 : ∀ J ∈ MainForward.faithfulLocalComponents T,
      (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal)
    (h1338 : Earlier1338Two T)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ T G₁ M) :
    ∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M := by
  intro K hK hKM
  have hTL : (T : Subgroup G) ≤ normalizer (L : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).mp (h1332 L hL))
  obtain ⟨hout, hle, hn, hp, hMspan⟩ :=
    relative_component_1338_applicability hG hA38 T L L₁ G₁ M hM hTL hH hK hKM
  have h23 := h1338 L hL H hout (conjugateSpanBy K T) hle hn hp hMspan
  let : Group.IsSolvable (conjugateSpanBy K T) :=
    Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three _ (by
      intro p hp hd
      exact (IsPiGroup_iff _ _).mp h23 ⟨p, hp⟩ hd)
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (le_conjugateSpanBy K T))
    (Subgroup.inclusion_injective _)
  exact hK.2.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).injective)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
