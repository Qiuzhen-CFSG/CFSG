module
public import CFSG.Quasithin.Chapter10.SourceElementCentralizerSetup
public import CFSG.Quasithin.ChapterB.Section02.Baumann.SpanSylow
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Theory.GroupTheory.ElementaryThompsonConjugacy

/-!
# The original point Sylow and Thompson transport

A locally saturated point fixed by an M-conjugate of Baum(T) is fixed
by Baum(T) itself: conjugate into the prescribed point Sylow within C_M(v),
then use Baumann weak closure in the original Sylow T. The proved source
Baumann normalizer control promotes that literal Sylow to C_G(v), and
Thompson heredity identifies J(C_T(v)) with J(T). The separate centralizing
source row uses the original full-module kernel normalizer control.

Source: Aschbacher–Smith10.2.9(1), printed pp.750–751. The row-specific
fixed-vector orbit is retained as an explicit input for its independent
natural/deleted geometry producers.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A locally saturated point fixed by an M-conjugate of the Thompson
subgroup retains the original Thompson subgroup. -/
theorem source_point_thompson_eq_of_conjugate_fixed
    {v : G}
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hex : ∃ m ∈ D.maximalLocal,
      (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤
        centralizer ({v} : Set G)) :
    elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G) := by
  obtain ⟨m,hm,hfix⟩ := hex
  apply elementaryAbelianMaxJ_eq_of_sylow_of_conjugate_le (T : Subgroup G) _ _
    inf_le_left T.isPGroup' hs (MulAut.conj m)
  refine le_inf ?_ hfix
  have hJM : elementaryAbelianMaxJ (T : Subgroup G) ≤ D.maximalLocal :=
    (sSup_le fun _ hA => hA.1).trans (le_normalizer_componentOrbit L T)
  exact (map_mono hJM).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer hm))

/-- Local Sylow saturation turns a conjugate Baumann-fixed representative
into a fixed vector for the original Baumann subgroup. -/
theorem source_point_baumann_fixed_of_conjugate_fixed
    {v : G}
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hex : ∃ m ∈ D.maximalLocal,
      (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤
        centralizer ({v} : Set G)) :
    baumann (T : Subgroup G) ≤ centralizer ({v} : Set G) := by
  obtain ⟨m,hm,hfix⟩ := hex
  let B := baumann (T : Subgroup G)
  let Q := B.map (MulAut.conj m).toMonoidHom
  have hQM : Q ≤ D.maximalLocal :=
    (map_mono (show B ≤ D.maximalLocal from
      inf_le_left.trans (le_normalizer_componentOrbit L T))).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer hm))
  obtain ⟨g,_,hg⟩ := exists_conjugate_le_relative_sylow _ _ Q hs
    ((T.isPGroup'.to_le inf_le_left).map (MulAut.conj m).toMonoidHom) (le_inf hQM hfix)
  have hh : B.map (MulAut.conj (g*m)).toMonoidHom ≤
      (T : Subgroup G) ⊓ centralizer ({v} : Set G) := by
    have he : (B.map (MulAut.conj m).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        B.map (MulAut.conj (g*m)).toMonoidHom := B.conjBy_conjBy m g
    exact he ▸ hg
  have he := baumann_conjugate_eq_of_le T (g*m) (hh.trans inf_le_left)
  exact he ▸ hh.trans inf_le_right

/-- The same concrete Baumann-orbit input discharges both point-Sylow
promotion and the exact Thompson equality used by the constrained inspection. -/
theorem source_point_sylow_and_thompson_of_baumann_conjugate_fixed
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G}
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hex : ∃ m ∈ D.maximalLocal,
      (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤
        centralizer ({v} : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) ∧
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
        elementaryAbelianMaxJ (T : Subgroup G) := by
  have hb := source_point_baumann_fixed_of_conjugate_fixed D hs hex
  exact ⟨source_element_sylow_of_baumann_centralizes D h1021 hb hs,
    elementaryAbelianMaxJ_eq_of_intermediate _ _
      (le_inf (sSup_le fun _ hA => hA.1) ((elementaryAbelianMaxJ_le_baumann _).trans hb))
      inf_le_left⟩
/-- The centralizing and moving source rows feed the same literal Sylow
and Thompson pair, with no action quotient substituted for the ambient groups. -/
theorem source_point_sylow_and_thompson_of_source_alternatives
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G} (hv : v ∈ D.fullModule)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hbranch : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∨
      ∃ m ∈ D.maximalLocal,
        (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤
          centralizer ({v} : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) ∧
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
        elementaryAbelianMaxJ (T : Subgroup G) := by
  rcases hbranch with hJ | hex
  · exact ⟨source_element_sylow_of_thompson_centralizes D hJ hv hs,
      elementaryAbelianMaxJ_eq_of_intermediate _ _
        (le_inf (sSup_le fun _ hA => hA.1)
          (hJ.trans (centralizer_le (Set.singleton_subset_iff.mpr hv)))) inf_le_left⟩
  · exact source_point_sylow_and_thompson_of_baumann_conjugate_fixed D h1021 hs hex

end CFSG.Quasithin.Chapter10
