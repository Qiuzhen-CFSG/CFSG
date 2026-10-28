module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Constructions
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# The Thompson subgroup and its temporary normalizer

In the proof of 15.3.67, `I` is the elementary Thompson subgroup of the
original `C_G(E)`, and `I₀` is its normalizer of `C_T(V_E/E)`. The latter
centralizer is the actual quotient-centralizer construction already fixed
in `AbelianAmalgam.Constructions`. Intersecting `I` with the temporary
normalizer therefore recovers exactly `I₀`.

The definitions do not assert a quotient identification, an offender
inequality, or an index. They fix the groups for the independent local
structure and module calculations, and for descent to the original `G_E`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam

open Subgroup
variable {G : Type*} [Group G]

/-- `I = J(C_G(E))`, using maximum elementary abelian subgroups. -/
noncomputable def lineI (E : Subgroup G) : Subgroup G :=
  Stellmacher.elementaryAbelianMaxJ (centralizer (E : Set G))

/-- `I₀ = N_I(C_T(V_E/E))`, before and after the temporary replacement. -/
noncomputable def lineI0 (T V E : Subgroup G) : Subgroup G :=
  lineI E ⊓ normalizer (lineQuotientCentralizer T V E : Set G)

/-- The Thompson generators lie in the original line centralizer. -/
theorem lineI_le_centralizer (E : Subgroup G) :
    lineI E ≤ centralizer (E : Set G) :=
  sSup_le fun _ hA => hA.1

/-- In particular `I` is contained in the original `G_E`. -/
theorem lineI_le_lineNormalizer (E : Subgroup G) : lineI E ≤ lineNormalizer E :=
  (lineI_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))

/-- The two definitions of `I₀` use the same original `I` and quotient. -/
theorem lineI0_eq_inf_temporary (T V E : Subgroup G) :
    lineI0 T V E = lineI E ⊓ temporaryLineNormalizer T V E := by
  apply le_antisymm
  · exact le_inf inf_le_left
      (le_inf (inf_le_left.trans (lineI_le_lineNormalizer E)) inf_le_right)
  · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)

/-- Characteristicity of the elementary Thompson construction makes `I`
normal in the original `G_E`. -/
theorem lineI_normal_in_lineNormalizer (E : Subgroup G) :
    ((lineI E).subgroupOf (lineNormalizer E)).Normal := by
  have hNC : lineNormalizer E ≤ normalizer (centralizer (E : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (E : Set G))).mp
      inferInstance
  apply (normal_subgroupOf_iff_le_normalizer (lineI_le_lineNormalizer E)).mpr
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he := Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj g)
    (centralizer (E : Set G))
  exact he.symm.trans (congrArg Stellmacher.elementaryAbelianMaxJ
    (mem_normalizer_iff_map_conj_eq.mp (hNC hg)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
