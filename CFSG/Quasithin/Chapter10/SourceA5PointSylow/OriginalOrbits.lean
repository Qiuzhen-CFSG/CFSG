module
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Transport
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import CFSG.Quasithin.ChapterB.Section02.Baumann.FixedOrbit
/-!
# Original partner points from Thompson fixed orbits

Each original moved vector has an L-conjugate fixed by J(T) in the
natural and deleted A₅ rows. Since the original moved factor is elementary
inside T, the fixed-center theorem makes that representative Baumann-fixed.
Conjugation carries this statement to every partner vector. For locally
saturated points, Baumann weak closure then supplies the full centralizer
Sylow subgroup and preserves the elementary Thompson subgroup.

Source: Aschbacher–Smith10.2.9(1), printed pp.750–751. The row orbit premise
is the exact contract discharged by the separate representation modules.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance pointSylowOriginalOrbitElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_a5_partner_baumann_conjugate_fixed_of_thompson_orbits
    (horbit : ∀ w ∈ ⁅D.fullModule,L⁆, ∃ l ∈ L,
      (MulAut.conj l) w ∈ ⁅D.fullModule,L⁆ ⊓
        centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    ∃ m ∈ D.maximalLocal,
      (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) D.simpleQTKE T D.maximal
  have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hWT : ⁅D.fullModule,L⁆ ≤ (T : Subgroup G) :=
    (le_normalizer_iff_commutator_le_left.mp (hLM.trans D.maximalLocal_normalizes_fullModule)).trans
      (D.fullModule_le_sylow hu)
  exact exists_baumann_conjugate_centralizing_of_elementary_orbits (T : Subgroup G)
    ⁅D.fullModule,L⁆ D.maximalLocal L hWT hLM horbit
    (le_normalizer_componentOrbit L T ht) hv

theorem source_a5_partner_sylow_and_thompson_of_thompson_orbits
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (horbit : ∀ w ∈ ⁅D.fullModule,L⁆, ∃ l ∈ L,
      (MulAut.conj l) w ∈ ⁅D.fullModule,L⁆ ⊓
        centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) ∧
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
        elementaryAbelianMaxJ (T : Subgroup G) :=
  source_point_sylow_and_thompson_of_baumann_conjugate_fixed D h1021 hs
    (source_a5_partner_baumann_conjugate_fixed_of_thompson_orbits D horbit ht hv)
end CFSG.Quasithin.Chapter10
