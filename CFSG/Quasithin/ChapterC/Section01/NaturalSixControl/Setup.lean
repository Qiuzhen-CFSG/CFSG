module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.Source
public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The original natural S6 point-stabilizer data

The source group is the actual product of its component and a Sylow two
subgroup. Its action on the specified binary natural module is marked by a
surjection onto S6 with the actual two-core as kernel. The chosen nonidentity
vector is fixed by the specified Sylow subgroup. Thus its centralizer is the
literal point parabolic, whose embedded two-core and Baumann subgroup are
used throughout C.1.37 and the application in 13.2.2(7).

Source: Aschbacher--Smith, C.1.37, printed pp.141--143, and 13.2.2(7),
printed pp.877--878.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Theory.GroupTheory
universe u
variable {K : Type u} [Group K]

/-- The literal source data for the natural S6 point-parabolic branch.
No offender, Baumann-family, or MS classification conclusion is a field. -/
structure SourceData (L V : Subgroup K) [L.Normal] [V.Normal] (T : Sylow 2 K) where
  sqtk : IsSQTK KnownSimple.IsKnownSimple K
  component : L.IsCComponent
  fitting : generalizedFitting K = pCore 2 K
  component_fitting : generalizedFitting L = pCore 2 L
  generation : L ⊔ (T : Subgroup K) = ⊤
  elementary : IsElementaryAbelian 2 V
  q : K →* Equiv.Perm (Fin 6)
  onto : Function.Surjective q
  ker_eq : q.ker = pCore 2 K
  image_component : L.map q = alternatingGroup (Fin 6)
  eV : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6))
  action : ∀ g v, (eV (MulAut.conjNormal g v)).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 6) (q g) (eV v).toAdd
  v : V
  v_ne : v ≠ 1
  sylow_fixes : ∀ t ∈ (T : Subgroup K), t * (v : K) = (v : K) * t

namespace SourceData
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : SourceData L V T)
include d

/-- The original point parabolic. Over F2 point and nonzero-vector
stabilizers coincide. -/
def P : Subgroup K := centralizer ({(d.v : K)} : Set K)

/-- The two-core of the original point parabolic, embedded in K. -/
noncomputable abbrev R : Subgroup K := d.P.pCoreIn 2

/-- The literal Baumann group used in 13.2.2(7). -/
noncomputable abbrev B : Subgroup K := ChapterB.baumann d.R

theorem sylow_le_point : (T : Subgroup K) ≤ d.P := by
  intro t ht
  apply mem_centralizer_iff.mpr
  intro x hx
  obtain rfl : x = (d.v : K) := Set.mem_singleton_iff.mp hx
  exact (d.sylow_fixes t ht).symm

theorem kernel_centralizer : d.q.ker = centralizer (V : Set K) :=
  RankOne.SymmetricSix.natural_six_kernel_eq_centralizer V d.q d.eV d.action

theorem centralizer_eq_core : centralizer (V : Set K) = pCore 2 K :=
  (kernel_centralizer d).symm.trans d.ker_eq

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
