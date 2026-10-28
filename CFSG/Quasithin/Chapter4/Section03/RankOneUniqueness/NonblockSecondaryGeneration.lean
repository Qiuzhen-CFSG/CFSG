module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySourceGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeCoreMovement

/-!
# Exact generation reduction for the secondary radical

The literal secondary projection carries its two-core onto the affine root
plane, which is moved by the point local. Its kernel lies in the original Q
once the source core identity Q=O₂(K) is supplied. Lifting the commutator
identity therefore proves Q[O₂(K₂),K₂]=QO₂(K₂).

Consequently Q[R₂,K₂]=R₂ is equivalent to the concrete coverage condition
R₂≤QO₂(K₂). This accounts for the entire radical and does not infer coverage
from the already known lower bound on the secondary two-core's order.
The final application gives the sufficient image generation under the same
literal normalQuotientAction used by the corrected sieve.

Proving the remaining coverage condition, constructing the MS/source data,
and final assembly remain with `qt-d-1222-rankone-uniqueness-nonblock`.
Source: Aschbacher--Smith, original 4.3.11--16, printed pp.617--618.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d)
include m
/-- The actual secondary two-core is moved modulo the original Q. -/
theorem secondary_core_generation (hn : 1 < n) (hcore : Q c = (K c).pCoreIn 2) :
    Q c ⊔ ⁅(secondary c).pCoreIn 2, secondary c⁆ = Q c ⊔ (secondary c).pCoreIn 2 := by
  let C := ⁅pCore 2 (secondary c), (⊤ : Subgroup (secondary c))⁆
  have he : C.map m.secondaryProjection = (pCore 2 (secondary c)).map m.secondaryProjection := by
    dsimp only [C]
    rw [map_commutator,m.secondary_core_image hn,
      map_top_of_surjective _ (m.secondaryProjection_surjective hn),pointLocalSL_core_moved]
  have hk : m.secondaryProjection.ker ≤ pCore 2 (secondary c) :=
    le_sSup ⟨inferInstance,m.secondaryProjection_kernel⟩
  have hi := congrArg (comap m.secondaryProjection) he
  rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hk] at hi
  have hG := congrArg (map (secondary c).subtype) hi
  simp only [C,Subgroup.map_sup,map_commutator,←MonoidHom.range_eq_map,range_subtype] at hG
  have hker : m.secondaryProjection.ker.map (secondary c).subtype ≤ Q c := by
    apply map_le_iff_le_comap.mpr
    rw [m.secondaryProjection_ker,hcore]
    exact le_rfl
  change ⁅(secondary c).pCoreIn 2,secondary c⁆ ⊔
    m.secondaryProjection.ker.map (secondary c).subtype = (secondary c).pCoreIn 2 at hG
  apply le_antisymm
  · exact sup_le_sup_left (le_sup_left.trans hG.le) _
  · exact sup_le le_sup_left
      (hG.ge.trans (sup_le le_sup_right (hker.trans le_sup_left)))

/-- The only remaining ambient generation premise is coverage of the whole R₂. -/
theorem radical_generation_iff_coverage (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) (hcore : Q c = (K c).pCoreIn 2) :
    Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c ↔
      R₂ c ≤ Q c ⊔ (secondary c).pCoreIn 2 := by
  constructor
  · intro he
    rw [←he]
    exact sup_le_sup_left (radical_secondary_commutator_le_core D) _
  · intro hcover
    apply le_antisymm
    · exact sup_le (core_le_radical c)
        (le_normalizer_iff_commutator_le_left.mp
          ((le_sup_left : secondary c ≤ secondary c ⊔ S c).trans
            ((secondary c ⊔ S c).le_normalizer.trans
              (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))))
    · apply hcover.trans
      rw [←m.secondary_core_generation hn hcore]
      exact sup_le_sup_left (commutator_mono (secondary_core_le_radical D) le_rfl) _

/-- Actual corrected-sieve application, retaining all images under s.action.
Coverage remains an explicit earlier-source premise owned by this task. -/
theorem action_generation_of_coverage (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) (s : SecondarySourceData c n)
    (hcover : R₂ c ≤ Q c ⊔ (secondary c).pCoreIn 2) :
    ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
      ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
        ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
      ((R₂ c).subgroupOf (rootNormalizer c)).map s.action :=
  s.action_generation_of_generation
    ((m.radical_generation_iff_coverage hn D s.core_eq_original).mpr hcover)

end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
