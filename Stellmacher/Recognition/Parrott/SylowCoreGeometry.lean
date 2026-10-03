module

public import Stellmacher.Recognition.Parrott.SylowSeedFrame
public import Stellmacher.Recognition.Parrott.CoreSquareFusion

/-!
# Geometry before choosing Parrott's core coordinates

Every noncentral square in the original core is conjugate to the marked v,
already for a frame through (10). The proof uses only a² = 1, b² = v,
and [a,w] = z, so it is available when choosing c² in (13).
The actual core and elementary subgroup memberships are retained.

`CoreCosetAlternatives` states the remaining geometric contract: the five
relations modulo the central line, with the product cd having central square.
It contains no exact equations (11)–(15) and does not assert existence.
Once these cosets are proved, multiplication of a by t and c by w,v,t,u
removes the central errors successively.

Source: Parrott (1972), pp.678–679, immediately before (4) and (13).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition
namespace ParrottSylowInitialData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

/-- The source alternatives before removal of the central factors. The
Boolean has the same meaning as in `CoreRelations`. This records the geometric
input to the coordinate adjustment, not an existence assumption. -/
public structure CoreCosetAlternatives (f : ParrottSylowInitialData n)
    (caseTwo : Bool) : Prop where
  ad_coset : Tits.parrottCommutator f.a f.d /
    (if caseTwo then f.u * n.v else f.u) ∈ zpowers z
  ac_coset : Tits.parrottCommutator f.a f.c /
    (if caseTwo then n.v else n.v * n.t) ∈ zpowers z
  c_square_coset : f.c ^ 2 /
    (if caseTwo then f.w else f.w * f.u) ∈ zpowers z
  cd_square_central : (f.c * f.d) ^ 2 ∈ zpowers z
  bc_coset : Tits.parrottCommutator f.b f.c /
    (if caseTwo then f.u * n.t else f.u * n.v) ∈ zpowers z

/-- The four core coordinates belong to the actual core. -/
public theorem generators_mem_core (f : ParrottSylowInitialData n) :
    ∀ g ∈ ({f.a, f.b, f.c, f.d} : Set G), g ∈ J := by
  intro g hg
  rw [← f.core_generators]
  exact subset_closure hg

/-- The five elementary coordinates belong to the actual derived core. -/
public theorem basis_mem_derived (f : ParrottSylowInitialData n) :
    ∀ g ∈ ({z, n.t, n.v, f.u, f.w} : Set G), g ∈ E := by
  intro g hg
  rw [← f.derived_basis]
  exact subset_closure hg

/-- The initial a is an involution or the identity by membership in F. -/
public theorem a_sq (f : ParrottSylowInitialData n) : f.a ^ 2 = 1 := by
  let : IsElementaryAbelian 2 e.F := e.elementary
  apply elemPow_eq_one_of_isElementaryAbelian (A := e.F)
  rw [← f.elementary_basis]
  exact subset_closure (by simp)

/-- The marked central involution commutes with each core element. -/
public theorem commute_z_of_mem_core (_f : ParrottSylowInitialData n)
    {g : G} (hg : g ∈ J) : Commute z g :=
  (mem_centralizer_singleton_iff.mp (map_subtype_le _ hg)).symm

/-- Every noncentral core square is fused to the marked v before any of
(11)–(15) is chosen. -/
public theorem core_square_isConj_v [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) :
    ∀ g : G, g ∈ J → g ^ 2 ∉ zpowers z → IsConj (g ^ 2) n.v :=
  parrott_core_square_isConj_v_of_initial_elements h f.a f.b f.w
    (f.generators_mem_core _ (by simp)) (f.generators_mem_core _ (by simp))
    (f.basis_mem_derived _ (by simp)) f.a_sq f.eq03_b f.eq02_aw

/-- A noncentral core square cannot be fused to z. This is the fusion
exclusion used to select the square coordinate on p.679. -/
public theorem core_square_not_isConj_z [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) {g : G}
    (hg : g ∈ J) (hs : g ^ 2 ∉ zpowers z) : ¬ IsConj z (g ^ 2) := by
  intro he
  exact n.not_isConj (he.trans (f.core_square_isConj_v h g hg hs))

end ParrottSylowInitialData
end Stellmacher.Recognition
