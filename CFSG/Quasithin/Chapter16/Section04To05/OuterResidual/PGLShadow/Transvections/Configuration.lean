module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.Geometry
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Source configuration for the transvection endgame

This interface retains the ambient subgroups of Lemma 16.4.6: T_L = T ∩ L,
T_C = C_T(L), E = ⟨r,z⟩, T_E = C_T(E), V = Ω₁(T_E), and L′ = L.conjBy g.
The two elements s,t normalize T_E itself. The preceding weak-closure argument
must construct this configuration; it is an input to the conditional endgame,
not a statement of the source theorem.

The local dihedral/semidihedral input concerns T_C R, as specified by 16.4.4(1).
The other dihedral input concerns T_L R. Neither is an assertion that the
not-yet-analyzed subgroup D = T_L⟨u⟩ has a prescribed fusion or quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.4(1) and 16.4.6, printed pp.1184–1186.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
open Subgroup
variable {G : Type*} [Group G]

/-- The source inner Sylow subgroup, in the common ambient group. -/
abbrev innerSylow (T : Sylow 2 G) (L : Subgroup G) : Subgroup G := (T : Subgroup G) ⊓ L

/-- The source centralizing Sylow subgroup. -/
abbrev centralizingSylow (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ centralizer (L : Set G)

/-- The actual centralizer T_E. -/
abbrev pairCentralizer (T : Sylow 2 G) (r z : G) : Subgroup G :=
  (T : Subgroup G) ⊓ centralizer ((zpowers r ⊔ zpowers z : Subgroup G) : Set G)

/-- The source D, before proving any of its fusion, index or normality properties. -/
abbrev transferSubgroup (T : Sylow 2 G) (L : Subgroup G) (u : G) : Subgroup G :=
  innerSylow T L ⊔ zpowers u

/-- Exact local alternatives from 16.4.4(1), with actual model equivalences. -/
def DihedralOrSemidihedral (Q : Subgroup G) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (Q ≃* DihedralGroup (2 ^ n))) ∨
  (∃ (n : ℕ) (hn : 4 ≤ n), Nonempty (Q ≃* Semidihedral.StandardModel n hn))

/-- The configuration at the beginning of the final two paragraphs on p.1185.
All its weak closure and intrinsic local facts remain inputs to this helper. -/
structure Configuration [Finite G] (T : Sylow 2 G) (L R : Subgroup G)
    (g r z v u s t : G) : Prop where
  source : IntersectionSetup T z L g R
  R_eq : R = zpowers r
  eight : EightConfig (omegaOneAmbient (pairCentralizer T r z)) r z v u s t
  centralizer_abelian : IsMulCommutative (pairCentralizer T r z)
  centralizer_sylow : SylowIn (pairCentralizer T r z)
    (centralizer ((zpowers r ⊔ zpowers z : Subgroup G) : Set G))
  inner_intersection : omegaOneAmbient (pairCentralizer T r z) ⊓ L = zpowers v
  conjugate_intersection : omegaOneAmbient (pairCentralizer T r z) ⊓ L.conjBy g = zpowers u
  center : (center (T : Subgroup G)).map (T : Subgroup G).subtype = zpowers z ⊔ zpowers v
  conjugate_center : (Subgroup.center ((T : Subgroup G).conjBy g)).map
    ((T : Subgroup G).conjBy g).subtype = zpowers r ⊔ zpowers u
  t_inner : t ∈ innerSylow T L
  s_conjugate : s ∈ (T : Subgroup G).conjBy g
  t_normalizes_centralizer : t ∈ normalizer (pairCentralizer T r z : Set G)
  s_normalizes_centralizer : s ∈ normalizer (pairCentralizer T r z : Set G)
  centralizer_in_central_factor : centralizingSylow T L ⊓ involutionCentralizer r = zpowers z
  inner_dihedral : ∃ n : ℕ, 2 ≤ n ∧
    Nonempty (↥(innerSylow T L ⊔ R) ≃* DihedralGroup (2 ^ n))
  central_dihedral_or_semidihedral : DihedralOrSemidihedral (centralizingSylow T L ⊔ R)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
