module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Setup

/-!
# Geometry interfaces for the noncontained binary branch

These definitions name the actual subgroups and conjugation orbit used on
printed p.1201 of Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.5.12. `FourSubgroupGeometry` specifies the intermediate local
calculation required of the S₈ × C₂ model. It asserts neither the orbit
under N_G(J(T)) nor a conclusion about that normalizer. Its construction
from the earlier inputs and the noncontainment branch is a separate
mathematical obligation.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary

open Subgroup

variable {G : Type*} [Group G]

/-- The actual orbit of A under I=N_G(J(T)), with left conjugation. -/
def thompsonNormalizerOrbit (T : Sylow 2 G) (A : Subgroup G) : Set (Subgroup G) :=
  {B | ∃ i ∈ normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G),
    A.conjBy i = B}

/-- The source's A₁=O₂(C_{L'}(z))R, as a subgroup of G. -/
def oppositeElementaryGroup (L : Subgroup G) (g z : G) (R : Subgroup G) : Subgroup G :=
  (L.conjBy g ⊓ involutionCentralizer z).pCoreIn 2 ⊔ R

/-- The concrete direct product occurring as J(T). -/
abbrev DihedralThompsonModel :=
  Multiplicative (ZMod 2) × (DihedralGroup 4 × DihedralGroup 4)

/-- The four maximal-order elementary subgroups, their relative normality,
and the ambient conjugacy needed for Burnside fusion. This is an output
contract for the local calculation, not a standing hypothesis of 16.5.12. -/
structure FourSubgroupGeometry (T : Sylow 2 G) (A A₁ B : Subgroup G) (t : G) : Prop where
  family : Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
    {A, A₁, A₁.conjBy t, B}
  distinct : [A, A₁, A₁.conjBy t, B].Nodup
  normal_in_thompson : ∀ E ∈ Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G),
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (E : Set G)
  normal_in_sylow : (T : Subgroup G) ≤ normalizer (A : Set G)
  conjugate : ∃ a : G, A.conjBy a = A₁
  switch_mem : t ∈ (T : Subgroup G)
  index_two : (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).relIndex
    (T : Subgroup G) = 2

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary
