module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Frame
public import Theory.SpecificGroups.AlternatingSix.PGLNineOvergroups.CentralLift

/-!
# Proper overgroups in the source J₂ vertex normalizer

For the literal M = N_G(X) and C = C_G(X), the order-three subgroup X
lies in C and is the kernel of the actual quotient map. Perfectness of C
therefore ensures that a proper subgroup of M has proper image in M/X.
The genuine PGL₂(9) theorem puts every such image containing an A₅ inside
PSL₂(9); compatibility of the image of C lifts this containment to C.

`edgeFrame_proper_overgroups` has precisely the quantifiers of `hovergroups`
in `SourceLocal.localDataOfCalculations`, for the actual edge fixer.
The source three-local calculation still supplies perfectness of C, the
isomorphism M/X ≃ PGL₂(9), and its compatible image of C. Quasisimplicity
and the central A₆ quotient supply stronger structure than this step needs.
No maximality or overgroup premise is assumed.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, printed p.266.
-/

@[expose] public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open Atlas.Comparisons.Exceptional GorensteinWalter
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.Overgroups
variable {G : Type*} [Group G] [Finite G]

/-- The literal normalizer quotient map in the chosen genuine PGL₂(9) coordinates. -/
abbrev vertexModelMap (D : Seed G)
    (e : (normalizer (D.X : Set G) ⧸ D.X.subgroupOf (normalizer (D.X : Set G))) ≃*
      PGL2 Nine.F) : normalizer (D.X : Set G) →* PGL2 Nine.F :=
  e.toMonoidHom.comp (QuotientGroup.mk' (D.X.subgroupOf (normalizer (D.X : Set G))))

/-- Changing the quotient coordinates preserves the embedded order-three kernel. -/
theorem vertexModelMap_ker (D : Seed G)
    (e : (normalizer (D.X : Set G) ⧸ D.X.subgroupOf (normalizer (D.X : Set G))) ≃*
      PGL2 Nine.F) : (vertexModelMap D e).ker = D.X.subgroupOf (normalizer (D.X : Set G)) := by
  exact (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans
    (QuotientGroup.ker_mk' _)

/-- The proper-overgroup calculation for every actual A₅ in the vertex normalizer. -/
theorem proper_overgroup_le_centralizer (D : Seed G)
    (hperfect : Group.IsPerfect (centralizer (D.X : Set G)))
    (e : (normalizer (D.X : Set G) ⧸ D.X.subgroupOf (normalizer (D.X : Set G))) ≃*
      PGL2 Nine.F)
    (himage : ((centralizer (D.X : Set G)).subgroupOf (normalizer (D.X : Set G))).map
        (vertexModelMap D e) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range)
    (F U : Subgroup G) (he : Nonempty (F ≃* alternatingGroup (Fin 5)))
    (hFM : F ≤ normalizer (D.X : Set G)) (hFU : F ≤ U)
    (hUM : U ≤ normalizer (D.X : Set G)) (hU : U ≠ normalizer (D.X : Set G)) :
    U ≤ centralizer (D.X : Set G) := by
  let M := normalizer (D.X : Set G)
  let C := centralizer (D.X : Set G)
  have hCM : C ≤ M := Subgroup.centralizer_le_normalizer _
  let : Group.IsPerfect C := hperfect
  let : Group.IsPerfect (C.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hCM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hCM).symm.surjective
  let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  have hXC : D.X ≤ C := D.X.le_centralizer
  have hker : (vertexModelMap D e).ker ≤ C.subgroupOf M := by
    rw [vertexModelMap_ker]
    intro x hx
    exact hXC hx
  have hk : Nat.card (vertexModelMap D e).ker ≤ 4 := by
    rw [vertexModelMap_ker, Nat.card_congr (subgroupOfEquivOfLe D.X.le_normalizer).toEquiv,
      D.card_X]
    decide
  have hproper : U.subgroupOf M ≠ ⊤ := by
    intro ht
    exact hU (le_antisymm hUM (subgroupOf_eq_top.mp ht))
  have hFM' : Nonempty (F.subgroupOf M ≃* alternatingGroup (Fin 5)) :=
    ⟨(subgroupOfEquivOfLe hFM).trans he.some⟩
  have ht : U.subgroupOf M ≤ C.subgroupOf M :=
    AlternatingSix.PGLNineOvergroups.proper_overgroup_le_of_small_kernel
      (vertexModelMap D e) (C.subgroupOf M) hker hk himage
      (F.subgroupOf M) (U.subgroupOf M) hFM' (fun _ hx => hFU hx) hproper
  intro x hx
  exact ht (show (⟨x, hUM hx⟩ : M) ∈ U.subgroupOf M from hx)

/-- The exact `hovergroups` input for the source edge-frame consumer. -/
theorem edgeFrame_proper_overgroups {D : Seed G} (frame : EdgeFrame D)
    (he : Nonempty (edgeFixer G D.base frame.y ≃* alternatingGroup (Fin 5)))
    (hperfect : Group.IsPerfect (centralizer (D.X : Set G)))
    (e : (normalizer (D.X : Set G) ⧸ D.X.subgroupOf (normalizer (D.X : Set G))) ≃*
      PGL2 Nine.F)
    (himage : ((centralizer (D.X : Set G)).subgroupOf (normalizer (D.X : Set G))).map
        (vertexModelMap D e) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range) :
    ∀ U : Subgroup G, edgeFixer G D.base frame.y ≤ U →
      U ≤ normalizer (D.X : Set G) → U ≠ normalizer (D.X : Set G) →
      U ≤ centralizer (D.X : Set G) := by
  intro U hFU hUM hU
  apply proper_overgroup_le_centralizer D hperfect e himage
    (edgeFixer G D.base frame.y) U he _ hFU hUM hU
  change MulAction.stabilizer G D.base ⊓ MulAction.stabilizer G frame.y ≤ _
  rw [D.stabilizer_eq_normalizer D.base]
  exact inf_le_left

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.Overgroups
