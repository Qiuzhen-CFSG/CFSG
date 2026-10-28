module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.SolvableResidual.PrimeTo
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic

/-!
# Short groups acting on an elementary normal subgroup

A short subgroup normalized by a normal elementary two-subgroup U either
centralizes U or has its entire commutator layer inside U. In the latter
case that layer is killed by the action on U, so a nontrivial perfect action
image is quasisimple. Such an image cannot have characteristic two.

Apply this to the solvable residual of a full parabolic preimage in the
literal quotient by C(U). The model embedding is retained, and the action
kernel is allowed to have an odd central part. This is the two-layer
nonblock step in Aschbacher--Smith 15.1.20(2), printed p.1095, using
C.1.7--8, printed p.123. The classical parabolic applications are in
Chapter15's constrained catalogue.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- A nontrivial perfect characteristic-two image on an elementary normal
module cannot arise from a short subgroup normalized by that module. -/
theorem not_isShort_of_characteristicTwo_action_image
    (U K : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUK : U ≤ normalizer (K : Set G)) (f : G →* D)
    (hker : f.ker = centralizer (U : Set G))
    (hne : K.map f ≠ ⊥) [Group.IsPerfect (K.map f)]
    (hf : generalizedFitting (K.map f) = pCore 2 (K.map f)) : ¬ IsShort K := by
  intro hs
  let : Finite (K.map f) := Finite.of_surjective _ (f.subgroupMap_surjective K)
  let : Nontrivial (K.map f) := (nontrivial_iff_ne_bot _).mpr hne
  have hblock : (blockU K).map K.subtype ≤ U := by
    rcases hs.blockU_le_or_centralizes_of_normalizing_twoGroup
      (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal hUK with hh | hh
    · exact hh
    · have hh := le_centralizer_iff.mp hh
      exact (hne (by rw [Subgroup.map_eq_bot_iff,hker]; exact hh)).elim
  have hk : blockU K ≤ (f.subgroupMap K).ker := by
    intro x hx
    apply Subtype.ext
    change f x = 1
    exact (show (x : G) ∈ f.ker from hker.symm ▸ U.le_centralizer
      (hblock (mem_map_of_mem K.subtype hx)))
  let q := QuotientGroup.lift (blockU K) (f.subgroupMap K) hk
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ (f.subgroupMap_surjective K) _
  rcases hs.quotient_blockU with hquasi | hthree
  · let := hquasi
    let : IsQuasisimple (K.map f) := IsQuasisimple.of_surjective q hq
    have hc : (⊤ : Subgroup (K.map f)) ≤ pCore 2 (K.map f) := by
      apply ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf).trans'
      exact le_centralizer_iff.mpr ((IsQuasisimple.pCore_le_center 2).trans
        (by intro x hx; exact mem_centralizer_iff.mpr fun y _ => mem_center_iff.mp hx y))
    have hp : IsPGroup 2 (K.map f) :=
      (show IsPGroup 2 (⊤ : Subgroup (K.map f)) from top_le_iff.mp hc ▸ pCore_isPGroup).of_equiv topEquiv
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  · let : IsCyclic (K ⧸ blockU K) := isCyclic_of_prime_card hthree
    let : Group.IsSolvable (K.map f) := Group.isSolvable_of_surjective hq
    exact Group.IsPerfect.not_isSolvable (K.map f) inferInstance

/-- The full preimage of a parabolic has a nonshort solvable residual if
its nontrivial residual image has characteristic two. -/
theorem not_isShort_residual_preimage
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (f : G →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (P : Subgroup D)
    (hne : (solvableResidual P).map P.subtype ≠ ⊥)
    (hfit : generalizedFitting ((solvableResidual P).map P.subtype) =
      pCore 2 ((solvableResidual P).map P.subtype)) :
    ¬ IsShort (solvableResidual (P.comap f)) := by
  let A := P.comap f
  let K := (solvableResidual A).map A.subtype
  have hUA : U ≤ A := (show U ≤ f.ker from hker.symm ▸ U.le_centralizer).trans
    (MonoidHom.ker_le_comap f P)
  have hUK : U ≤ normalizer (K : Set G) := (hUA.trans A.le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image A (solvableResidual A))
  have he : K.map f = (solvableResidual P).map P.subtype :=
    map_solvableResidual_comap f hf P
  let : Finite D := Finite.of_surjective f hf
  let : Group.IsPerfect (K.map f) := by rw [he]; exact Group.IsPerfect.map P.subtype
  have hn := not_isShort_of_characteristicTwo_action_image U K hUK f hker
    (he.symm ▸ hne) (he.symm ▸ hfit)
  intro hs
  exact hn (RankOne.Solvable.isShort_of_equiv
    ((solvableResidual A).equivMapOfInjective A.subtype A.subtype_injective) hs)

/-- The model embedding and quotient map determine the actual residual.
No two-group or centrality assumption is imposed on the action kernel. -/
theorem not_isShort_residual_preimage_of_model
    {E : Type*} [Group E] [Finite E]
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (f : G →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G))
    (j : E →* D) (hj : Function.Injective j) (P B : Subgroup E)
    (hres : (solvableResidual P).map P.subtype = B)
    (hne : B ≠ ⊥) (hfit : generalizedFitting B = pCore 2 B) :
    ¬ IsShort (solvableResidual ((P.map j).comap f)) := by
  let : Finite D := Finite.of_surjective f hf
  have he : (solvableResidual (P.map j)).map (P.map j).subtype = B.map j := by
    rw [←map_embedded_solvableResidual_of_hom,hres]
  apply not_isShort_residual_preimage U f hf hker (P.map j)
  · rw [he]
    exact fun hh => hne ((map_eq_bot_iff_of_injective _ hj).mp hh)
  · rw [he]
    let e := B.equivMapOfInjective j hj
    exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit))
end CFSG.Quasithin.ChapterC

