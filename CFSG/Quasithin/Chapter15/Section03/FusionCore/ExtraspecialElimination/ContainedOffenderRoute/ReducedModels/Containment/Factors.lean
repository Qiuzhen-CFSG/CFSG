module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment.Setup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.LieBorels
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.FactorControl
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.SelfNormalizing

/-!
# All conjugate components for the contained-offender Borel

These adapters retain the exact star projection and every T-conjugate
component. The intrinsic quotient and commuting-family normalizer theorems
from ModelSelection.Transport and LieBorels apply using the relative
normality and quasisimplicity already derived from Input. No solvability
of M ∩ H or generation of the first offender span by components is used.

The actual Sylow intersection maps to a Sylow subgroup of the whole star
closure. Its normalizer is solvable by the concrete model calculations.
At a binary model it is self-normalizing. Both conclusions lift through
the original two-core kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1144, proof of 15.3.49(k). The transport proofs follow the existing
ModelSelection.Transport and LieBorels arguments with their weaker inputs.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment
open Subgroup ComponentReduction ModelReduction BorelInner
open AutomorphismCollapse ModelSelection
open CFSG.Quasithin.Chapter1
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z E upper : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

open LieBorels (factor)

theorem closure_inter_sylow :
    IsSylowIn 2 ((T : Subgroup G) ⊓ localSpan L T) (localSpan L T) ∧
    IsSylowIn 2 (starImage H ((T : Subgroup G) ⊓ localSpan L T))
      (starImage H (localSpan L T)) := by
  have hs := CFSG.Quasithin.Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    d.sylowIn d.closure_le d.closure_normal.isSubnormal
  exact ⟨hs, BinaryModels.starImage_isSylowIn _ _ _
    (inf_le_right.trans d.closure_le) d.closure_le hs⟩

theorem closure_projection_ker_le_inter :
    (starProjection H (localSpan L T) d.closure_le).ker ≤
      ((T : Subgroup G) ⊓ localSpan L T).subgroupOf (localSpan L T) := by
  intro x hx
  have hx' : (⟨x, d.closure_le x.property⟩ : H) ∈ pCore 2 H :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
  exact ⟨pCore_isPGroup.le_sylow_of_normal (T.subtype d.t_le) hx', x.property⟩

/-- Solvability of the intrinsic star normalizer is equivalent to solvability
of the actual relative normalizer in G. -/
theorem borel_isSolvable_iff :
    Group.IsSolvable (localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) : Subgroup G) ↔
    Group.IsSolvable (normalizer
      ((starImage H ((T : Subgroup G) ⊓ localSpan L T)).subgroupOf
        (starImage H (localSpan L T)) : Set (starImage H (localSpan L T)))) := by
  let K := localSpan L (T : Subgroup G)
  let D := (T : Subgroup G) ⊓ K
  let B := K ⊓ normalizer (D : Set G)
  let f := starProjection H K d.closure_le
  let N := normalizer ((starImage H D).subgroupOf (starImage H K) : Set (starImage H K))
  have he : N.comap f = B.subgroupOf K :=
    starProjection_normalizer_comap H K D d.closure_le inf_le_right
      (closure_projection_ker_le_inter d)
  have hm : (B.subgroupOf K).map f = N :=
    starProjection_normalizer_map H K D d.closure_le inf_le_right
      (closure_projection_ker_le_inter d)
  let e := subgroupOfEquivOfLe (show B ≤ K from inf_le_left)
  constructor
  · intro hB
    let _ := hB
    let : Group.IsSolvable (B.subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    change Group.IsSolvable N
    rw [← hm]
    exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  · intro hN
    let _ := hN
    have hk : IsPGroup 2 f.ker := by
      rw [starProjection_ker H K d.closure_le d.closure_normal.isSubnormal]
      exact pCore_isPGroup
    let : Group.IsNilpotent f.ker := hk.isNilpotent
    let : Group.IsSolvable (B.subgroupOf K) :=
      he ▸ isSolvable_comap_of_solvable_ker f N
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem star_isCComponent : (starImage H L).IsCComponent := by
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact d.component_in_H.map_quotient (pCore 2 H)

noncomputable def conjugateStarEquiv (t : T) :
    starImage H L ≃* starImage H (L.map (MulAut.conj (t : G)).toMonoidHom) := by
  rw [starImage_map_conj H L d.l_le ⟨t, d.t_le t.property⟩]
  exact (starImage H L).equivMapOfInjective
    (MulAut.conj (QuotientGroup.mk' (pCore 2 H) ⟨t, d.t_le t.property⟩)).toMonoidHom
    (MulAut.conj _).injective

theorem conjugate_star_isCComponent (t : T) :
    (starImage H (L.map (MulAut.conj (t : G)).toMonoidHom)).IsCComponent := by
  rw [starImage_map_conj H L d.l_le ⟨t, d.t_le t.property⟩]
  exact (star_isCComponent d).map_equiv (MulAut.conj _)

omit d [Finite G] in
private theorem localSpan_eq_iSup (L T : Subgroup G) :
    localSpan L T = ⨆ t : T, L.map (MulAut.conj (t : G)).toMonoidHom := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro x ⟨t, ht, l, hl, rfl⟩
    exact (le_iSup (fun t : T => L.map (MulAut.conj (t : G)).toMonoidHom) ⟨t, ht⟩)
      ⟨l, hl, rfl⟩
  · apply iSup_le
    intro t x hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact subset_closure ⟨t, t.property, l, hl, rfl⟩

theorem conjugateFactors_properties (C : Subgroup (H ⧸ pCore 2 H))
    (hC : C ∈ conjugateFactors H L T) :
    C.IsCComponent ∧ C ≤ starImage H (localSpan L T) ∧
      starImage H Y0 ≤ normalizer (C : Set (H ⧸ pCore 2 H)) ∧
      Nonempty (starImage H L ≃* C) := by
  obtain ⟨t, rfl⟩ := mem_conjugateFactors.mp hC
  refine ⟨conjugate_star_isCComponent d t, ?_,
    conjugate_star_normalized d t t.property, ⟨conjugateStarEquiv d t⟩⟩
  apply map_mono (comap_mono ?_)
  intro x hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact subset_closure ⟨t, t.property, l, hl, rfl⟩

/-- The finite family generates the whole star closure, including every orbit. -/
theorem conjugateFactors_sup :
    (conjugateFactors H L T).sup id = starImage H (localSpan L T) := by
  have hCH (t : T) : L.map (MulAut.conj (t : G)).toMonoidHom ≤ H := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact d.closure_le (subset_closure ⟨t, t.property, l, hl, rfl⟩)
  have hi : (localSpan L T).subgroupOf H =
      ⨆ t : T, (L.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le d.closure_le, Subgroup.map_iSup]
    simp_rw [map_subgroupOf_eq_of_le (hCH _)]
    exact localSpan_eq_iSup L T
  have hstar : starImage H (localSpan L T) =
      ⨆ t : T, starImage H (L.map (MulAut.conj (t : G)).toMonoidHom) := by
    unfold starImage
    rw [hi, Subgroup.map_iSup]
  apply le_antisymm
  · exact Finset.sup_le fun C hC => (conjugateFactors_properties d C hC).2.1
  · rw [hstar]
    apply iSup_le
    intro t
    exact Finset.le_sup (f := id) (mem_conjugateFactors.mpr ⟨t, rfl⟩)

/-- Once classification establishes quasisimplicity, all distinct members
of the actual factor family commute. -/
theorem conjugateFactors_commute
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (C D : Subgroup (H ⧸ pCore 2 H))
    (hC : C ∈ conjugateFactors H L T) (hD : D ∈ conjugateFactors H L T)
    (hne : C ≠ D) : C ≤ centralizer (D : Set (H ⧸ pCore 2 H)) := by
  let _ := hq
  obtain ⟨hCc, _, _, ⟨eC⟩⟩ := conjugateFactors_properties d C hC
  obtain ⟨hDc, _, _, ⟨eD⟩⟩ := conjugateFactors_properties d D hD
  have hC' : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) C :=
    ⟨hCc.subnormal, Theory.GroupTheory.IsQuasisimple.of_mulEquiv eC⟩
  have hD' : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) D :=
    ⟨hDc.subnormal, Theory.GroupTheory.IsQuasisimple.of_mulEquiv eD⟩
  exact commutator_eq_bot_iff_le_centralizer.mp (hC'.commutator_eq_bot_of_ne hD' hne)


noncomputable def factorEquiv (C : ↥(conjugateFactors H L T)) :
    starImage H L ≃* factor C :=
  (conjugateFactors_properties d C.val C.property).2.2.2.some.trans
    (subgroupOfEquivOfLe (conjugateFactors_properties d C.val C.property).2.1).symm


/-- The intrinsic factors generate all of L₀*, without an orbit-size assumption. -/
theorem factor_sup : (⨆ C : ↥(conjugateFactors H L T), factor C) = ⊤ := by
  apply map_injective (starImage H (localSpan L T)).subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
  simp_rw [factor, map_subgroupOf_eq_of_le
    (conjugateFactors_properties d _ (Subtype.property _)).2.1]
  rw [← conjugateFactors_sup d, Finset.sup_eq_iSup, iSup_subtype]
  rfl

/-- Quasisimplicity makes distinct intrinsic factors commute. -/
theorem factor_commute (hq : Theory.GroupTheory.IsQuasisimple (starImage H L)) :
    Pairwise fun C D : ↥(conjugateFactors H L T) =>
      factor C ≤ centralizer (factor D : Set (starImage H (localSpan L T))) := by
  intro C D hne x hx y hy
  apply Subtype.ext
  exact conjugateFactors_commute d hq C.val D.val C.property D.property
    (fun h => hne (Subtype.ext h)) hx y.val hy

/-- Every factor retains the same concrete Lie alternative and field exponent. -/
theorem factor_lieModel {e : ℕ} (h : LieComponentModel (starImage H L) e)
    (C : ↥(conjugateFactors H L T)) : LieComponentModel (factor C) e :=
  lieModel_transport (factorEquiv d C) h

/-- A Sylow marking for the actual star image of T ∩ L₀. -/
noncomputable def closureSylow : Sylow 2 (starImage H (localSpan L T)) :=
  (closure_inter_sylow d).2.choose

/-- The marking has exactly the required intrinsic subgroup as carrier. -/
theorem closureSylow_coe :
    (closureSylow d : Subgroup (starImage H (localSpan L T))) =
      (starImage H ((T : Subgroup G) ⊓ localSpan L T)).subgroupOf
        (starImage H (localSpan L T)) := by
  apply map_injective (starImage H (localSpan L T)).subtype_injective
  have hle : starImage H ((T : Subgroup G) ⊓ localSpan L T) ≤
      starImage H (localSpan L T) := map_mono (comap_mono inf_le_right)
  rw [map_subgroupOf_eq_of_le hle]
  exact (closure_inter_sylow d).2.choose_spec

/-- The original relative normalizer is solvable exactly when this Sylow normalizer is. -/
theorem borel_isSolvable_iff_closureSylow :
    Group.IsSolvable (localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) : Subgroup G) ↔
      Group.IsSolvable (normalizer
        (closureSylow d : Set (starImage H (localSpan L T)))) := by
  change _ ↔ Group.IsSolvable (normalizer
    ((closureSylow d : Subgroup (starImage H (localSpan L T))) :
      Set (starImage H (localSpan L T))))
  rw [closureSylow_coe]
  exact borel_isSolvable_iff d


theorem closure_normalizer_isSolvable {e : ℕ}
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hmodel : LieComponentModel (starImage H L) e)
    (S : Sylow 2 (starImage H (localSpan L T))) :
    Group.IsSolvable (normalizer (S : Set (starImage H (localSpan L T)))) := by
  exact Sylow.isSolvable_normalizer_of_commuting_family factor
    (factor_commute d hq) (factor_sup d)
    (fun C P => LieBorels.model_normalizer_isSolvable (factor_lieModel d hmodel C) P) S

/-- The Borel needed in 15.3.49(k) is the solvable relative normalizer of
the actual Sylow intersection in L₀ = ⟨L^T⟩. The classification inputs
are discharged by the containment assembly using `Input.component_sections`. -/
theorem borel_isSolvable {e : ℕ}
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hmodel : LieComponentModel (starImage H L) e) :
    Group.IsSolvable (localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) : Subgroup G) :=
  (borel_isSolvable_iff_closureSylow d).mpr
    (closure_normalizer_isSolvable d hq hmodel (closureSylow d))


theorem borel_eq_of_component_self_normalizing
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hN : ∀ P : Sylow 2 (starImage H L), normalizer (P : Set (starImage H L)) = P) :
    relativeBorel L T = sylowIntersection L T := by
  classical
  let _ := Fintype.ofFinite ↥(conjugateFactors H L T)
  have hf (C : ↥(conjugateFactors H L T)) (P : Sylow 2 (factor C)) :
      normalizer (P : Set (factor C)) = P :=
    Sylow.self_normalizing_of_surjective (factorEquiv d C).toMonoidHom
      (factorEquiv d C).surjective hN P
  have hn := Sylow.self_normalizing_of_commuting_family
    (factor (H := H) (L := L) (T := T)) (factor_commute d hq) (factor_sup d) hf
    (closureSylow d)
  change normalizer ((closureSylow d : Subgroup (starImage H (localSpan L T))) :
    Set (starImage H (localSpan L T))) = _ at hn
  rw [closureSylow_coe] at hn
  change normalizer ((starImage H (sylowIntersection L T)).subgroupOf
    (starImage H (localSpan L T)) : Set (starImage H (localSpan L T))) =
    (starImage H (sylowIntersection L T)).subgroupOf (starImage H (localSpan L T)) at hn
  have hi : (relativeBorel L T).subgroupOf (localSpan L T) =
      (sylowIntersection L T).subgroupOf (localSpan L T) := by
    unfold relativeBorel
    rw [← starProjection_normalizer_comap H (localSpan L T) (sylowIntersection L T)
      d.closure_le inf_le_right (closure_projection_ker_le_inter d), hn,
      ← starProjection_map H (localSpan L T) (sylowIntersection L T) d.closure_le inf_le_right]
    exact comap_map_eq_self (closure_projection_ker_le_inter d)
  have he := congrArg (Subgroup.map (localSpan L T).subtype) hi
  simpa only [map_subgroupOf_eq_of_le (show relativeBorel L T ≤ localSpan L T from inf_le_left),
    map_subgroupOf_eq_of_le (show sylowIntersection L T ≤ localSpan L T from inf_le_right)] using he


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment
