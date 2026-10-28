module

public import Theory.GroupTheory.NoncentralChiefRefinement.Transport

/-!
# Changing the ambient group of a chief series

A group isomorphism maps the lattice of normal subgroups and each literal
relative quotient. The quotient isomorphism intertwines conjugation by an
actor with conjugation by its image, so completeness and noncentral binary
chief counts are preserved. This supplies the actor changes in the proof of
Aschbacher–Smith 14.7.70, printed p.1074.
-/

public section
noncomputable section
open Subgroup
namespace NoncentralChiefRefinement
variable {K H : Type*} [Group K] [Group H]

/-- Forward images under a genuine group isomorphism, restricted to normal nodes. -/
@[expose] def actorNormalEquiv (e : K ≃* H) : NormalNode K ≃o NormalNode H where
  toFun A := ⟨A.val.map e.toMonoidHom, A.property.map _ e.surjective⟩
  invFun A := ⟨A.val.map e.symm.toMonoidHom, A.property.map _ e.symm.surjective⟩
  left_inv A := Subtype.ext (e.mapSubgroup.left_inv A.val)
  right_inv A := Subtype.ext (e.mapSubgroup.right_inv A.val)
  map_rel_iff' := e.mapSubgroup.map_rel_iff

private def actorSectionHom (e : K ≃* H) (A B : NormalNode K) :
    B.val →* Section (actorNormalEquiv e A) (actorNormalEquiv e B) :=
  (QuotientGroup.mk' _).comp (e.toMonoidHom.subgroupMap B.val)

private theorem actorSectionHom_surjective (e : K ≃* H) (A B : NormalNode K) :
    Function.Surjective (actorSectionHom e A B) :=
  (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective _ _)

private theorem actorSectionHom_ker (e : K ≃* H) (A B : NormalNode K) :
    A.val.subgroupOf B.val = (actorSectionHom e A B).ker := by
  ext b
  rw [MonoidHom.mem_ker]
  change (b : K) ∈ A.val ↔ QuotientGroup.mk'
    ((actorNormalEquiv e A).val.subgroupOf (actorNormalEquiv e B).val)
    (e.toMonoidHom.subgroupMap B.val b) = 1
  exact (Subgroup.mem_map_iff_mem e.injective).symm.trans
    (QuotientGroup.eq_one_iff
      (N := (actorNormalEquiv e A).val.subgroupOf (actorNormalEquiv e B).val)
      (e.toMonoidHom.subgroupMap B.val b)).symm

/-- The original and image relative sections are isomorphic via the literal map. -/
def actorSectionEquiv (e : K ≃* H) (A B : NormalNode K) :
    Section A B ≃* Section (actorNormalEquiv e A) (actorNormalEquiv e B) :=
  QuotientGroup.liftEquiv _ (actorSectionHom_surjective e A B) (actorSectionHom_ker e A B)

@[simp] theorem actorSectionEquiv_mk (e : K ≃* H) (A B : NormalNode K) (b : B.val) :
    actorSectionEquiv e A B (QuotientGroup.mk' _ b) =
      QuotientGroup.mk' ((actorNormalEquiv e A).val.subgroupOf (actorNormalEquiv e B).val)
        (e.toMonoidHom.subgroupMap B.val b) :=
  QuotientGroup.liftEquiv_mk _ (actorSectionHom_surjective e A B) (actorSectionHom_ker e A B) b

/-- The acting element is transported by the same group isomorphism. -/
theorem actorSectionEquiv_equivariant (e : K ≃* H) (A B : NormalNode K)
    (k : K) (x : Section A B) :
    actorSectionEquiv e A B (sectionAction A B k x) =
      sectionAction (actorNormalEquiv e A) (actorNormalEquiv e B) (e k)
        (actorSectionEquiv e A B x) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
  rw [sectionAction_mk, actorSectionEquiv_mk, actorSectionEquiv_mk]
  change QuotientGroup.mk' ((actorNormalEquiv e A).val.subgroupOf (actorNormalEquiv e B).val)
    (e.toMonoidHom.subgroupMap B.val (MulAut.conjNormal k b)) =
    QuotientGroup.mk' ((actorNormalEquiv e A).val.subgroupOf (actorNormalEquiv e B).val)
      (MulAut.conjNormal (e k) (e.toMonoidHom.subgroupMap B.val b))
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  change e (k * (b : K) * k⁻¹) = e k * e b * (e k)⁻¹
  simp only [map_mul, map_inv]

/-- Centrality is preserved, with surjectivity used to cover all image actors. -/
theorem actor_isCentral_iff (e : K ≃* H) (A B : NormalNode K) :
    IsCentral (actorNormalEquiv e A) (actorNormalEquiv e B) ↔ IsCentral A B := by
  rw [isCentral_iff_action, isCentral_iff_action]
  constructor
  · intro h k x
    apply (actorSectionEquiv e A B).injective
    rw [actorSectionEquiv_equivariant, h]
  · intro h k x
    obtain ⟨k, rfl⟩ := e.surjective k
    obtain ⟨x, rfl⟩ := (actorSectionEquiv e A B).surjective x
    rw [← actorSectionEquiv_equivariant, h]

/-- Both the prime-group test and noncentrality use the actual quotient map. -/
theorem actor_isNoncentralTwo_iff (e : K ≃* H) (A B : NormalNode K) :
    IsNoncentralTwo (actorNormalEquiv e A) (actorNormalEquiv e B) ↔ IsNoncentralTwo A B :=
  and_congr ⟨fun h => h.of_equiv (actorSectionEquiv e A B).symm,
    fun h => h.of_equiv (actorSectionEquiv e A B)⟩
    (not_congr (actor_isCentral_iff e A B))

/-- Transport a chief series through a genuine isomorphism of its ambient actor. -/
@[expose] def ChiefSeries.mapActor (s : ChiefSeries K) (e : K ≃* H) : ChiefSeries H where
  length := s.length
  toFun i := actorNormalEquiv e (s i)
  step i := (apply_covBy_apply_iff (actorNormalEquiv e)).mpr (s.step i)

@[simp] theorem ChiefSeries.mapActor_apply (s : ChiefSeries K) (e : K ≃* H)
    (i : Fin (s.length + 1)) : s.mapActor e i = actorNormalEquiv e (s i) := rfl

@[simp] theorem ChiefSeries.mapActor_head (s : ChiefSeries K) (e : K ≃* H) :
    (s.mapActor e).head = actorNormalEquiv e s.head := rfl

@[simp] theorem ChiefSeries.mapActor_last (s : ChiefSeries K) (e : K ≃* H) :
    (s.mapActor e).last = actorNormalEquiv e s.last := rfl

/-- Complete series stay complete under the ambient isomorphism. -/
theorem ChiefSeries.mapActor_complete (s : ChiefSeries K) (e : K ≃* H)
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    (s.mapActor e).head = ⊥ ∧ (s.mapActor e).last = ⊤ := by
  simp only [mapActor_head, mapActor_last, h0, h1, OrderIso.map_bot, OrderIso.map_top, and_self]

/-- Changing the actor through an isomorphism preserves the noncentral binary count. -/
@[simp] theorem ChiefSeries.mapActor_noncentralTwoCount (s : ChiefSeries K) (e : K ≃* H) :
    (s.mapActor e).noncentralTwoCount = s.noncentralTwoCount := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun i => actor_isNoncentralTwo_iff e (s i.castSucc) (s i.succ))

end NoncentralChiefRefinement
