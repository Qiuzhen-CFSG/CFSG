module
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist
public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer

/-!
# Exact inertia of a natural A₆ central cover

A normalizing operator on a seed acts on its actual central quotient.
The linear normalizer of natural A₆ is S₆, so stabilization implies a
natural component automorphism. Conversely, the S₆ intertwiner and
homogeneous uniqueness preserve the seed itself, including its fixed
kernel. Inertia is exactly the preimage of natural S₆ in Aut(A₆).
Its index is two whenever the original actor moves the seed.

Source: Aschbacher--Smith A.1.40--42 and14.6.22,
printed pp.31--32 and1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K T : Subgroup G}
    {I : Submodule (ZMod 2) V}

/-- Stabilizing a seed with a natural A₆ central quotient induces a
natural S₆ automorphism; the covering kernel is retained. -/
theorem IsIrrPlusWith.alternating_six_natural_of_map_eq
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryAlternatingSixNaturalNormalizer.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryAlternatingSixNaturalNormalizer.action (j k) (l v))
    (ht : I.map (ρ t.val) = I) :
    MulAut.congr j (K.normalizerMonoidHom ⟨t,hI.normalizes t.property⟩) ∈
      AlternatingSix.ShadowLocal.natural := by
  let S := quotientImage ρ K I hI.invariant
  let σ := S.toRepresentation
  let θ := normalizerQuotientRepresentation ρ K
  let tN : normalizer (K : Set G) := ⟨t,hI.normalizes t.property⟩
  let n := K.normalizerMonoidHom tN
  have hS : S.toSubmodule.map (θ tN) = S.toSubmodule := by
    change (I.map (fixedSpace ρ K).mkQ).map (normalizerQuotientRepresentation ρ K tN) =
      I.map (fixedSpace ρ K).mkQ
    rw [←quotientImage_map_normalizer ρ K I tN]
    exact congrArg (Submodule.map (fixedSpace ρ K).mkQ) ht
  let a := (Submodule.equivMapOfInjective (θ tN) (θ.apply_bijective tN).1 S.toSubmodule).trans
    (LinearEquiv.ofEq _ _ hS)
  have ha (v : S.toSubmodule) : (a v : V ⧸ fixedSpace ρ K) = θ tN v := rfl
  have hcomm (k : K) (w : V ⧸ fixedSpace ρ K) :
      θ tN (fixedQuotientRepresentation ρ K k w) =
        fixedQuotientRepresentation ρ K (n k) (θ tN w) := by
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
      change (fixedSpace ρ K).mkQ (ρ t.val (ρ k.val w)) =
        (fixedSpace ρ K).mkQ (ρ (n k).val (ρ t.val w))
      simp only [n,Subgroup.normalizerMonoidHom_apply_apply_coe,tN,
        ←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have heq (k : K) (v : S.toSubmodule) : a (σ k v) = σ (n k) (a v) := by
    apply Subtype.ext
    change (a (σ k v)).val = fixedQuotientRepresentation ρ K (n k) (a v).val
    rw [ha,ha]
    exact hcomm k v.val
  let q := centralQuotientImageEquiv ρ K I
  let b : S.toSubmodule ≃ₗ[ZMod 2] BinaryAlternatingSixNaturalNormalizer.Vector := q.symm.trans l
  have hb (k : K) (v : S.toSubmodule) : b (σ k v) = BinaryAlternatingSixNaturalNormalizer.action (j k) (b v) := by
    obtain ⟨w,rfl⟩ := q.surjective v
    rw [←centralQuotientImageEquiv_equivariant ρ K I hI.invariant]
    change l (q.symm (q (centralQuotientRepresentation ρ K I hI.invariant k w))) =
      BinaryAlternatingSixNaturalNormalizer.action (j k) (l (q.symm (q w)))
    simpa only [q.symm_apply_apply] using he k w
  let α := (MulAut.congr j) n
  let c := b.symm.trans (a.trans b)
  have hc (g : alternatingGroup (Fin 6)) (v : BinaryAlternatingSixNaturalNormalizer.Vector) :
      c (BinaryAlternatingSixNaturalNormalizer.action g v) = BinaryAlternatingSixNaturalNormalizer.action (α g) (c v) := by
    obtain ⟨k,rfl⟩ := j.surjective g
    obtain ⟨w,rfl⟩ := b.surjective v
    change b (a (b.symm (BinaryAlternatingSixNaturalNormalizer.action (j k) (b w)))) =
      BinaryAlternatingSixNaturalNormalizer.action (α (j k)) (b (a (b.symm (b w))))
    rw [←hb,b.symm_apply_apply,b.symm_apply_apply,heq,hb]
    congr 2
    simp only [α,MulAut.congr_apply,MulEquiv.trans_apply,j.symm_apply_apply]
  exact BinaryAlternatingSixNaturalNormalizer.natural_of_intertwiner α c hc

theorem IsIrrPlusWith.alternating_six_map_eq_of_natural
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryAlternatingSixNaturalNormalizer.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryAlternatingSixNaturalNormalizer.action (j k) (l v))
    (ht : MulAut.congr j (K.normalizerMonoidHom ⟨t,hI.normalizes t.property⟩) ∈
      AlternatingSix.ShadowLocal.natural) : I.map (ρ t.val) = I := by
  let φ : T →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr j).toMonoidHom.comp
      (K.normalizerMonoidHom.comp (inclusion hI.normalizes))
  have hn : φ t⁻¹ ∈ AlternatingSix.ShadowLocal.natural := by
    rw [map_inv]
    exact AlternatingSix.ShadowLocal.natural.inv_mem ht
  obtain ⟨s,hs⟩ := hn
  let S := quotientImage ρ K I hI.invariant
  let q := centralQuotientImageEquiv ρ K I
  let b : S.toSubmodule ≃ₗ[ZMod 2] BinaryAlternatingSixNaturalNormalizer.Vector := q.symm.trans l
  have hb (k : K) (v : S.toSubmodule) : b (S.toRepresentation k v) =
      BinaryAlternatingSixNaturalNormalizer.action (j k) (b v) := by
    obtain ⟨w,rfl⟩ := q.surjective v
    rw [←centralQuotientImageEquiv_equivariant ρ K I hI.invariant]
    change l (q.symm (q (centralQuotientRepresentation ρ K I hI.invariant k w))) =
      BinaryAlternatingSixNaturalNormalizer.action (j k) (l (q.symm (q w)))
    simpa only [q.symm_apply_apply] using he k w
  let u := BinaryAlternatingSixNaturalNormalizer.naturalLinearAction s
  have hu (a : alternatingGroup (Fin 6)) (v : BinaryAlternatingSixNaturalNormalizer.Vector) :
      u (BinaryAlternatingSixNaturalNormalizer.action a v) =
        BinaryAlternatingSixNaturalNormalizer.action
          (AlternatingSix.ShadowLocal.permutationAction s a) (u v) := by
    change BinaryPermutation.naturalRepresentation (Fin 6) s
      (BinaryPermutation.naturalRepresentation (Fin 6) a.val v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (s*a.val*s⁻¹)
        (BinaryPermutation.naturalRepresentation (Fin 6) s v)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  apply hI.map_eq_of_central_twist ρ t (b.trans (u.trans b.symm))
  intro k v
  apply b.injective
  change b (b.symm (u (b (S.toRepresentation k v)))) =
    b (S.toRepresentation
      (K.normalizerMonoidHom ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩ k)
        (b.symm (u (b v))))
  rw [b.apply_symm_apply,hb,hb,b.apply_symm_apply,hu]
  congr 2
  have hh := DFunLike.congr_fun hs (j k)
  change AlternatingSix.ShadowLocal.permutationAction s (j k) =
    j (K.normalizerMonoidHom ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩ (j.symm (j k))) at hh
  simpa only [j.symm_apply_apply] using hh

/-- The inertia in the prescribed normalizing actor is the literal
preimage of the natural S₆ subgroup of Aut(A₆). -/
theorem IsIrrPlusWith.alternating_six_inertia
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryAlternatingSixNaturalNormalizer.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryAlternatingSixNaturalNormalizer.action (j k) (l v)) :
    (subspaceStabilizer ρ I).subgroupOf T =
      AlternatingSix.ShadowLocal.natural.comap ((MulAut.congr j).toMonoidHom.comp
        (K.normalizerMonoidHom.comp (inclusion hI.normalizes))) := by
  ext t
  exact (subspace_map_eq_iff ρ I t.val).symm.trans
    ⟨hI.alternating_six_natural_of_map_eq ρ t j l he,
      hI.alternating_six_map_eq_of_natural ρ t j l he⟩

/-- The natural subgroup has index two in Aut(A₆), hence a moved original
homogeneous seed has inertia of index two, even when the cover is nonsplit. -/
theorem IsIrrPlusWith.alternating_six_stabilizer_index
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryAlternatingSixNaturalNormalizer.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryAlternatingSixNaturalNormalizer.action (j k) (l v))
    (hmoved : ∃ t : T, I.map (ρ t.val) ≠ I) :
    (subspaceStabilizer ρ I).relIndex T = 2 := by
  let N := AlternatingSix.ShadowLocal.natural
  let : N.Normal := normal_of_index_eq_two
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  have hd : (subspaceStabilizer ρ I).relIndex T ∣ 2 := by
    change ((subspaceStabilizer ρ I).subgroupOf T).index ∣ 2
    rw [hI.alternating_six_inertia ρ j l he,index_comap]
    rw [← GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index]
    exact relIndex_dvd_index_of_normal _ _
  apply ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
  intro hh
  obtain ⟨t,ht⟩ := hmoved
  exact ht ((subspace_map_eq_iff ρ I t.val).mpr ((relIndex_eq_one.mp hh) t.property))

end Representation.BinaryOffender.Homogeneous
