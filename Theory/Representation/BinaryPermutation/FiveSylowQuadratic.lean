module

public import Theory.Representation.BinaryPermutation.FiveQuadratic
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five

/-!
# Sylow four-groups on five-point permutation quotients

The standard double transpositions lie in a Sylow two-subgroup of A₅.
Sylow conjugacy and the specified extension of the A₅ action supply their
marking for every Sylow subgroup, and quadraticity transports through that
conjugacy. Thus every such subgroup acts nonquadratically on every noncentral
permutation quotient. A contained subgroup of binary rank at least two is
already the whole Sylow four-group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed p.955, using 13.8.18(4) and 13.8.4(5),(6).
-/

public section
open Subgroup
open scoped Pointwise

namespace BinaryPermutation.FiveSylowQuadratic
open Representation.BinaryOffender
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V}

private theorem quadratic_map_conj {A : Subgroup H} (hA : IsQuadratic ρ A) (g : H) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have h := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using h

end BinaryPermutation.FiveSylowQuadratic

namespace BinaryPermutation.FiveSylowQuadratic
variable {H : Type*} [Group H] [Finite H]

/-- Sylow conjugacy puts both marked double transpositions in one conjugate. -/
theorem exists_sylow_marking
    (K : Subgroup H) (e : H ≃* Equiv.Perm (Fin 5))
    (eK : K ≃* alternatingGroup (Fin 5)) (he : ∀ k : K, e k = eK k)
    (P : Sylow 2 K) :
    ∃ g : H,
      e.symm (Equiv.swap 0 1 * Equiv.swap 2 3) ∈
        ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ∧
      e.symm (Equiv.swap 0 2 * Equiv.swap 1 3) ∈
        ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨Q, hQ⟩ := BinaryPermutation.CubicFixedSpace.Five.klein_isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) P' Q
  have hp : (P' : Subgroup (alternatingGroup (Fin 5))).map
      (MulAut.conj g).toMonoidHom = Q := by
    have h := congrArg (fun S : Sylow 2 (alternatingGroup (Fin 5)) =>
      (S : Subgroup (alternatingGroup (Fin 5)))) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  have mark (x : alternatingGroup (Fin 5)) (hx : x ∈ Q) :
      e.symm x.val ∈ ((P : Subgroup K).map K.subtype).map
        (MulAut.conj (e.symm g.val)).toMonoidHom := by
    change x ∈ (Q : Subgroup (alternatingGroup (Fin 5))) at hx
    rw [← hp] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨k.val, ⟨k, hk, rfl⟩, ?_⟩
    apply e.injective
    change e (e.symm g.val * k.val * (e.symm g.val)⁻¹) = e (e.symm x.val)
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply, he]
    have h := congrArg Subtype.val hyx
    change g.val * y.val * g.val⁻¹ = x.val at h
    simpa only [← hky, MulEquiv.coe_toMonoidHom] using h
  exact ⟨e.symm g.val,
    mark _ (hQ BinaryPermutation.CubicFixedSpace.Five.first_mem),
    mark _ (hQ BinaryPermutation.CubicFixedSpace.Five.second_mem)⟩
end BinaryPermutation.FiveSylowQuadratic

namespace BinaryPermutation.FiveSylowQuadratic
open Representation.BinaryOffender
variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]

/-- Every Sylow two-subgroup of the normal A₅ acts nonquadratically on a
noncentral quotient of the five-point permutation module. -/
theorem not_quadratic_sylow
    (K : Subgroup H) (e : H ≃* Equiv.Perm (Fin 5))
    (eK : K ≃* alternatingGroup (Fin 5)) (he : ∀ k : K, e k = eK k)
    (ρ : Representation (ZMod 2) H V)
    (f : BinaryPermutation.Full (Fin 5) →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (heq : ∀ g v, f (BinaryPermutation.representation (Fin 5) g v) = ρ (e.symm g) (f v))
    (hnoncentral : ∃ h v, ρ h v ≠ v) (P : Sylow 2 K) :
    ¬ IsQuadratic ρ ((P : Subgroup K).map K.subtype) := by
  obtain ⟨g, ha, hb⟩ := exists_sylow_marking K e eK he P
  intro hquad
  exact BinaryPermutation.FiveQuadratic.not_quadratic_of_noncentral_quotient
    e ρ f hf heq hnoncentral _ ha hb (quadratic_map_conj hquad g)

/-- The ambient image of the Sylow subgroup has order four. -/
theorem sylow_card (K : Subgroup H) (eK : K ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 K) : Nat.card ((P : Subgroup K).map K.subtype) = 4 := by
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  have h := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card
    (P.mapSurjective (f := eK.toMonoidHom) eK.surjective)
  change Nat.card ((P : Subgroup K).map eK.toMonoidHom) = 4 at h
  rwa [Subgroup.card_map_of_injective eK.injective] at h

/-- Containment in a Sylow four-group and binary rank at least two force
equality with that four-group, giving the nonquadratic action. -/
theorem not_quadratic_of_rank_two
    (K : Subgroup H) (e : H ≃* Equiv.Perm (Fin 5))
    (eK : K ≃* alternatingGroup (Fin 5)) (he : ∀ k : K, e k = eK k)
    (ρ : Representation (ZMod 2) H V)
    (f : BinaryPermutation.Full (Fin 5) →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (heq : ∀ g v, f (BinaryPermutation.representation (Fin 5) g v) = ρ (e.symm g) (f v))
    (hnoncentral : ∃ h v, ρ h v ≠ v) (P : Sylow 2 K)
    (A : Subgroup H) (hAP : A ≤ (P : Subgroup K).map K.subtype)
    (hrank : 2 ≤ rank A) : ¬ IsQuadratic ρ A := by
  have hcard : 4 ≤ Nat.card A :=
    (Nat.le_log_iff_pow_le (by decide) Nat.card_pos.ne').mp hrank
  have heqA := Subgroup.eq_of_le_of_card_ge hAP (by
    rw [sylow_card K eK P]
    exact hcard)
  rw [heqA]
  exact not_quadratic_sylow K e eK he ρ f hf heq hnoncentral P

/-- The same obstruction for an actor with a conjugate of rank at least two
inside the marked Sylow four-group. This is the γ-to-α step in the source. -/
theorem not_quadratic_of_conjugate_rank_two
    (K : Subgroup H) (e : H ≃* Equiv.Perm (Fin 5))
    (eK : K ≃* alternatingGroup (Fin 5)) (he : ∀ k : K, e k = eK k)
    (ρ : Representation (ZMod 2) H V)
    (f : BinaryPermutation.Full (Fin 5) →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (heq : ∀ g v, f (BinaryPermutation.representation (Fin 5) g v) = ρ (e.symm g) (f v))
    (hnoncentral : ∃ h v, ρ h v ≠ v) (P : Sylow 2 K)
    (A C : Subgroup H) (g : H) (hconj : C.map (MulAut.conj g).toMonoidHom = A)
    (hAP : A ≤ (P : Subgroup K).map K.subtype) (hrank : 2 ≤ rank A) :
    ¬ IsQuadratic ρ C := by
  intro hc
  have ha := quadratic_map_conj hc g
  rw [hconj] at ha
  exact not_quadratic_of_rank_two K e eK he ρ f hf heq hnoncentral P A hAP hrank ha
end BinaryPermutation.FiveSylowQuadratic

namespace BinaryPermutation.FiveSylowQuadratic

/-- Relabel an equivariant permutation quotient using genuine five-point
coordinates. The original permutation action can be the source coset action. -/
theorem exists_equivariant_quotient {H Ω V : Type*} [Group H] [MulAction H Ω]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : H ≃* Equiv.Perm (Fin 5)) (d : Ω ≃ Fin 5)
    (hd : ∀ h ω, d (h • ω) = e h (d ω))
    (ρ : Representation (ZMod 2) H V)
    (f₀ : Full Ω →ₗ[ZMod 2] V) (hf₀ : Function.Surjective f₀)
    (heq₀ : ∀ h v, f₀ (representation Ω (MulAction.toPerm h) v) = ρ h (f₀ v)) :
    ∃ f : Full (Fin 5) →ₗ[ZMod 2] V, Function.Surjective f ∧
      ∀ g v, f (representation (Fin 5) g v) = ρ (e.symm g) (f v) := by
  let c : Full (Fin 5) ≃ₗ[ZMod 2] Full Ω :=
    { toFun := fun v => v ∘ d
      invFun := fun v => v ∘ d.symm
      left_inv := by intro v; ext i; simp
      right_inv := by intro v; ext i; simp
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  have hc (h : H) (v : Full (Fin 5)) :
      c (representation (Fin 5) (e h) v) =
        representation Ω (MulAction.toPerm h) (c v) := by
    ext ω
    change v ((e h).symm (d ω)) = v (d (h⁻¹ • ω))
    rw [hd, map_inv]
    rfl
  refine ⟨f₀.comp c.toLinearMap, hf₀.comp c.surjective, ?_⟩
  intro g v
  change f₀ (c (representation (Fin 5) g v)) = ρ (e.symm g) (f₀ (c v))
  have hc' := hc (e.symm g) v
  rw [e.apply_symm_apply] at hc'
  rw [hc', heq₀]

end BinaryPermutation.FiveSylowQuadratic
