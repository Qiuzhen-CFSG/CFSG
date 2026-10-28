module

public import Theory.Representation.BinaryOffender.Basic

/-!
# Conjugacy transport for binary offenders

Conjugation preserves subgroup order and elementary abelian structure. The
representation operator at the conjugating element identifies the two fixed
spaces, so it also preserves their codimensions. These facts apply to arbitrary
binary representations, including the full permutation module used in
Aschbacher–Smith, *The Classification of Quasithin Groups*, B.3.2, pp. 83–84.

The fixed-space equivalence follows the proof of the private conjugacy lemma
in `Theory.Representation.SylowInvariantDimension`.
-/

public section

namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Binary rank is unchanged by conjugation. -/
theorem rank_map_conj (A : Subgroup G) (g : G) :
    rank (A.map (MulAut.conj g).toMonoidHom) = rank A := by
  unfold rank
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-- Conjugation preserves nontrivial elementary abelian subgroups. -/
theorem IsElementaryTwo.map_conj {A : Subgroup G} (hA : IsElementaryTwo A)
    (g : G) : IsElementaryTwo (A.map (MulAut.conj g).toMonoidHom) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  exact ⟨fun h => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A
    (MulAut.conj g).injective).mp h), IsElementaryAbelian.map _⟩

/-- The representation operator transports fixed spaces along conjugation. -/
noncomputable def fixedSpaceConjEquiv (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (g : G) :
    fixedSpace ρ A ≃ₗ[ZMod 2] fixedSpace ρ (A.map (MulAut.conj g).toMonoidHom) := by
  let B := A.map (MulAut.conj g).toMonoidHom
  have hinv (x : V) : ρ g⁻¹ (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : V) : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hforward (v : fixedSpace ρ A) : ρ g v ∈ fixedSpace ρ B := by
    intro b
    obtain ⟨a, ha, hab⟩ := b.property
    have hv : ρ a v = v := v.property ⟨a, ha⟩
    change ρ (b : G) (ρ g v) = ρ g v
    rw [← hab]
    change ρ (g * a * g⁻¹) (ρ g v) = _
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, hinv, hv]
  have hback (v : fixedSpace ρ B) : ρ g⁻¹ v ∈ fixedSpace ρ A := by
    intro a
    have hmem : g * (a : G) * g⁻¹ ∈ B := ⟨a, a.property, rfl⟩
    have hv : ρ (g * (a : G) * g⁻¹) v = v := v.property ⟨_, hmem⟩
    change ρ (a : G) (ρ g⁻¹ v) = ρ g⁻¹ v
    have h := congrArg (fun x : V => ρ g⁻¹ x) hv
    rw [map_mul, map_mul] at h
    simpa only [Module.End.mul_apply, hinv] using h
  exact
    { toFun := fun v => ⟨ρ g v, hforward v⟩
      invFun := fun v => ⟨ρ g⁻¹ v, hback v⟩
      left_inv := fun v => Subtype.ext (hinv v)
      right_inv := fun v => Subtype.ext (hginv v)
      map_add' := fun v w => Subtype.ext (map_add (ρ g) (v : V) (w : V))
      map_smul' := fun c v => Subtype.ext (map_smul (ρ g) c (v : V)) }

/-- Fixed codimension is unchanged by conjugation. -/
theorem fixedCodim_map_conj [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (g : G) :
    fixedCodim ρ (A.map (MulAut.conj g).toMonoidHom) = fixedCodim ρ A := by
  have h := (fixedSpaceConjEquiv ρ A g).finrank_eq
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ (A.map (MulAut.conj g).toMonoidHom)
  omega

end Representation.BinaryOffender
