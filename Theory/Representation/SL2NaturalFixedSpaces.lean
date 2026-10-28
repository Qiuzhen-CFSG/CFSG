module

public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Theory.Representation.GeneralLinearNatural

/-!
# Half-sized fixed spaces for a natural SL₂ normalizer

The additive scalar commutant makes a compatible actor field-semilinear.
A nonidentity linear actor fixes at most one field line. For a nontrivial
field twist, (u,v) ↦ u+c v injects the fixed half-space squared into the
plane. Equality of cardinalities makes this map onto. Applying it to c²u
forces the actor to square to one. The same argument identifies the full
fixed space; the scalar commutant excludes an inner quotient action.

This proves the local linear algebra used in Aschbacher--Smith 6.1.13,
printed p.670 (PDF p.687), retaining the actual natural action throughout.
-/

@[expose] public section
namespace Representation.SL2NaturalFixedSpaces
open Matrix
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- A field line, with the actual underlying additive subgroup retained. -/
def IsFieldLine (U : AddSubgroup (Fin 2 → F)) : Prop :=
  ∃ W : Submodule F (Fin 2 → F), Module.finrank F W = 1 ∧ W.toAddSubgroup = U

private theorem twist_involutive
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ c v, E (c • v) = σ c • E v)
    (U : AddSubgroup (Fin 2 → F)) (hcard : Nat.card U = Nat.card F)
    (hfix : ∀ v ∈ U, E v = v) :
    Function.Involutive E ∧ ∀ v, v ∈ U ↔ E v = v := by
  obtain ⟨c, hc⟩ : ∃ c : F, σ c ≠ c := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  let f : U × U → (Fin 2 → F) := fun p => p.1.val + c • p.2.val
  have hinj : Function.Injective f := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ hh
    change v.val + c • w.val = v'.val + c • w'.val at hh
    have hd : c • (w.val - w'.val) = v'.val - v.val := by
      rw [smul_sub]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using hh)
    have he := congrArg E hd
    rw [hsemi, map_sub, map_sub, hfix _ v.property, hfix _ v'.property,
      hfix _ w.property, hfix _ w'.property, ← hd] at he
    have hz : (σ c - c) • (w.val - w'.val) = 0 := by rw [sub_smul, he, sub_self]
    have hw : w = w' := Subtype.ext (sub_eq_zero.mp
      ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)))
    have hv : v = v' := by
      rw [hw] at hh
      exact Subtype.ext (add_right_cancel hh)
    exact Prod.ext hv hw
  have hcards : Nat.card (U × U) = Nat.card (Fin 2 → F) := by
    rw [Nat.card_prod, hcard, Nat.card_fun, Nat.card_fin, pow_two]
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcards⟩).2
  have hmem (v : Fin 2 → F) : v ∈ U ↔ E v = v := by
    refine ⟨hfix v, ?_⟩
    intro hv
    obtain ⟨⟨x, y⟩, rfl⟩ := hsurj v
    change E (x.val + c • y.val) = x.val + c • y.val at hv
    rw [map_add, hsemi, hfix _ x.property, hfix _ y.property] at hv
    have hy : y.val = 0 := by
      have hh := add_left_cancel hv
      exact (smul_eq_zero.mp (show (σ c - c) • y.val = 0 by
        rw [sub_smul, hh, sub_self])).resolve_left (sub_ne_zero.mpr hc)
    simp [f, hy]
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra! hh
    have hbot : U = ⊥ := by
      apply le_antisymm _ bot_le
      intro u hu
      exact hh u hu
    have hsmall : Nat.card F = 1 := by simpa [hbot] using hcard.symm
    exact (ne_of_gt (Finite.one_lt_card (α := F))) hsmall
  obtain ⟨⟨v, w⟩, he⟩ := hsurj ((c * c) • u)
  change v.val + c • w.val = (c * c) • u at he
  have he' := congrArg E he
  rw [map_add, hsemi, hsemi, hfix _ v.property, hfix _ w.property,
    hfix _ hu, map_mul] at he'
  have hw : w.val = (σ c + c) • u := by
    apply (smul_right_injective (M := Fin 2 → F) (sub_ne_zero.mpr hc))
    calc
      (σ c - c) • w.val = (v.val + σ c • w.val) - (v.val + c • w.val) := by
        rw [sub_smul]; abel
      _ = (σ c * σ c) • u - (c * c) • u := by rw [he, he']
      _ = (σ c - c) • ((σ c + c) • u) := by
        rw [← sub_smul, smul_smul]
        congr 1
        ring
  have hs : σ (σ c) = c := by
    have hh := hfix _ w.property
    rw [hw, hsemi, hfix _ hu] at hh
    have hsc := (smul_left_injective F hu0) hh
    rw [map_add] at hsc
    exact add_right_cancel (hsc.trans (add_comm _ _))
  refine ⟨?_, hmem⟩
  intro z
  obtain ⟨⟨v, w⟩, rfl⟩ := hsurj z
  change E (E (v.val + c • w.val)) = v.val + c • w.val
  rw [map_add, hsemi, hfix _ v.property, hfix _ w.property,
    map_add, hsemi, hfix _ v.property, hfix _ w.property, hs]

private theorem linear_fixed_line
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hne : E ≠ 1)
    (hlin : ∀ (c : F) v, E (c • v) = c • E v)
    (U : AddSubgroup (Fin 2 → F)) (hcard : Nat.card U = Nat.card F)
    (hfix : ∀ v ∈ U, E v = v) : IsFieldLine U := by
  let W : Submodule F (Fin 2 → F) := {
    carrier := {v | E v = v}
    zero_mem' := E.map_zero
    add_mem' := by
      intro v w hv hw
      exact (E.map_add v w).trans (congrArg₂ (· + ·) hv hw)
    smul_mem' := by
      intro c v hv
      exact (hlin c v).trans (congrArg (c • ·) hv) }
  have hWtop : W ≠ ⊤ := by
    intro hh
    apply hne
    apply LinearEquiv.ext
    intro v
    exact (show v ∈ W from hh ▸ Submodule.mem_top)
  have hle : U ≤ W.toAddSubgroup := hfix
  have hWcard : Nat.card F ≤ Nat.card W := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective (fun v : U => (⟨v, hle v.property⟩ : W))
      (fun _ _ h => Subtype.ext (congrArg (fun z : W => (z : Fin 2 → F)) h))
  have hpos : 0 < Module.finrank F W := by
    by_contra hz
    have hd : Module.finrank F W = 0 := by omega
    rw [Module.natCard_eq_pow_finrank (K := F) (V := W), hd, pow_zero] at hWcard
    exact (not_le_of_gt (Finite.one_lt_card (α := F))) hWcard
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hWtop)
  have hdim : Module.finrank F W = 1 := by
    simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at hlt
    omega
  refine ⟨W, hdim, ?_⟩
  symm
  apply AddSubgroup.eq_of_le_of_card_ge hle
  change Nat.card W ≤ Nat.card U
  rw [hcard, Module.natCard_eq_pow_finrank (K := F), hdim, pow_one]

omit [Finite F] in
private theorem outer_of_twist
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ c v, E (c • v) = σ c • E v) :
    ¬ ∃ g, a = MulAut.conj g := by
  rintro ⟨g, rfl⟩
  let A := SpecialLinearGroup.toLin' g
  let D : (Fin 2 → F) →+ (Fin 2 → F) := A.symm.toAddMonoidHom.comp E.toAddMonoidHom
  obtain ⟨d, hd⟩ := SL2NaturalOffenders.centralizer_scalar D (by
    intro k v
    change A.symm (E (k.val.mulVec v)) = k.val.mulVec (A.symm (E v))
    rw [he]
    change A.symm ((SpecialLinearGroup.toLin' (g * k * g⁻¹)) (E v)) =
      (SpecialLinearGroup.toLin' k) (A.symm (E v))
    simp only [map_mul, LinearEquiv.mul_apply, map_inv, LinearEquiv.coe_inv]
    exact A.symm_apply_apply _)
  have hlin (c : F) (v : Fin 2 → F) : E (c • v) = c • E v := by
    apply A.symm.injective
    rw [A.symm.map_smul]
    change D (c • v) = c • D v
    rw [hd, hd, smul_comm]
  apply hne
  ext c
  obtain ⟨v, hv⟩ := E.surjective (![1,0] : Fin 2 → F)
  have hh : σ c • (![1,0] : Fin 2 → F) = c • (![1,0] : Fin 2 → F) := by
    rw [← hv, ← hsemi, hlin]
  simpa using congrFun hh 0

/-- A nonidentity normalizer of natural SL₂ fixing an additive half-space
fixes either a field line or exactly that half-space, inducing an outer involution. -/
theorem halfSpace_alternatives
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (hne : E ≠ 1)
    (U : AddSubgroup (Fin 2 → F)) (hcard : Nat.card U = Nat.card F)
    (hfix : ∀ v ∈ U, E v = v) :
    IsFieldLine U ∨
      ((∀ v, v ∈ U ↔ E v = v) ∧ a ^ 2 = 1 ∧ ¬ ∃ g, a = MulAut.conj g) := by
  obtain ⟨σ, hσ⟩ := OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
    (specialLinearNatural 2 (k := F)) (fun f hf => SL2NaturalOffenders.centralizer_scalar f hf)
    a E he
  by_cases hid : σ = RingEquiv.refl F
  · exact Or.inl (linear_fixed_line E hne (by simpa only [hid, RingEquiv.refl_apply] using hσ)
      U hcard hfix)
  obtain ⟨hi, hU⟩ := twist_involutive E σ hid hσ U hcard hfix
  refine Or.inr ⟨hU, ?_, outer_of_twist a E he σ hid hσ⟩
  apply MulEquiv.ext
  intro g
  change a (a g) = g
  apply specialLinearNatural_injective 2
  apply LinearMap.ext
  intro v
  have hh := congrArg E (he g v)
  rw [hi, he, hi] at hh
  exact hh.symm

end Representation.SL2NaturalFixedSpaces
