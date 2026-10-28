module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CentralField
public import Theory.Representation.FactorDegreeFiltration
public import Mathlib.GroupTheory.Sylow

/-!
# A concrete universal module for the faithful central character

For any two-subgroup P of the even hexacode cover, take the permutation
module on the actual left cosets G/P and then the omega-eigenspace of the
marked central cubic. Every irreducible F₄-representation with this central
character is a quotient of this space. A nonzero P-fixed vector supplies
the coset map; the explicit cubic projector makes its restriction nonzero.

Thus an actual simple-factor filtration of this fixed module controls the
irreducible degrees, including field descent. For a Sylow two-subgroup the
coset module has 135 coordinates and the chosen central eigenspace has 45.
The finite filtration itself is a separate obligation; it is not assumed
to follow from a numerical decomposition matrix.

Source application: Aschbacher–Smith K.1.3, printed p.453, citing GM02
Theorem 6.2/Table 6.3. The quotient construction is the elementary
fixed-vector and Frobenius-reciprocity argument on the concrete ATLAS carrier.
-/

@[expose] public section
open Atlas.Codes
namespace Representation.Hexacode.TwelveDimensional

abbrev Cover := HexEvenAutomorphisms

/-- The literal left-coset permutation representation. -/
noncomputable abbrev cosetRepresentation (P : Subgroup Cover) :=
  Representation.ofMulAction F Cover (Cover ⧸ P)

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The chosen central-character subrepresentation, with its actual operator. -/
def centralEigenspace (σ : Representation F Cover V) : Subrepresentation σ where
  toSubmodule :=
    { carrier := {v | σ hexEvenZ v = omega • v}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw
        change σ hexEvenZ v = omega • v at hv
        change σ hexEvenZ w = omega • w at hw
        change σ hexEvenZ (v + w) = omega • (v + w)
        rw [map_add, hv, hw, smul_add]
      smul_mem' := by
        intro a v hv
        change σ hexEvenZ v = omega • v at hv
        change σ hexEvenZ (a • v) = omega • (a • v)
        rw [map_smul, hv, smul_comm] }
  apply_mem_toSubmodule g v hv := by
    change σ hexEvenZ (σ g v) = omega • σ g v
    rw [← Module.End.mul_apply, ← map_mul, central_commutes, map_mul]
    change σ g (σ hexEvenZ v) = omega • σ g v
    rw [hv, map_smul]

/-- The universal module for the selected central character. -/
noncomputable abbrev cosetCentralRepresentation (P : Subgroup Cover) :=
  (centralEigenspace (cosetRepresentation P)).toRepresentation

/-- A two-group fixes a nonzero vector over the actual four-element field. -/
theorem field_pGroup_fixed_vector {H : Type*} [Group H]
    [FiniteDimensional F V] [Nontrivial V]
    (σ : Representation F H V) (hH : IsPGroup 2 H) :
    ∃ v : V, v ≠ 0 ∧ ∀ h : H, σ h v = v := by
  classical
  let e := (Module.finBasis F V).equivFun
  let : Finite V := Finite.of_equiv _ e.symm.toEquiv
  let : MulAction H V :=
    { smul := fun h v => σ h v
      one_smul v := by change σ 1 v = v; simp
      mul_smul h k v := by change σ (h * k) v = σ h (σ k v); rw [map_mul]; rfl }
  have hc : Nat.card V = 4 ^ Module.finrank F V := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := F),
      field_card, Nat.card_fin]
  have hd : 2 ∣ Nat.card V := by
    rw [hc]
    exact dvd_trans (by decide : 2 ∣ 4)
      (dvd_pow_self _ (ne_of_gt (Module.finrank_pos (R := F) (M := V))))
  have hz : (0 : V) ∈ MulAction.fixedPoints H V := fun h => map_zero (σ h)
  obtain ⟨v, hv, hv0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hd hz
  exact ⟨v, Ne.symm hv0, hv⟩

/-- A fixed vector gives an actual equivariant map from the left-coset module. -/
theorem exists_coset_map (P : Subgroup Cover) (σ : Representation F Cover V)
    (v : V) (hv : ∀ p : P, σ p.val v = v) :
    ∃ f : (cosetRepresentation P).IntertwiningMap σ,
      f (MonoidAlgebra.single (QuotientGroup.mk 1) 1) = v := by
  classical
  let value : Cover ⧸ P → V := Quotient.lift (fun g : Cover => σ g v) (by
    intro g h hrel
    have he := congrArg (σ g) (hv ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hrel⟩)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using he.symm)
  have hvalue (g : Cover) (x : Cover ⧸ P) : value (g • x) = σ g (value x) := by
    induction x using QuotientGroup.induction_on with
    | H h => exact LinearMap.congr_fun (σ.map_mul g h) v
  let b := MonoidAlgebra.basis (Cover ⧸ P) F
  let l := b.constr F value
  have hl (x : Cover ⧸ P) : l (MonoidAlgebra.single x 1) = value x :=
    b.constr_basis F value x
  let f : (cosetRepresentation P).IntertwiningMap σ :=
    { toLinearMap := l
      isIntertwining' := by
        intro g
        apply b.ext
        intro x
        change l (cosetRepresentation P g (MonoidAlgebra.single x 1)) =
          σ g (l (MonoidAlgebra.single x 1))
        rw [Representation.ofMulAction_single, hl, hl, hvalue] }
  refine ⟨f, ?_⟩
  change l (MonoidAlgebra.single (QuotientGroup.mk 1) 1) = v
  rw [hl]
  change σ 1 v = v
  simp

/-- The cubic character projector, without division since three equals one. -/
def centralProjector (σ : Representation F Cover V) (v : V) : V :=
  v + omega ^ 2 • σ hexEvenZ v + omega • σ hexEvenZ (σ hexEvenZ v)

/-- The explicit projector lands in the literal central eigenspace. -/
theorem centralProjector_mem (σ : Representation F Cover V) (v : V) :
    centralProjector σ v ∈ centralEigenspace σ := by
  have hc : σ hexEvenZ (σ hexEvenZ (σ hexEvenZ v)) = v := by
    have hp : σ hexEvenZ ^ 3 = 1 := by
      rw [← map_pow, ← hexEvenZ_order, pow_orderOf_eq_one, map_one]
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply,
      Module.End.one_apply] using LinearMap.congr_fun hp v
  change σ hexEvenZ (v + omega ^ 2 • σ hexEvenZ v +
      omega • σ hexEvenZ (σ hexEvenZ v)) =
    omega • (v + omega ^ 2 • σ hexEvenZ v + omega • σ hexEvenZ (σ hexEvenZ v))
  simp only [map_add, map_smul, hc, smul_add, smul_smul,
    show omega * omega ^ 2 = (1 : F) by decide,
    show omega * omega = omega ^ 2 by rw [pow_two], one_smul]
  abel

/-- The projector is the identity on a target with the chosen central character. -/
theorem map_centralProjector {W : Type*} [AddCommGroup W] [Module F W]
    {τ : Representation F Cover W} {σ : Representation F Cover V}
    (f : τ.IntertwiningMap σ) (hs : ∀ v, σ hexEvenZ v = omega • v) (w : W) :
    f (centralProjector τ w) = f w := by
  simp only [centralProjector, map_add, map_smul,
    f.isIntertwining τ σ, hs, smul_smul,
    show omega ^ 2 * omega = (1 : F) by decide,
    show omega * (omega * omega) = (1 : F) by decide, one_smul]
  have hh : f w + f w = 0 := by
    rw [← two_smul F, show (2 : F) = 0 by decide, zero_smul]
  rw [hh, zero_add]

/-- Every irreducible module with this central character is a quotient of the
same concrete eigenspace. No absolute irreducibility is assumed. -/
theorem exists_central_coset_quotient (P : Subgroup Cover) (hP : IsPGroup 2 P)
    [FiniteDimensional F V] (σ : Representation F Cover V) [IsIrreducible σ]
    (hs : ∀ v, σ hexEvenZ v = omega • v) :
    ∃ f : (cosetCentralRepresentation P).IntertwiningMap σ,
      Function.Surjective f := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨v, hv, hfix⟩ := field_pGroup_fixed_vector (σ.comp P.subtype) hP
  obtain ⟨f, hf⟩ := exists_coset_map P σ v hfix
  let r : (cosetCentralRepresentation P).IntertwiningMap σ :=
    { toLinearMap := f.toLinearMap.comp (centralEigenspace (cosetRepresentation P)).toSubmodule.subtype
      isIntertwining' := by
        intro g
        ext w
        exact f.isIntertwining _ _ g w.val }
  have hr : r ≠ 0 := by
    intro hr
    let w := MonoidAlgebra.single (QuotientGroup.mk (s := P) 1) (1 : F)
    have he := congrArg (fun q : (cosetCentralRepresentation P).IntertwiningMap σ =>
      q ⟨centralProjector (cosetRepresentation P) w,
        centralProjector_mem (cosetRepresentation P) w⟩) hr
    change f (centralProjector (cosetRepresentation P) w) = 0 at he
    rw [map_centralProjector f hs, hf] at he
    exact hv he
  exact ⟨r, (IsIrreducible.surjective_or_eq_zero r).resolve_right hr⟩

/-- The remaining finite certificate: actual simple factors of one central
coset module, over F₄ itself, of degrees three or nine. -/
def CosetFiltration : Prop :=
  ∃ P : Sylow 2 Cover,
    FactorDegreeFiltration ({3, 9} : Set ℕ) (cosetCentralRepresentation (P : Subgroup Cover))

/-- A checked coset filtration rules out field dimension six, including
irreducible modules that are not absolutely irreducible. -/
theorem field_finrank_ne_six_of_cosetFiltration (h : CosetFiltration)
    [FiniteDimensional F V] (σ : Representation F Cover V) [IsIrreducible σ]
    (hs : ∀ v, σ hexEvenZ v = omega • v) : Module.finrank F V ≠ 6 := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨f, hf⟩ := exists_central_coset_quotient P P.isPGroup' σ hs
  have hn : f ≠ 0 := by
    intro hz
    let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ := hf v
    exact hv (hw.symm.trans (congrArg (fun q => q w) hz))
  have hd := hP.finrank_mem f hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  omega

end Representation.Hexacode.TwelveDimensional
