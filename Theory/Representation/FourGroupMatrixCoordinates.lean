module
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Matrix coordinates for four-groups

Every finite elementary abelian group of order four has two-dimensional F₂
coordinates in which all its automorphisms are represented by SL₂(2) matrices.
The supplied action of any finite faithful actor likewise has an injective
matrix representation intertwining that exact action. This coordinate argument
is extracted from the natural-action recognition used in Stellmacher,
*Pushing up*, (2.1) and (3.3)(6).

The proof chooses a basis of the elementary abelian vector space. Its dimension
is two by the cardinality formula, and every invertible linear map has determinant
one because F₂ has only one unit. Applying this construction to the full
automorphism group gives simultaneous coordinates. For the standard coordinate
group, the named natural action is literally matrix multiplication; matrix
extensionality proves faithfulness, and the matrix/linear-map equivalence
represents every automorphism. These APIs supply the coordinate identifications
needed for the two-factor wreath-module recognition in Stellmacher (1.7).
-/
open scoped IsMulCommutative Matrix
namespace FourGroupMatrixCoordinates
universe u v

public theorem faithful_card_four_embedding
    {G : Type u} {W : Type v}
    [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (hfaithful : fixingSubgroup G (Set.univ : Set W) = ⊥)
    (hWcard : Nat.card W = 4) :
    ∃ φ : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      Function.Injective φ ∧
      ∃ eW : Additive W ≃+ (Fin 2 → ZMod 2),
        ∀ (g : G) (w : W),
          eW (Additive.ofMul (g • w)) =
            Matrix.mulVec (φ g).1 (eW (Additive.ofMul w)) := by
  let ρ := Representation.ofElementaryAbelianAction
    (A := G) (G := W) (p := 2)
  have hρinj : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro g hg
      have hρg : ρ g = 1 :=
        congrArg Units.val (MonoidHom.mem_ker.mp hg)
      have hgfix : (g : G) ∈ fixingSubgroup G (Set.univ : Set W) := by
        rw [mem_fixingSubgroup_iff]
        intro w _hw
        have happ := LinearMap.congr_fun hρg (Additive.ofMul w)
        exact Additive.ofMul.injective (by simpa [ρ] using happ)
      rw [hfaithful] at hgfix
      simpa using hgfix
    · exact bot_le
  let toSL : LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) →*
      _root_.SpecialLinearGroup (ZMod 2) (Additive W) :=
    { toFun := fun a => ⟨a.toLinearEquiv, Subsingleton.elim _ _⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have htoSLinj : Function.Injective toSL := by
    intro a b hab
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Additive W)).injective
    exact congrArg Subtype.val hab
  let nW := Module.finrank (ZMod 2) (Additive W)
  have hnW : nW = 2 := by
    have hc : Nat.card (Additive W) = 4 := by
      exact (Nat.card_congr Additive.toMul).trans hWcard
    rw [@Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive W)] at hc
    norm_num at hc
    change 2 ^ nW = 2 ^ 2 at hc
    exact Nat.pow_right_injective (by omega) hc
  let b0 : Module.Basis (Fin nW) (ZMod 2) (Additive W) :=
    Module.finBasis (ZMod 2) (Additive W)
  let φ : G →* _root_.SpecialLinearGroup (ZMod 2) (Additive W) :=
    toSL.comp ρ.asGroupHom
  have hφinj : Function.Injective φ := htoSLinj.comp hρinj
  let b : Module.Basis (Fin 2) (ZMod 2) (Additive W) := by
    simpa [hnW] using b0
  let ψ : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.SpecialLinearGroup.toLin_equiv b).symm.toMonoidHom.comp φ
  refine ⟨ψ, (Matrix.SpecialLinearGroup.toLin_equiv b).symm.injective.comp hφinj,
    b.equivFun.toAddEquiv, ?_⟩
  intro g w
  change b.equivFun (ρ g (Additive.ofMul w)) =
    Matrix.mulVec (ψ g).1 (b.equivFun (Additive.ofMul w))
  have hmat : (ψ g : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      LinearMap.toMatrix b b (ρ g) := by
    rfl
  rw [hmat]
  change b.repr (ρ g (Additive.ofMul w)) =
    (LinearMap.toMatrix b b (ρ g)).mulVec (b.repr (Additive.ofMul w))
  exact (LinearMap.toMatrix_mulVec_repr b b (ρ g) (Additive.ofMul w)).symm


/-- The standard SL₂(2) action on its multiplicative four-element module. -/
@[expose, instance_reducible] public def naturalAction :
    MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (Fin 2 → ZMod 2)) where
  smul a x := Multiplicative.ofAdd (Matrix.mulVec a.1 x.toAdd)
  one_smul x := by change Multiplicative.ofAdd ((1 : Matrix _ _ _) *ᵥ x.toAdd) = x; simp
  mul_smul a b x := by
    change Multiplicative.ofAdd ((a.1 * b.1) *ᵥ x.toAdd) = _
    exact congrArg Multiplicative.ofAdd (Matrix.mulVec_mulVec x.toAdd a.1 b.1).symm
  smul_one a := by change Multiplicative.ofAdd (a.1 *ᵥ 0) = 1; simp
  smul_mul a x y := by
    change Multiplicative.ofAdd (a.1 *ᵥ (x.toAdd + y.toAdd)) = _
    rw [Matrix.mulVec_add]
    rfl

/-- The named natural action is precisely matrix multiplication. -/
public theorem naturalAction_smul
    (m : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (w : Multiplicative (Fin 2 → ZMod 2)) :
    letI := naturalAction
    m • w = Multiplicative.ofAdd (Matrix.mulVec m.1 w.toAdd) := rfl

public theorem naturalAction_faithful :
    letI := naturalAction
    FaithfulSMul (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (Fin 2 → ZMod 2)) := by
  let _ := naturalAction
  constructor
  intro a b h
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  exact congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd x))

public theorem naturalAction_surjective :
    letI := naturalAction
    ∀ a : MulAut (Multiplicative (Fin 2 → ZMod 2)),
      ∃ m : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        ∀ w : Multiplicative (Fin 2 → ZMod 2), m • w = a w := by
  let _ := naturalAction
  intro a
  let e : (Fin 2 → ZMod 2) ≃+ (Fin 2 → ZMod 2) :=
    MulEquiv.toAdditiveLeft a
  let eL : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    e.toLinearEquiv (fun c x => by
      simpa using ZMod.map_smul e.toAddMonoidHom c x)
  let s : _root_.SpecialLinearGroup (ZMod 2) (Fin 2 → ZMod 2) :=
    ⟨eL, Subsingleton.elim _ _⟩
  let m := Matrix.SpecialLinearGroup.toLin'_equiv.symm s
  refine ⟨m, ?_⟩
  intro w
  have he := congrArg (fun t : _root_.SpecialLinearGroup (ZMod 2)
    (Fin 2 → ZMod 2) => t w.toAdd)
    (Matrix.SpecialLinearGroup.toLin'_equiv.apply_symm_apply s)
  exact congrArg Multiplicative.ofAdd he

public theorem exists_four_group_matrix_coordinates
    {W : Type v} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 4) :
    ∃ e : W ≃* Multiplicative (Fin 2 → ZMod 2),
      ∀ a : MulAut W, ∃ m : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        ∀ w : W, e (a w) =
          Multiplicative.ofAdd (Matrix.mulVec m.1 (e w).toAdd) := by
  have hfaithful : fixingSubgroup (MulAut W) (Set.univ : Set W) = ⊥ := by
    apply le_antisymm
    · intro a ha
      rw [mem_fixingSubgroup_iff] at ha
      apply Subgroup.mem_bot.mpr
      ext w
      exact ha w (Set.mem_univ w)
    · exact bot_le
  obtain ⟨φ, _, e, he⟩ := faithful_card_four_embedding hfaithful hcard
  refine ⟨e.toMultiplicativeRight, ?_⟩
  intro a
  refine ⟨φ a, ?_⟩
  intro w
  exact congrArg Multiplicative.ofAdd (he a w)

end FourGroupMatrixCoordinates
