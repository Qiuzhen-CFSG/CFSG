module
public import Theory.Representation.CentralCubicRestriction
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Basic
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Recognizing the natural GL₂(4) action from a central cubic

A nonidentity central element of a faithful transitive linear group fixes
no nonzero vector. For an element of order three, its norm operator is
therefore zero. The quadratic relation defines actual F₄ scalars on the
same binary space. On sixteen vectors the field dimension is two, and
an acting group of order 180 fills GL₂(4). The resulting coordinates
intertwine the original action with literal matrix multiplication.

The automorphism-subgroup version retains the original elementary
abelian group and its evaluation action. It supplies the natural-action
step for full sixteen-plane normalizers in Aschbacher, *Sporadic Groups*
(1994), 46.14(5a), pp.257–258. The scalar construction is reused from
`CentralCubicRestriction`; no classification or representation catalogue
is assumed.
-/

@[expose] public noncomputable section
namespace Representation.CentralCubicNaturalFour
open SL2FourNatural

/-- The multiplicative carrier of the natural F₄ plane. -/
abbrev Plane := Multiplicative SL2FourNatural.V

/-- The full linear group on the two-dimensional F₄ plane. -/
abbrev LinearGroup := Matrix.GeneralLinearGroup (Fin 2) F

/-- The literal natural matrix action, as automorphisms of the additive plane. -/
def naturalAction : LinearGroup →* MulAut Plane where
  toFun g := (SemilinearNormalizer.linear g).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact LinearEquiv.congr_fun SemilinearNormalizer.linear.map_one v
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    exact LinearEquiv.congr_fun (SemilinearNormalizer.linear.map_mul g h) v

/-- The action is exactly matrix multiplication on columns. -/
theorem naturalAction_apply (g : LinearGroup) (v : Plane) :
    naturalAction g v = Multiplicative.ofAdd (g.val.mulVec v.toAdd) := rfl

variable {H V : Type*} [Group H] [AddCommGroup V]
  [Module (ZMod 2) V]

/-- A nontrivial central cubic is fixed-free in a faithful transitive action. -/
theorem central_fixed_free (ρ : Representation (ZMod 2) H V)
    (hf : Function.Injective ρ)
    (ht : ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g : H, ρ g x = y)
    (z : H) (hz : z ∈ Subgroup.center H) (hn : z ≠ 1)
    (v : V) (hv : ρ z v = v) : v = 0 := by
  by_contra hnz
  apply hn
  apply hf
  ext w
  simp only [map_one,Module.End.one_apply]
  by_cases hw : w = 0
  · subst w; simp
  · obtain ⟨g,rfl⟩ := ht v w hnz hw
    have hc : ρ z * ρ g = ρ g * ρ z := by
      rw [←map_mul,←map_mul,Subgroup.mem_center_iff.mp hz g]
    change (ρ z * ρ g) v = (ρ g) v
    rw [hc]
    change ρ g (ρ z v) = ρ g v
    rw [hv]

/-- The cubic norm vanishes in the faithful transitive action. -/
theorem central_quadratic (ρ : Representation (ZMod 2) H V)
    (hf : Function.Injective ρ)
    (ht : ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g : H, ρ g x = y)
    (z : H) (hz : z ∈ Subgroup.center H) (hn : z ≠ 1) (hc : z ^ 3 = 1) :
    ρ z ^ 2 + ρ z + 1 = 0 := by
  have hp (v : V) : ρ z (ρ z (ρ z v)) = v := by
    have hh : ρ z ^ 3 = 1 := by rw [←map_pow,hc,map_one]
    simpa only [pow_succ,pow_zero,one_mul,Module.End.mul_apply,Module.End.one_apply]
      using LinearMap.congr_fun hh v
  ext v
  apply central_fixed_free ρ hf ht z hz hn
  change ρ z (ρ z (ρ z v) + ρ z v + v) = ρ z (ρ z v) + ρ z v + v
  rw [map_add,map_add,hp]
  abel

/-- A faithful order-180 transitive binary action with central cubic is the natural GL₂(4) action. -/
theorem natural_marking [Finite H] [Finite V] (ρ : Representation (ZMod 2) H V)
    (hf : Function.Injective ρ)
    (ht : ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g : H, ρ g x = y)
    (hH : Nat.card H = 180) (hV : Nat.card V = 16)
    (z : H) (hz : z ∈ Subgroup.center H) (hn : z ≠ 1) (hc : z ^ 3 = 1) :
    ∃ (f : H ≃* Matrix.GeneralLinearGroup (Fin 2) F)
      (e : V ≃ₗ[ZMod 2] (Fin 2 → F)),
      ∀ g v, e (ρ g v) = (f g).val.mulVec (e v) := by
  classical
  have hq := central_quadratic ρ hf ht z hz hn hc
  let := CentralCubicRestriction.fieldModule ρ z hq
  let := CentralCubicRestriction.fieldTower ρ z hq
  let σ := CentralCubicRestriction.fieldRepresentation ρ z hz hq
  have hdim : Module.finrank F V = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := F) (V := V)
    rw [hV, Nat.card_eq_fintype_card,card_field] at hh
    exact Nat.pow_right_injective (by decide : 1 < 4) hh.symm
  let b := Module.finBasisOfFinrankEq F V hdim
  let μ := (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp σ
  let f : H →* Matrix.GeneralLinearGroup (Fin 2) F := MonoidHom.toHomUnits μ
  have hfi : Function.Injective f := by
    intro g j hh
    apply hf
    have he := (LinearMap.toMatrixAlgEquiv b).injective (congrArg Units.val hh)
    ext v
    exact LinearMap.congr_fun he v
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) = 180 := by
    rw [Matrix.card_GL_field]
    norm_num [card_field,Fin.prod_univ_succ]
  have hfs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,hH.trans hGL.symm⟩).2
  refine ⟨MulEquiv.ofBijective f ⟨hfi,hfs⟩,b.equivFun.restrictScalars (ZMod 2),?_⟩
  intro g v
  exact (LinearMap.toMatrix_mulVec_repr b b (σ g) v).symm
open scoped IsMulCommutative

/-- The natural marking for an actual automorphism subgroup, with the original action retained. -/
theorem automorphism_marking {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (H : Subgroup (MulAut A)) (hH : Nat.card H = 180) (hA : Nat.card A = 16)
    (ht : ∀ x y : A, x ≠ 1 → y ≠ 1 → ∃ g : H, g • x = y)
    (C : Subgroup H) (hC : Nat.card C = 3) (hc : C ≤ Subgroup.center H) :
    ∃ (f : H ≃* LinearGroup) (e : A ≃* Plane),
      ∀ g a, e (g • a) = naturalAction (f g) (e a) := by
  let ρ : Representation (ZMod 2) H (Additive A) :=
    { toFun g := { g.val.toAdditive.toAddMonoidHom with
                    map_smul' := ZMod.map_smul g.val.toAdditive }
      map_one' := by ext; rfl
      map_mul' _ _ := by ext; rfl }
  have hf : Function.Injective ρ := by
    intro g h hh
    apply Subtype.ext
    apply MulEquiv.ext
    intro a
    exact LinearMap.congr_fun hh (Additive.ofMul a)
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by rw [hC]; decide)
  obtain ⟨c,hc1⟩ := exists_ne (1 : C)
  have hn : (c : H) ≠ 1 := fun hh => hc1 (Subtype.ext hh)
  have hp : (c : H) ^ 3 = 1 := by
    have hh : c ^ 3 = 1 := hC ▸ (pow_card_eq_one' : c ^ Nat.card C = 1)
    exact congrArg Subtype.val hh
  obtain ⟨f,e,he⟩ := natural_marking ρ hf ht hH hA c (hc c.property) hn hp
  exact ⟨f,e.toAddEquiv.toMultiplicative,he⟩
end Representation.CentralCubicNaturalFour
