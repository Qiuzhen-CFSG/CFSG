module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointRecognition
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Exact adjoint displacement of the two G₂ root families

For Wilson roots A and B, explicit six-coordinate embeddings give the complete
images of the displacement operators at every nonzero field parameter. The
coordinate equivalence identifies these with the actual split-octonion
derivation action. Rank-nullity and scalar restriction give binary fixed
codimension `6*r`; conjugation preserves that value.

These are the root-class calculations in GM04 Proposition 8.2, pp.53–54.
The classification of all involutions and the pointwise-kernel equality case
remain separate obligations in `InnerCalculations`. In particular these exact
equalities rule out using a universal strict involution bound above `6*r`.
The root identities reused here are the attributed ATLAS/Wilson ports in
`Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates.Roots`.
-/

public section
open Subgroup Representation Representation.BinaryOffender Atlas.G2
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
attribute [local instance] ZMod.algebra
open Atlas.G2.Restricted.Adjoint.Coordinates
variable (F : Type*) [Field F] [CharP F 2]

section RootA
private def rootAImage : (Fin 6 → F) →ₗ[F] Space F where
  toFun w := ![w 0, w 1, w 2, w 3, w 4, 0, w 5, 0, 0, 0, 0, 0, 0, w 5]
  map_add' := by intros; ext i; fin_cases i <;> simp
  map_smul' := by intros; ext i; fin_cases i <;> simp

omit [CharP F 2] in
private theorem rootAImage_injective : Function.Injective (rootAImage F) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h6 := congrFun h 6
  funext i
  fin_cases i <;> simpa [rootAImage] using (by assumption)

private theorem rootA_range (a : F) (ha : a ≠ 0) :
    LinearMap.range ((Representation.restrictScalars (k := ZMod 2) (action F)) (rootA a) -
      LinearMap.id) = ((rootAImage F).restrictScalars (ZMod 2)).range := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨![a*v 6+a^2*v 8+a*v 13, a*v 5, a*v 11, a*v 9, a*v 10, a*v 8], ?_⟩
    change rootAImage F _ = action F (rootA a) v - v
    rw [action_rootA]
    ext i
    fin_cases i <;> simp [rootAImage, sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf <;>
      simp [CharTwo.ofNat_eq_mod]
  · rintro ⟨v, rfl⟩
    refine ⟨![0,0,0,0,0,v 1/a,(v 0+a*v 5)/a,0,v 5/a,v 3/a,v 4/a,v 2/a,0,0], ?_⟩
    change action F (rootA a) _ - _ = rootAImage F v
    rw [action_rootA]
    ext i
    fin_cases i <;> simp [rootAImage, sub_eq_add_neg, CharTwo.neg_eq] <;>
      field_simp <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod]

variable [Finite F]

/-- Every nonidentity Wilson A root element moves exactly six field dimensions
in the actual derivation action. -/
theorem rootA_fixedCodim {r : ℕ} (hF : Nat.card F = 2 ^ r) (a : F) (ha : a ≠ 0) :
    fixedCodim (adjointBinary F) (zpowers (rootA a)) = 6 * r := by
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  let : Module.Finite (ZMod 2) (Space F) := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 2) F = r := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) F = 2 ^ r
    rw [← hF]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
  let τ := Representation.restrictScalars (k := ZMod 2) (action F)
  have he : fixedCodim (adjointBinary F) (zpowers (rootA a)) =
      fixedCodim τ (zpowers (rootA a)) := by
    have h := fixedCodim_map_equivariant (adjointBinary F) τ
      (MonoidHom.id (Model F)) ((equiv F).restrictScalars (ZMod 2))
      (fun g v => by
        change equiv F (Restricted.Adjoint.action F g v) = action F g (equiv F v)
        exact (repEquiv F).isIntertwining g v) (zpowers (rootA a))
    simpa only [Subgroup.map_id] using h
  have hj : Function.Injective ((rootAImage F).restrictScalars (ZMod 2)) :=
    rootAImage_injective F
  rw [he, fixedCodim_zpowers_eq_displacement_rank, rootA_range F a ha,
    LinearMap.finrank_range_of_inj hj]
  simp [Module.finrank_pi_fintype, hd]
end RootA

section RootB
private def rootBImage : (Fin 6 → F) →ₗ[F] Space F where
  toFun w := ![w 0, w 1, w 2, 0, 0, w 3, 0, w 4, 0, 0, 0, 0, 0, w 5]
  map_add' := by intros; ext i; fin_cases i <;> simp
  map_smul' := by intros; ext i; fin_cases i <;> simp

omit [CharP F 2] in
private theorem rootBImage_injective : Function.Injective (rootBImage F) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 5
  have h4 := congrFun h 7
  have h6 := congrFun h 13
  funext i
  fin_cases i <;> simpa [rootBImage] using (by assumption)

private theorem rootB_range (a : F) (ha : a ≠ 0) :
    LinearMap.range ((Representation.restrictScalars (k := ZMod 2) (action F)) (rootB a) -
      LinearMap.id) = ((rootBImage F).restrictScalars (ZMod 2)).range := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨![a*v 3, a*v 6+a^2*v 9, a*v 12, a*v 8, a*v 10, a*v 9], ?_⟩
    change rootBImage F _ = action F (rootB a) v - v
    rw [action_rootB]
    ext i
    fin_cases i <;> simp [rootBImage, sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf <;>
      simp [CharTwo.ofNat_eq_mod]
  · rintro ⟨v, rfl⟩
    refine ⟨![0,0,0,v 0/a,0,0,(v 1+a*v 5)/a,0,v 3/a,v 5/a,v 4/a,0,v 2/a,0], ?_⟩
    change action F (rootB a) _ - _ = rootBImage F v
    rw [action_rootB]
    ext i
    fin_cases i <;> simp [rootBImage, sub_eq_add_neg, CharTwo.neg_eq]
    all_goals field_simp
    all_goals ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod]

variable [Finite F]

/-- Every nonidentity Wilson B root element also moves exactly six field
dimensions. -/
theorem rootB_fixedCodim {r : ℕ} (hF : Nat.card F = 2 ^ r) (a : F) (ha : a ≠ 0) :
    fixedCodim (adjointBinary F) (zpowers (rootB a)) = 6 * r := by
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  let : Module.Finite (ZMod 2) (Space F) := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 2) F = r := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) F = 2 ^ r
    rw [← hF]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
  let τ := Representation.restrictScalars (k := ZMod 2) (action F)
  have he : fixedCodim (adjointBinary F) (zpowers (rootB a)) =
      fixedCodim τ (zpowers (rootB a)) := by
    have h := fixedCodim_map_equivariant (adjointBinary F) τ
      (MonoidHom.id (Model F)) ((equiv F).restrictScalars (ZMod 2))
      (fun g v => by
        change equiv F (Restricted.Adjoint.action F g v) = action F g (equiv F v)
        exact (repEquiv F).isIntertwining g v) (zpowers (rootB a))
    simpa only [Subgroup.map_id] using h
  have hj : Function.Injective ((rootBImage F).restrictScalars (ZMod 2)) :=
    rootBImage_injective F
  rw [he, fixedCodim_zpowers_eq_displacement_rank, rootB_range F a ha,
    LinearMap.finrank_range_of_inj hj]
  simp [Module.finrank_pi_fintype, hd]
end RootB
variable [Finite F]

/-- The literal conjugacy equations are the interface consumed by the inner
involution geometry; both root classes have fixed codimension `6*r`. -/
theorem fixedCodim_of_root_conjugate {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (t : Model F)
    (ht : (∃ a : F, a ≠ 0 ∧ ∃ c : Model F, t = c * rootA a * c⁻¹) ∨
      (∃ a : F, a ≠ 0 ∧ ∃ c : Model F, t = c * rootB a * c⁻¹)) :
    fixedCodim (adjointBinary F) (zpowers t) = 6 * r := by
  let : Finite (Restricted.Adjoint.Space F) :=
    Finite.of_injective (equiv F) (equiv F).injective
  let : Module.Finite (ZMod 2) (Restricted.Adjoint.Space F) := Module.Finite.of_finite
  rcases ht with ⟨a, ha, c, rfl⟩ | ⟨a, ha, c, rfl⟩
  · rw [fixedCodim_zpowers_conj]
    exact rootA_fixedCodim F hF a ha
  · rw [fixedCodim_zpowers_conj]
    exact rootB_fixedCodim F hF a ha
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
