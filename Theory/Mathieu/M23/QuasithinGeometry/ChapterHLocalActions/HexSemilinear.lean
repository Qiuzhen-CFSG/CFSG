module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural.FieldModel
import all Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural.FieldModel
public import Theory.SpecificGroups.GL2.Semilinear
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The hexacode coordinate stabilizer as ΓL₂(4)

For `i0 = firstThree 0`, the full coordinate stabilizer acts faithfully on
`hexZeroCoordinate i0`. The two remaining systematic coordinates identify
this space with F₄ squared. Even elements act linearly and odd elements act
semilinearly for Frobenius, by the existing hexacode field structure.

The target is the independently defined group `GL₂(F₄) ⋊ Aut(F₄)`, using all
invertible matrices and all field automorphisms. Its natural action is faithful
and covers every invertible semilinear map. Transporting the hexacode action
through the fixed coordinates gives an injective homomorphism to this group;
both groups have order 360, so this very homomorphism is an equivalence.
Faithfulness on the coordinate-zero space follows by recovering coordinate
positions from the unique second zero of each nonzero word, then excluding
the two nonidentity scalars in the coordinate-permutation kernel.

`modelEquiv_equivariant` is the actual action identification needed for
Aschbacher–Smith H.14.2(2), printed p.397 of `refs/quasithin.pdf` (combined
manuscript, 1 March 2004). `hex_semilinear_coverage` explicitly realizes every
invertible semilinear map by an element of the full stabilizer. Native M23
quotient and conjugation transport remains with the Chapter H assembly.

The coordinate map is reused from `Representation.Hexacode.ZeroNatural`.
The internal `import all` of `FieldModel` accesses its coordinate formulas
only in proofs of this extension; all exported signatures use its public API.
Underlying hexacode geometry and local group orders use the ATLAS ports of
Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research and
Attribution License 1.0; see `LICENSES/ATLAS.txt`. No new ATLAS port is used.
-/

public section

noncomputable section
open Atlas.Codes Representation.Hexacode
open Representation.SL2FourNatural (V fieldFrobenius)
open Matrix.GeneralLinearGroup
namespace Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.HexSemilinear
/-- The genuine semidirect product of all invertible matrices with all field automorphisms. -/
abbrev Gamma := GammaL2 F

private def glEquiv : GL (Fin 2) F ≃* (V ≃ₗ[F] V) :=
  toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F V)

private def linear : GL (Fin 2) F →* (V ≃ₗ[Bit] V) where
  toFun A := (glEquiv A).restrictScalars Bit
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun glEquiv.map_one v
  map_mul' A B := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun (glEquiv.map_mul A B) v

private def coefficient : (F ≃+* F) →* (V ≃ₗ[Bit] V) where
  toFun σ :=
    { toFun v i := σ (v i)
      invFun v i := σ.symm (v i)
      left_inv v := by funext i; exact σ.symm_apply_apply _
      right_inv v := by funext i; exact σ.apply_symm_apply _
      map_add' v w := by funext i; exact map_add σ _ _
      map_smul' c v := by
        funext i
        fin_cases c
        · change σ ((0 : Bit) • v i) = (0 : Bit) • σ (v i)
          simp
        · change σ ((1 : Bit) • v i) = (1 : Bit) • σ (v i)
          simp }
  map_one' := by apply LinearEquiv.ext; intro v; rfl
  map_mul' σ τ := by apply LinearEquiv.ext; intro v; rfl

/-- The natural action of ΓL₂(4) on the binary restriction of its F₄ plane. -/
def natural : Gamma →* (V ≃ₗ[Bit] V) :=
  SemidirectProduct.lift linear coefficient (by
    intro σ
    apply MonoidHom.ext
    intro A
    apply LinearEquiv.ext
    intro v
    change ((A.val.map σ).mulVec v) =
      (fun i => σ (A.val.mulVec (fun j => σ.symm (v j)) i))
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul,
      RingEquiv.apply_symm_apply, Matrix.map_apply])

/-- The action is literally matrix multiplication after entrywise field automorphism. -/
theorem natural_apply (g : Gamma) (v : V) :
    natural g v = g.left.val.mulVec (fun i => g.right (v i)) := by rfl

private theorem field_cases (x : F) : x = 0 ∨ x = 1 ∨ x = omega ∨ x = 1 + omega := by
  revert x
  decide

/-- All automorphisms of the four-element field are identity or Frobenius. -/
theorem fieldAutomorphism_cases (σ : F ≃+* F) : σ = 1 ∨ σ = fieldFrobenius := by
  have determine (σ τ : F ≃+* F) (h : σ omega = τ omega) : σ = τ := by
    apply RingEquiv.ext
    intro x
    rcases field_cases x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · simpa only [map_add, map_one] using congrArg (1 + ·) h
  rcases field_cases (σ omega) with h | h | h | h
  · exact False.elim ((by decide : omega ≠ 0) (σ.injective (h.trans σ.map_zero.symm)))
  · exact False.elim ((by decide : omega ≠ 1) (σ.injective (h.trans σ.map_one.symm)))
  · exact Or.inl (determine σ 1 h)
  · exact Or.inr (determine σ fieldFrobenius (h.trans (by decide : 1 + omega = fieldFrobenius omega)))

private theorem aut_card : Nat.card (F ≃+* F) = 2 := by
  let f : Bool → (F ≃+* F) := fun b => if b then fieldFrobenius else 1
  have hf : Function.Bijective f := by
    constructor
    · intro b c h
      cases b <;> cases c
      · rfl
      · exact False.elim (fieldFrobenius_ne_id h.symm)
      · exact False.elim (fieldFrobenius_ne_id h)
      · rfl
    · intro σ
      rcases fieldAutomorphism_cases σ with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp)

private theorem gamma_card : Nat.card Gamma = 360 := by
  rw [SemidirectProduct.card, Matrix.card_GL_field, field_card, aut_card]
  decide

/-- The coefficient component is the field automorphism of the natural semilinear action. -/
theorem natural_smul (g : Gamma) (c : F) (v : V) :
    natural g (c • v) = g.right c • natural g v := by
  change glEquiv g.left (fun i => g.right (c * v i)) = _
  simp only [map_mul]
  exact (glEquiv g.left).map_smul (g.right c) _

private theorem linear_injective : Function.Injective linear := by
  intro A B h
  apply glEquiv.injective
  apply LinearEquiv.ext
  intro v
  exact LinearEquiv.congr_fun h v

/-- The natural semilinear action is faithful, including its field component. -/
theorem natural_injective : Function.Injective natural := by
  intro g h he
  have hr : g.right = h.right := by
    apply RingEquiv.ext
    intro c
    obtain ⟨v, hv⟩ := (natural g).surjective (fun _ => 1)
    have hc := LinearEquiv.congr_fun he (c • v)
    rw [natural_smul, natural_smul, ← he, hv] at hc
    simpa using congrFun hc 0
  apply SemidirectProduct.ext
  · apply linear_injective
    have hm : linear g.left * coefficient g.right = linear h.left * coefficient h.right := he
    rw [hr] at hm
    exact mul_right_cancel hm
  · exact hr

private theorem natural_exists (e : V ≃ₗ[Bit] V) (σ : F ≃+* F)
    (he : ∀ (c : F) (v : V), e (c • v) = σ c • e v) :
    ∃ g : Gamma, natural g = e := by
  let L : V ≃ₗ[F] V :=
    { ((coefficient σ).symm.trans e).toAddEquiv with
      map_smul' := by
        intro c v
        change e (fun i => σ.symm (c * v i)) = c • _
        simp only [map_mul]
        change e (σ.symm c • (fun i => σ.symm (v i))) = _
        rw [he, RingEquiv.apply_symm_apply]
        rfl }
  refine ⟨⟨glEquiv.symm L, σ⟩, ?_⟩
  apply LinearEquiv.ext
  intro v
  change glEquiv (glEquiv.symm L) (coefficient σ v) = e v
  rw [glEquiv.apply_symm_apply]
  change e ((coefficient σ).symm (coefficient σ v)) = e v
  rw [LinearEquiv.symm_apply_apply]

open Representation.Hexacode.ZeroNatural
/-- The first systematic hexacode coordinate. -/
abbrev i0 : HexIndex := firstThree 0
/-- The full stabilizer of the chosen coordinate, including odd automorphisms. -/
abbrev H := hexPointStabilizer i0
/-- The actual coordinate-zero hexacode space. -/
abbrev W := hexZeroCoordinate i0

private def hexBinary : H →* (W ≃ₗ[Bit] W) where
  toFun := hexZeroLinear i0
  map_one' := by apply LinearEquiv.ext; intro w; rfl
  map_mul' g h := by apply LinearEquiv.ext; intro w; rfl

private def coordinatesAction : H →* (V ≃ₗ[Bit] V) where
  toFun h := vectorCoordinates.symm.trans ((hexBinary h).trans vectorCoordinates)
  map_one' := by apply LinearEquiv.ext; intro v; simp
  map_mul' g h := by apply LinearEquiv.ext; intro v; simp

private theorem coordinatesAction_equivariant (h : H) (w : W) :
    coordinatesAction h (vectorCoordinates w) = vectorCoordinates (hexZeroLinear i0 h w) := by
  change vectorCoordinates (hexBinary h (vectorCoordinates.symm (vectorCoordinates w))) = _
  rw [vectorCoordinates.symm_apply_apply]
  rfl

private theorem inverseCoordinates_smul (c : F) (v : V) :
    (vectorCoordinates.symm (c • v)).val = c • (vectorCoordinates.symm v).val := by
  change (fieldVectorCoordinates.symm (c • v)).val = c • (fieldVectorCoordinates.symm v).val
  rw [fieldVectorCoordinates.symm.map_smul]
  rfl

private theorem coordinatesAction_semilinear (h : H) :
    ∃ σ : F ≃+* F, ∀ (c : F) (v : V),
      coordinatesAction h (c • v) = σ c • coordinatesAction h v := by
  rcases Int.units_eq_one_or (hexSign h.val) with he | ho
  · refine ⟨1, ?_⟩
    intro c v
    funext j
    change fieldCoordinates (action h.val (vectorCoordinates.symm (c • v)).val) j.succ = _
    rw [inverseCoordinates_smul, action_even_smul _ he, fieldCoordinates.map_smul]
    rfl
  · refine ⟨fieldFrobenius, ?_⟩
    intro c v
    funext j
    change fieldCoordinates (action h.val (vectorCoordinates.symm (c • v)).val) j.succ = _
    rw [inverseCoordinates_smul, action_odd_smul _ ho, fieldCoordinates.map_smul]
    rfl

private theorem model_exists (h : H) : ∃ g : Gamma, natural g = coordinatesAction h := by
  obtain ⟨σ, hσ⟩ := coordinatesAction_semilinear h
  exact natural_exists _ σ hσ

private def model : H →* Gamma where
  toFun h := (model_exists h).choose
  map_one' := by
    apply natural_injective
    rw [(model_exists 1).choose_spec, map_one, map_one]
  map_mul' g h := by
    apply natural_injective
    rw [(model_exists (g * h)).choose_spec, map_mul, map_mul,
      (model_exists g).choose_spec, (model_exists h).choose_spec]

private theorem model_natural (h : H) : natural (model h) = coordinatesAction h :=
  (model_exists h).choose_spec

private theorem hexBinary_injective : Function.Injective hexBinary := by
  apply (injective_iff_map_eq_one hexBinary).mpr
  intro g hg
  have fixed (w : W) : hexZeroLinear i0 g w = w :=
    LinearEquiv.congr_fun hg w
  have hp : hexCoordinateHom g.val = 1 := by
    apply Equiv.ext
    intro j
    by_cases hj : j = i0
    · subst j
      exact g.property
    have nt : Nontrivial (hexDoubleZero i0 j) := by
      let := Fintype.ofFinite (hexDoubleZero i0 j)
      apply Fintype.one_lt_card_iff_nontrivial.mp
      rw [← Nat.card_eq_fintype_card, hexDoubleZero_card i0 j (Ne.symm hj)]
      decide
    obtain ⟨u, hu⟩ := exists_ne (0 : hexDoubleZero i0 j)
    let w : W := ⟨u.val, u.property.1⟩
    have hw : w ≠ 0 := by
      intro hw
      apply hu
      exact Subtype.ext (congrArg (fun x : W => x.val) hw)
    obtain ⟨_, _, huniq⟩ := hexZeroCoordinate_unique_other_zero i0 w hw
    have hjzero : w.val.val j = 0 := u.property.2
    have hpre : w.val.val (g.val.val.perm.symm j) = 0 := by
      have he := congrArg (fun v : W => v.val.val j) (fixed w)
      change g.val.val.localMap j (w.val.val (g.val.val.perm.symm j)) = w.val.val j at he
      rw [hjzero] at he
      exact (g.val.val.localMap j).map_eq_zero_iff.mp he
    have hprei : g.val.val.perm.symm j ≠ i0 := by
      intro he
      have he' := congrArg g.val.val.perm he
      rw [Equiv.apply_symm_apply, g.property] at he'
      exact hj he'
    have he : g.val.val.perm.symm j = j :=
      (huniq _ ⟨hprei, hpre⟩).trans (huniq j ⟨hj, hjzero⟩).symm
    exact ((Equiv.symm_apply_eq g.val.val.perm).mp he).symm
  have local_fixed (j : HexIndex) (hj : i0 ≠ j) : g.val.val.localMap j = 1 := by
    apply LinearEquiv.ext
    intro c
    obtain ⟨w, hw⟩ := hexZeroCoordinate_other_surjective i0 j hj c
    have he := congrArg (fun v : W => v.val.val j) (fixed w)
    change g.val.val.localMap j (w.val.val (g.val.val.perm.symm j)) = w.val.val j at he
    have hperm : g.val.val.perm = 1 := hp
    rw [hperm] at he
    change g.val.val.localMap j (w.val.val j) = w.val.val j at he
    rwa [hw] at he
  have hl := local_fixed (firstThree 1) (by decide)
  rcases hex_kernel_trichotomy g.val hp with he | he | he
  · exact Subtype.ext he
  · rw [he] at hl
    exact False.elim ((by decide : hexZ.val.localMap (firstThree 1) (1, 0) ≠ (1, 0))
      (LinearEquiv.congr_fun hl (1, 0)))
  · rw [he] at hl
    exact False.elim ((by decide : (hexZ ^ 2).val.localMap (firstThree 1) (1, 0) ≠ (1, 0))
      (LinearEquiv.congr_fun hl (1, 0)))

private theorem coordinatesAction_injective : Function.Injective coordinatesAction := by
  intro g h he
  apply hexBinary_injective
  apply LinearEquiv.ext
  intro w
  apply vectorCoordinates.injective
  exact (coordinatesAction_equivariant g w).symm.trans
    ((LinearEquiv.congr_fun he (vectorCoordinates w)).trans (coordinatesAction_equivariant h w))

private theorem model_bijective : Function.Bijective model := by
  have : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)
  apply (Nat.bijective_iff_injective_and_card model).mpr
  constructor
  · intro g h he
    apply coordinatesAction_injective
    rw [← model_natural, ← model_natural, he]
  · rw [hexPointStabilizer_card, gamma_card]

/-- The full hexacode coordinate stabilizer is the genuine ΓL₂(4). -/
def modelEquiv : H ≃* Gamma := MulEquiv.ofBijective model model_bijective

/-- The actual two systematic coordinates intertwine the two group actions. -/
theorem modelEquiv_equivariant (h : H) (w : W) :
    natural (modelEquiv h) (vectorCoordinates w) =
      vectorCoordinates (hexZeroLinear i0 h w) := by
  change natural (model h) (vectorCoordinates w) = _
  rw [model_natural]
  exact coordinatesAction_equivariant h w

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
/-- Every invertible semilinear map occurs, with its prescribed field automorphism. -/
theorem semilinearEquiv_coverage (σ : F ≃+* F)
    (e : LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) V V) :
    ∃ g : Gamma, g.right = σ ∧ ∀ v : V, natural g v = e v := by
  let eb : V ≃ₗ[Bit] V :=
    { e.toAddEquiv with
      map_smul' := by
        intro c v
        fin_cases c
        · change e ((0 : Bit) • v) = (0 : Bit) • e v
          simp
        · change e ((1 : Bit) • v) = (1 : Bit) • e v
          simp }
  obtain ⟨g, hg⟩ := natural_exists eb σ (fun c v => e.map_smulₛₗ c v)
  refine ⟨g, ?_, fun v => LinearEquiv.congr_fun hg v⟩
  apply RingEquiv.ext
  intro c
  obtain ⟨v, hv⟩ := e.surjective (fun _ => 1)
  have hc : natural g (c • v) = e (c • v) := LinearEquiv.congr_fun hg (c • v)
  rw [natural_smul, e.map_smulₛₗ, show natural g v = e v from LinearEquiv.congr_fun hg v, hv] at hc
  simpa using congrFun hc 0

/-- Every invertible semilinear map is realized by the literal hexacode action
through the same coordinate equivalence, with the specified field automorphism. -/
theorem hex_semilinear_coverage (σ : F ≃+* F)
    (e : LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) V V) :
    ∃ h : H, (modelEquiv h).right = σ ∧ ∀ w : W,
      ZeroNatural.vectorCoordinates (hexZeroLinear i0 h w) =
        e (ZeroNatural.vectorCoordinates w) := by
  obtain ⟨g, hσ, hg⟩ := semilinearEquiv_coverage σ e
  obtain ⟨h, rfl⟩ := modelEquiv.surjective g
  refine ⟨h, hσ, fun w => ?_⟩
  rw [← modelEquiv_equivariant]
  exact hg _

end Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.HexSemilinear
