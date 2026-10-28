module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Source
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Additive irreducibility of the four point-parabolic constituents

The scalar characters and the two plane actions are transitive on nonzero
vectors. Consequently invariant additive subgroups, including all binary
submodules, are trivial or full. The literal subspace and quotient actions
are identified by the coordinate equivalences, and their cardinalities and
noncentrality are computed. An explicit alternating form intertwines the
plane actions on the embedded SL₂; the full GL₂ actions remain distinct formulas.

Source: Aschbacher–Smith, G.2.1 and G.2.5(6–8), printed pp.332,335–336.
This supplies constituent facts, not a chief-factor count.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility
open Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

/-- Irreducibility among all additive subgroups, hence also among binary submodules. -/
def AdditivelyIrreducible {A V : Type*} [AddGroup V] (act : A → V → V) : Prop :=
  ∀ K : AddSubgroup V, (∀ x v, v ∈ K → act x v ∈ K) → K = ⊥ ∨ K = ⊤

/-- At least one actor moves at least one vector. -/
def Noncentral {A V : Type*} (act : A → V → V) : Prop := ∃ x v, act x v ≠ v

private theorem irreducible_of_transitive {A V : Type*} [AddGroup V]
    (act : A → V → V)
    (ht : ∀ v w, v ≠ 0 → w ≠ 0 → ∃ x, act x v = w) :
    AdditivelyIrreducible act := by
  intro K hK
  rcases K.bot_or_exists_ne_zero with h | ⟨v,hv,hv0⟩
  · exact Or.inl h
  · right
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · exact hw ▸ K.zero_mem
    obtain ⟨x,hx⟩ := ht v w hv0 hw
    exact hx ▸ hK x v hv

/-- The scalar character on the natural line. -/
def scalarAction (x : pointParabolicSL F) (z : F) : F := (scalar F x : F) * z
/-- The inverse character on the dual quotient. -/
def inverseScalarAction (x : pointParabolicSL F) (z : F) : F :=
  (↑(scalar F x)⁻¹ : F) * z
/-- The full GL₂ action, retaining its determinant. -/
def blockAction (x : pointParabolicSL F) (v : Fin 2 → F) : Fin 2 → F :=
  (block F x : Matrix (Fin 2) (Fin 2) F) *ᵥ v
/-- The full contragredient GL₂ action. -/
def dualBlockAction (x : pointParabolicSL F) (v : Fin 2 → F) : Fin 2 → F :=
  (block F x⁻¹ : Matrix (Fin 2) (Fin 2) F).transpose *ᵥ v

theorem scalar_transitive (v w : F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x, scalarAction F x v = w := by
  refine ⟨pointTorusHom F (Units.mk0 (w / v) (div_ne_zero hw hv)), ?_⟩
  simp [scalarAction, scalar_torus, hv]

theorem inverseScalar_transitive (v w : F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x, inverseScalarAction F x v = w := by
  obtain ⟨x,hx⟩ := scalar_transitive F v w hv hw
  exact ⟨x⁻¹, by simpa [inverseScalarAction, scalarAction] using hx⟩

theorem block_transitive (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x, blockAction F x v = w := by
  obtain ⟨x,hx⟩ := Matrix.SL2.exists_mulVec_eq F v w hv hw
  exact ⟨blockLift F (SpecialLinearGroup.toGL x), by simpa [blockAction] using hx⟩

theorem dualBlock_transitive (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x, dualBlockAction F x v = w := by
  obtain ⟨x,hx⟩ := Matrix.SL2.exists_mulVec_eq F v w hv hw
  refine ⟨(blockLift F (SpecialLinearGroup.toGL x.transpose))⁻¹, ?_⟩
  simpa only [dualBlockAction, inv_inv, block_lift,
    SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_transpose,
    transpose_transpose] using hx

variable {A : Type*} [Group A] (p : A →* pointParabolicSL F)

omit [Finite F] in
private theorem transitive_pullback {V : Type*} [Zero V] (act : pointParabolicSL F → V → V)
    (hp : Function.Surjective p)
    (ht : ∀ v w, v ≠ 0 → w ≠ 0 → ∃ x, act x v = w)
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) : ∃ x, act (p x) v = w := by
  obtain ⟨x,hx⟩ := ht v w hv hw
  obtain ⟨y,rfl⟩ := hp x
  exact ⟨y,hx⟩

theorem scalar_irreducible (hp : Function.Surjective p) :
    AdditivelyIrreducible (fun x => scalarAction F (p x)) :=
  irreducible_of_transitive _ (transitive_pullback F p _ hp (scalar_transitive F))
theorem inverseScalar_irreducible (hp : Function.Surjective p) :
    AdditivelyIrreducible (fun x => inverseScalarAction F (p x)) :=
  irreducible_of_transitive _ (transitive_pullback F p _ hp (inverseScalar_transitive F))
theorem block_irreducible (hp : Function.Surjective p) :
    AdditivelyIrreducible (fun x => blockAction F (p x)) :=
  irreducible_of_transitive _ (transitive_pullback F p _ hp (block_transitive F))
theorem dualBlock_irreducible (hp : Function.Surjective p) :
    AdditivelyIrreducible (fun x => dualBlockAction F (p x)) :=
  irreducible_of_transitive _ (transitive_pullback F p _ hp (dualBlock_transitive F))

/-- A concrete alternating-form identification of the dual plane with the natural plane. -/
def alternatingEquiv : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun v := ![v 1, -v 0]
  invFun v := ![-v 1, v 0]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a v := by ext i; fin_cases i <;> simp

omit [Finite F] in
/-- On the actual determinant-one subgroup the alternating form intertwines
contragredient and natural actions. No assertion is made for the full GL₂ action. -/
theorem alternating_intertwines (x : SL(2,F)) (v : Fin 2 → F) :
    alternatingEquiv F (x⁻¹.val.transpose *ᵥ v) =
      x.val *ᵥ alternatingEquiv F v := by
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ext i
  fin_cases i <;>
    simp [alternatingEquiv, mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem block_restrict_SL (x : SL(2,F)) (v : Fin 2 → F) :
    blockAction F (blockLift F (SpecialLinearGroup.toGL x)) v = x.val *ᵥ v := by
  simp [blockAction]

theorem dualBlock_restrict_SL (x : SL(2,F)) (v : Fin 2 → F) :
    alternatingEquiv F (dualBlockAction F (blockLift F (SpecialLinearGroup.toGL x)) v) =
      x.val *ᵥ alternatingEquiv F v := by
  rw [dualBlockAction, map_inv, block_lift, ← map_inv]
  exact alternating_intertwines F x v

theorem scalar_restrict_SL (x : SL(2,F)) :
    scalar F (blockLift F (SpecialLinearGroup.toGL x)) = 1 := by
  rw [scalar_eq_det_inv, block_lift, SpecialLinearGroup.coeToGL_det, inv_one]

/-- The specified block diagonal section is a homomorphism, so its SL₂
restriction is a literal subgroup of the full point parabolic. -/
def blockSection : GL (Fin 2) F →* pointParabolicSL F where
  toFun := blockLift F
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockLift]
  map_mul' B C := by
    apply Subtype.ext
    apply Subtype.ext
    change (blockLift F (B * C)).val.val = (blockLift F B).val.val * (blockLift F C).val.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockLift, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, mul_comm]

def specialLinearSection : SL(2,F) →* pointParabolicSL F :=
  (blockSection F).comp SpecialLinearGroup.toGL

theorem specialLinearSection_injective : Function.Injective (specialLinearSection F) := by
  intro x y h
  apply SpecialLinearGroup.toGL_injective
  have he : block F (blockLift F (SpecialLinearGroup.toGL x)) =
      block F (blockLift F (SpecialLinearGroup.toGL y)) := congrArg (block F) h
  simpa only [block_lift] using he

omit [Finite F] in
private theorem noncentral_pullback {V : Type*} (act : pointParabolicSL F → V → V)
    (hp : Function.Surjective p) (ht : Noncentral act) : Noncentral (fun x => act (p x)) := by
  obtain ⟨x,v,hv⟩ := ht
  obtain ⟨y,rfl⟩ := hp x
  exact ⟨y,v,hv⟩

/-- Both scalar characters are noncentral as soon as the field has more than two elements. -/
theorem scalar_noncentral (hp : Function.Surjective p) (hc : 2 < Nat.card F) :
    Noncentral (fun x => scalarAction F (p x)) ∧
      Noncentral (fun x => inverseScalarAction F (p x)) := by
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨z,hz⟩ := exists_ne (1 : Fˣ)
  have hz' : (z : F) ≠ 1 := fun h => hz (Units.ext h)
  constructor
  · apply noncentral_pullback F p _ hp
    exact ⟨pointTorusHom F z, 1, by simpa [scalarAction] using hz'⟩
  · apply noncentral_pullback F p _ hp
    exact ⟨(pointTorusHom F z)⁻¹, 1, by simpa [inverseScalarAction] using hz'⟩

omit [Finite F] in
private theorem plane_noncentral (act : pointParabolicSL F → (Fin 2 → F) → (Fin 2 → F))
    (ht : ∀ v w, v ≠ 0 → w ≠ 0 → ∃ x, act x v = w) : Noncentral act := by
  have h0 : (![1,0] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have h1 : (![0,1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  obtain ⟨x,hx⟩ := ht _ _ h0 h1
  refine ⟨x, ![1,0], ?_⟩
  rw [hx]
  intro h
  have := congrFun h 0
  simp at this

theorem plane_actions_noncentral (hp : Function.Surjective p) :
    Noncentral (fun x => blockAction F (p x)) ∧
      Noncentral (fun x => dualBlockAction F (p x)) :=
  ⟨noncentral_pullback F p _ hp (plane_noncentral F _ (block_transitive F)),
   noncentral_pullback F p _ hp (plane_noncentral F _ (dualBlock_transitive F))⟩

/-- The literal line action expressed through its previously constructed coordinates. -/
def naturalLineAction (x : pointParabolicSL F) (v : naturalLine F) : naturalLine F :=
  (naturalLineEquiv F).symm (scalarAction F x (naturalLineEquiv F v))

noncomputable def naturalQuotientAction (x : pointParabolicSL F)
    (v : (Fin 3 → F) ⧸ naturalLine F) : (Fin 3 → F) ⧸ naturalLine F :=
  (naturalQuotientEquiv F).symm (blockAction F x (naturalQuotientEquiv F v))

def dualPlaneAction (x : pointParabolicSL F) (v : dualPlane F) : dualPlane F :=
  (dualPlaneEquiv F).symm (dualBlockAction F x (dualPlaneEquiv F v))

noncomputable def dualQuotientAction (x : pointParabolicSL F)
    (v : (Fin 3 → F) ⧸ dualPlane F) : (Fin 3 → F) ⧸ dualPlane F :=
  (dualQuotientEquiv F).symm (inverseScalarAction F x (dualQuotientEquiv F v))

/-- This transported action is exactly restriction of the ambient natural action. -/
theorem naturalLineAction_val (x : pointParabolicSL F) (v : naturalLine F) :
    (naturalLineAction F x v).val = x.val.val *ᵥ v.val := by
  have hv := congrArg Subtype.val ((naturalLineEquiv F).symm_apply_apply v)
  change lineVector F (v.val 0) = v.val at hv
  change lineVector F ((scalar F x : F) * v.val 0) = _
  rw [← natural_line_action, hv]

/-- The action is on the literal quotient and commutes with its literal quotient map. -/
theorem naturalQuotientAction_mk (x : pointParabolicSL F) (v : Fin 3 → F) :
    naturalQuotientAction F x ((naturalLine F).mkQ v) =
      (naturalLine F).mkQ (x.val.val *ᵥ v) := by
  apply (naturalQuotientEquiv F).injective
  simp only [naturalQuotientAction, LinearEquiv.apply_symm_apply,
    naturalQuotientEquiv_mk, blockAction, natural_quotient_action]

theorem dualPlaneAction_val (x : pointParabolicSL F) (v : dualPlane F) :
    (dualPlaneAction F x v).val = x.val⁻¹.val.transpose *ᵥ v.val := by
  have hv := congrArg Subtype.val ((dualPlaneEquiv F).symm_apply_apply v)
  change planeVector F (tail F v.val) = v.val at hv
  change planeVector F ((block F x⁻¹ : Matrix (Fin 2) (Fin 2) F).transpose *ᵥ tail F v.val) = _
  rw [← dual_plane_action, hv]

theorem dualQuotientAction_mk (x : pointParabolicSL F) (v : Fin 3 → F) :
    dualQuotientAction F x ((dualPlane F).mkQ v) =
      (dualPlane F).mkQ (x.val⁻¹.val.transpose *ᵥ v) := by
  apply (dualQuotientEquiv F).injective
  simp only [dualQuotientAction, LinearEquiv.apply_symm_apply,
    dualQuotientEquiv_mk, inverseScalarAction, dual_quotient_action]

private theorem transport_transitive {V W A : Type*} [AddGroup V] [AddGroup W]
    (e : V ≃+ W) (act : A → W → W)
    (ht : ∀ v w, v ≠ 0 → w ≠ 0 → ∃ x, act x v = w)
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x, e.symm (act x (e v)) = w := by
  obtain ⟨x,hx⟩ := ht (e v) (e w) (by simpa using hv) (by simpa using hw)
  exact ⟨x, by rw [hx, e.symm_apply_apply]⟩

/-- All four literal factors are irreducible even among arbitrary additive subgroups. -/
theorem flag_irreducible (hp : Function.Surjective p) :
    AdditivelyIrreducible (fun x => naturalLineAction F (p x)) ∧
    AdditivelyIrreducible (fun x => naturalQuotientAction F (p x)) ∧
    AdditivelyIrreducible (fun x => dualPlaneAction F (p x)) ∧
    AdditivelyIrreducible (fun x => dualQuotientAction F (p x)) := by
  refine ⟨irreducible_of_transitive _ ?_, irreducible_of_transitive _ ?_,
    irreducible_of_transitive _ ?_, irreducible_of_transitive _ ?_⟩
  · exact transport_transitive (naturalLineEquiv F).toAddEquiv _
      (transitive_pullback F p _ hp (scalar_transitive F))
  · exact transport_transitive (naturalQuotientEquiv F).toAddEquiv _
      (transitive_pullback F p _ hp (block_transitive F))
  · exact transport_transitive (dualPlaneEquiv F).toAddEquiv _
      (transitive_pullback F p _ hp (dualBlock_transitive F))
  · exact transport_transitive (dualQuotientEquiv F).toAddEquiv _
      (transitive_pullback F p _ hp (inverseScalar_transitive F))

private theorem transport_noncentral {V W A : Type*} [AddGroup V] [AddGroup W]
    (e : V ≃+ W) (act : A → W → W) (ht : Noncentral act) :
    Noncentral (fun x v => e.symm (act x (e v))) := by
  obtain ⟨x,v,hv⟩ := ht
  refine ⟨x,e.symm v, ?_⟩
  simpa only [e.apply_symm_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq] using hv

theorem flag_noncentral (hp : Function.Surjective p) (hc : 2 < Nat.card F) :
    Noncentral (fun x => naturalLineAction F (p x)) ∧
    Noncentral (fun x => naturalQuotientAction F (p x)) ∧
    Noncentral (fun x => dualPlaneAction F (p x)) ∧
    Noncentral (fun x => dualQuotientAction F (p x)) := by
  obtain ⟨hs,hi⟩ := scalar_noncentral F p hp hc
  obtain ⟨hb,hd⟩ := plane_actions_noncentral F p hp
  exact ⟨transport_noncentral (naturalLineEquiv F).toAddEquiv _ hs,
    transport_noncentral (naturalQuotientEquiv F).toAddEquiv _ hb,
    transport_noncentral (dualPlaneEquiv F).toAddEquiv _ hd,
    transport_noncentral (dualQuotientEquiv F).toAddEquiv _ hi⟩

omit [Finite F] in
/-- The cardinalities refer to the actual subspaces and quotients. -/
theorem flag_card {n : ℕ} (hc : Nat.card F = 2 ^ n) :
    Nat.card (naturalLine F) = 2 ^ n ∧
    Nat.card ((Fin 3 → F) ⧸ naturalLine F) = 2 ^ (2*n) ∧
    Nat.card (dualPlane F) = 2 ^ (2*n) ∧
    Nat.card ((Fin 3 → F) ⧸ dualPlane F) = 2 ^ n := by
  have hp : Nat.card (Fin 2 → F) = 2 ^ (2*n) := by
    rw [Nat.card_fun, Nat.card_fin, hc, ← pow_mul, Nat.mul_comm n 2]
  exact ⟨(Nat.card_congr (naturalLineEquiv F).toEquiv).trans hc,
    (Nat.card_congr (naturalQuotientEquiv F).toEquiv).trans hp,
    (Nat.card_congr (dualPlaneEquiv F).toEquiv).trans hp,
    (Nat.card_congr (dualQuotientEquiv F).toEquiv).trans hc⟩

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility
