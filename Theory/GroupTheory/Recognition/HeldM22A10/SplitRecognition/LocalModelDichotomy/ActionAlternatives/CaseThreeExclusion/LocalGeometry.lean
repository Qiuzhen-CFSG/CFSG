module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseThreeExclusion.SourceGroups
public import Mathlib.GroupTheory.Commutator.Basic


/-!
# The Case III source subgroups and local centralizer

The actual split centralizer is put in the coordinates supplied by `R`.
The actor subgroups `<a,b>` and `<a,b,d>` have orders four and eight, so their
full preimages have orders 64 and 128. These preimages map to the literal
`sourceH` and `sourceT`; the first also gives the required source-word coverage.

The full local centralizer of `d` consists of the sixteen words
`z1^x * z3^z * a^i * d^j`. Its multiplication has the single cross term
`i*w` in the first vector coordinate. Small kernel-checked finite calculations
show that every commutator lies in `<z1>` and that `[z3,a] = z1`.
The isomorphism with the original centralizer transports both its order and
its ambient derived subgroup. No simplicity or Case III exclusion is used.

These are the five local-geometry premises of `false_of_source_computations`.
Computing the full `C_C(d)` also identifies the `C_T(d)` appearing in Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 1, pp.2–3, DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion

private def actorH : Subgroup SymmetricFour where
  carrier := {s | ∃ i j : Fin 2, s = jankoA ^ i.val * jankoB ^ j.val}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private def actorT : Subgroup SymmetricFour where
  carrier := {s | ∃ i j l : Fin 2,
    s = jankoA ^ i.val * jankoB ^ j.val * jankoD ^ l.val}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance : DecidablePred (· ∈ actorH) := fun _ => inferInstanceAs
  (Decidable (∃ i j : Fin 2, _ = jankoA ^ i.val * jankoB ^ j.val))
private instance : DecidablePred (· ∈ actorT) := fun _ => inferInstanceAs
  (Decidable (∃ i j l : Fin 2, _ = jankoA ^ i.val * jankoB ^ j.val * jankoD ^ l.val))

private theorem actorH_card : Nat.card actorH = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem actorT_card : Nat.card actorT = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

variable (ρ : SymmetricFour →* MulAut BinaryFour)
private abbrev Model := BinaryFour ⋊[ρ] SymmetricFour
private def overActor (A : Subgroup SymmetricFour) : Subgroup (Model ρ) :=
  A.comap SemidirectProduct.rightHom

private def overActorEquiv (A : Subgroup SymmetricFour) : overActor ρ A ≃ BinaryFour × A where
  toFun x := ⟨x.val.left, ⟨x.val.right, x.property⟩⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem overActor_card (A : Subgroup SymmetricFour) :
    Nat.card (overActor ρ A) = 16 * Nat.card A := by
  rw [Nat.card_congr (overActorEquiv ρ A), Nat.card_prod]
  congr 1
  change Nat.card (Fin 4 → ZMod 2) = 16
  rw [Nat.card_eq_fintype_card]
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
  (R : JankoCoordinates (D.binaryAction K hK) .three)

private noncomputable def normalizedAction : SymmetricFour →* MulAut BinaryFour :=
  (MulAut.congr R.basis.symm).toMonoidHom.comp (D.binaryAction K hK)

private noncomputable def modelEquiv : Model (normalizedAction D K hK R) ≃* D.centralizer :=
  (SemidirectProduct.congr R.basis (MulEquiv.refl _) (by
    intro s
    apply MulEquiv.ext
    intro v
    change R.basis (R.basis.symm (D.binaryAction K hK s (R.basis v))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl)).trans (D.binarySemidirectEquiv K hK)

private noncomputable def modelEmbedding : Model (normalizedAction D K hK R) →* G :=
  D.centralizer.subtype.comp (modelEquiv D K hK R).toMonoidHom

private theorem modelEmbedding_apply (v : BinaryFour) (s : SymmetricFour) :
    modelEmbedding D K hK R ⟨v, s⟩ =
      R.ambientBasis D K hK v * jankoAmbientComplement D K hK s := rfl

private theorem modelEmbedding_injective : Function.Injective (modelEmbedding D K hK R) :=
  D.centralizer.subtype_injective.comp (modelEquiv D K hK R).injective

private theorem normalized_a (v : BinaryFour) :
    normalizedAction D K hK R jankoA v = jankoSourceA .three v := by
  change R.basis.symm (D.binaryAction K hK jankoA (R.basis v)) = _
  rw [R.action_a, MulEquiv.symm_apply_apply]
private theorem normalized_d (v : BinaryFour) :
    normalizedAction D K hK R jankoD v = jankoSourceD .three v := by
  change R.basis.symm (D.binaryAction K hK jankoD (R.basis v)) = _
  rw [R.action_d, MulEquiv.symm_apply_apply]

private theorem modelH_map :
    (overActor (normalizedAction D K hK R) actorH).map (modelEmbedding D K hK R) =
      sourceH D K hK R := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨i, j, hs⟩ := hy
    rcases y with ⟨v, s⟩
    dsimp at hs
    subst s
    exact sourceHWord_mem D K hK R v i j
  · apply sup_le
    · rintro x ⟨v, rfl⟩
      refine ⟨⟨v, 1⟩, actorH.one_mem, ?_⟩
      rw [modelEmbedding_apply, map_one, mul_one]
    · apply (closure_le _).mpr
      intro x hx
      rcases hx with rfl | hx
      · refine ⟨⟨1, jankoA⟩, ?_, ?_⟩
        · exact (by decide +kernel : jankoA ∈ actorH)
        · rw [modelEmbedding_apply, map_one, one_mul]
      · rcases hx with rfl
        refine ⟨⟨1, jankoB⟩, ?_, ?_⟩
        · exact (by decide +kernel : jankoB ∈ actorH)
        · rw [modelEmbedding_apply, map_one, one_mul]

private theorem modelT_map :
    (overActor (normalizedAction D K hK R) actorT).map (modelEmbedding D K hK R) =
      sourceT D K hK R := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨i, j, l, hs⟩ := hy
    rcases y with ⟨v, s⟩
    dsimp at hs
    subst s
    rw [modelEmbedding_apply, map_mul, map_pow, ← mul_assoc]
    exact (sourceT D K hK R).mul_mem
      (sourceH_le_sourceT D K hK R (sourceHWord_mem D K hK R v i j))
      ((sourceT D K hK R).pow_mem (sourceD_mem_sourceT D K hK R) l.val)
  · apply sup_le
    · rw [← modelH_map D K hK R]
      apply map_mono
      apply comap_mono
      exact (by decide +kernel : ∀ s : SymmetricFour, s ∈ actorH → s ∈ actorT)
    · apply zpowers_le.mpr
      refine ⟨⟨1, jankoD⟩, ?_, ?_⟩
      · exact (by decide +kernel : jankoD ∈ actorT)
      · rw [modelEmbedding_apply, map_one, one_mul]

/-- The embedded source subgroup `E<a,b>` has order 64. -/
public theorem sourceH_card : Nat.card (sourceH D K hK R) = 64 := by
  rw [← modelH_map D K hK R, card_map_of_injective (modelEmbedding_injective D K hK R),
    overActor_card, actorH_card]

/-- The embedded source subgroup `E<a,b,d>` has order 128. -/
public theorem sourceT_card : Nat.card (sourceT D K hK R) = 128 := by
  rw [← modelT_map D K hK R, card_map_of_injective (modelEmbedding_injective D K hK R),
    overActor_card, actorT_card]

/-- Every element of the actual source subgroup has the prescribed binary word form. -/
public theorem sourceH_words (t : G) (ht : t ∈ sourceH D K hK R) :
    ∃ (v : BinaryFour) (i j : Fin 2), t = sourceHWord D K hK R v i j := by
  rw [← modelH_map D K hK R] at ht
  obtain ⟨⟨v, s⟩, hs, rfl⟩ := ht
  obtain ⟨i, j, rfl⟩ := hs
  exact ⟨v, i, j, rfl⟩

-- Coordinates `(x,z,i,j)` for `z1^x * z3^z * a^i * d^j`.
private abbrev LCode := (ZMod 2 × ZMod 2) × (Fin 2 × Fin 2)
private def lvector (q : LCode) : BinaryFour :=
  Multiplicative.ofAdd ![q.1.1, 0, q.1.2, 0]
private def lactor (q : LCode) : SymmetricFour :=
  jankoA ^ q.2.1.val * jankoD ^ q.2.2.val
private def lword (q : LCode) : Model ρ := ⟨lvector q, lactor q⟩
private def modelL : Subgroup (Model ρ) :=
  centralizer ({SemidirectProduct.inr jankoD} : Set (Model ρ))

private theorem modelL_mem
    (hd : ∀ v, ρ jankoD v = jankoSourceD .three v) (x : Model ρ) :
    x ∈ modelL ρ ↔ ∃ q : LCode, x = lword ρ q := by
  change x ∈ centralizer ({SemidirectProduct.inr jankoD} : Set (Model ρ)) ↔ _
  rw [mem_centralizer_singleton_iff, SemidirectProduct.ext_iff]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_mul, map_one, mul_one, hd]
  rcases x with ⟨v, s⟩
  change (v = jankoSourceD .three v ∧ s * jankoD = jankoD * s) ↔
    ∃ q : LCode, (⟨v, s⟩ : Model ρ) = lword ρ q
  simp only [lword, SemidirectProduct.ext_iff]
  have h : ∀ (v : BinaryFour) (s : SymmetricFour),
      (v = jankoSourceD .three v ∧ s * jankoD = jankoD * s) ↔
      ∃ q : LCode, v = lvector q ∧ s = lactor q := by decide +kernel
  exact h v s

private theorem lword_injective : Function.Injective (lword ρ) := by
  intro q r h
  have h' : lvector q = lvector r ∧ lactor q = lactor r :=
    SemidirectProduct.ext_iff.mp h
  have hi : ∀ q r : LCode, lvector q = lvector r ∧ lactor q = lactor r → q = r := by
    decide +kernel
  exact hi q r h'

private theorem modelL_card (hd : ∀ v, ρ jankoD v = jankoSourceD .three v) :
    Nat.card (modelL ρ) = 16 := by
  let f : LCode → modelL ρ := fun q => ⟨lword ρ q, (modelL_mem ρ hd _).mpr ⟨q, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r h
      exact lword_injective ρ (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      obtain ⟨q, rfl⟩ := (modelL_mem ρ hd x).mp hx
      exact ⟨q, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

-- The only nontrivial action on this four-dimensional parameter set is
-- conjugation of `z3` by `a`, which contributes `z1`.
private def lmul (q r : LCode) : LCode :=
  ⟨⟨q.1.1 + r.1.1 + (q.2.1.val : ZMod 2) * r.1.2, q.1.2 + r.1.2⟩,
    ⟨q.2.1 + r.2.1, q.2.2 + r.2.2⟩⟩
private def linv (q : LCode) : LCode :=
  ⟨⟨q.1.1 + (q.2.1.val : ZMod 2) * q.1.2, q.1.2⟩, q.2⟩
private def lone : LCode := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
private def lz : LCode := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
private def lcomm (q r : LCode) : LCode := lmul (lmul (lmul q r) (linv q)) (linv r)

private theorem lword_one : lword ρ lone = 1 := by
  apply SemidirectProduct.ext
  · change lvector lone = 1
    decide +kernel
  · simp [lword, lactor, lone]

private theorem lword_mul
    (ha : ∀ v, ρ jankoA v = jankoSourceA .three v)
    (hd : ∀ v, ρ jankoD v = jankoSourceD .three v) (q r : LCode) :
    lword ρ (lmul q r) = lword ρ q * lword ρ r := by
  rcases q with ⟨⟨x, z⟩, ⟨i, j⟩⟩
  rcases r with ⟨⟨y, w⟩, ⟨k, l⟩⟩
  apply SemidirectProduct.ext
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp only [lword, lmul, lvector, lactor, SemidirectProduct.mul_left,
        pow_zero, pow_one, mul_one, one_mul, map_one, map_mul, MulAut.one_apply,
        MulAut.mul_apply, ha, hd] <;>
      revert x z y w <;> decide +kernel
  · have h : ∀ q r : LCode, lactor (lmul q r) = lactor q * lactor r := by decide +kernel
    exact h _ _

private theorem lword_inv
    (ha : ∀ v, ρ jankoA v = jankoSourceA .three v)
    (hd : ∀ v, ρ jankoD v = jankoSourceD .three v) (q : LCode) :
    lword ρ (linv q) = (lword ρ q)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← lword_mul ρ ha hd]
  have h : ∀ q : LCode, lmul (linv q) q = lone := by decide +kernel
  rw [h, lword_one]

private theorem lword_comm
    (ha : ∀ v, ρ jankoA v = jankoSourceA .three v)
    (hd : ∀ v, ρ jankoD v = jankoSourceD .three v) (q r : LCode) :
    lword ρ (lcomm q r) = ⁅lword ρ q, lword ρ r⁆ := by
  simp only [lcomm, lword_mul ρ ha hd, lword_inv ρ ha hd, commutatorElement_def]

private theorem modelL_derived
    (ha : ∀ v, ρ jankoA v = jankoSourceA .three v)
    (hd : ∀ v, ρ jankoD v = jankoSourceD .three v) :
    ⁅modelL ρ, modelL ρ⁆ = zpowers (lword ρ lz) := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨q, rfl⟩ := (modelL_mem ρ hd x).mp hx
    obtain ⟨r, rfl⟩ := (modelL_mem ρ hd y).mp hy
    rw [← lword_comm ρ ha hd]
    have h : ∀ q r : LCode, lcomm q r = lone ∨ lcomm q r = lz := by decide +kernel
    rcases h q r with h | h
    · rw [h, lword_one]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  · apply zpowers_le.mpr
    let q : LCode := ⟨⟨0, 1⟩, ⟨0, 0⟩⟩
    let r : LCode := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
    have hc : lcomm q r = lz := by decide +kernel
    rw [← hc, lword_comm ρ ha hd]
    exact commutator_mem_commutator
      ((modelL_mem ρ hd _).mpr ⟨q, rfl⟩) ((modelL_mem ρ hd _).mpr ⟨r, rfl⟩)

private theorem modelEmbedding_inr_d :
    modelEmbedding D K hK R (SemidirectProduct.inr jankoD) =
      jankoAmbientComplement D K hK jankoD := by
  change modelEmbedding D K hK R ⟨1, jankoD⟩ = _
  rw [modelEmbedding_apply, map_one, one_mul]

private theorem modelEmbedding_range : (modelEmbedding D K hK R).range = D.centralizer := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact (modelEquiv D K hK R y).property
  · intro x hx
    obtain ⟨y, hy⟩ := (modelEquiv D K hK R).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

private theorem modelL_map :
    (modelL (normalizedAction D K hK R)).map (modelEmbedding D K hK R) =
      D.centralizer ⊓ centralizer ({jankoAmbientComplement D K hK jankoD} : Set G) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    constructor
    · exact (modelEquiv D K hK R y).property
    · apply mem_centralizer_singleton_iff.mpr
      have h := congrArg (modelEmbedding D K hK R) (mem_centralizer_singleton_iff.mp hy)
      simpa only [map_mul, modelEmbedding_inr_d] using h
  · intro x hx
    have hx' : x ∈ (modelEmbedding D K hK R).range :=
      modelEmbedding_range D K hK R ▸ hx.1
    obtain ⟨y, rfl⟩ := hx'
    refine ⟨y, ?_, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply modelEmbedding_injective D K hK R
    simpa only [map_mul, modelEmbedding_inr_d] using mem_centralizer_singleton_iff.mp hx.2

include R in
/-- The centralizer of the actual complement involution inside `D.centralizer` has order 16. -/
public theorem sourceCentralizer_card :
    Nat.card (D.centralizer ⊓
      centralizer ({jankoAmbientComplement D K hK jankoD} : Set G) : Subgroup G) = 16 := by
  rw [← modelL_map D K hK R, card_map_of_injective (modelEmbedding_injective D K hK R)]
  exact modelL_card _ (normalized_d D K hK R)

private theorem modelEmbedding_z :
    modelEmbedding D K hK R (lword (normalizedAction D K hK R) lz) =
      sourceZ D K hK R := by
  rw [lword, modelEmbedding_apply, show lactor lz = 1 by decide +kernel, map_one, mul_one]
  rfl

/-- The ambient derived subgroup of the full local centralizer is the literal source line. -/
public theorem sourceCentralizer_derived :
    ⁅D.centralizer ⊓ centralizer ({jankoAmbientComplement D K hK jankoD} : Set G),
      D.centralizer ⊓ centralizer ({jankoAmbientComplement D K hK jankoD} : Set G)⁆ =
        zpowers (sourceZ D K hK R) := by
  rw [← modelL_map D K hK R, ← map_commutator,
    modelL_derived _ (normalized_a D K hK R) (normalized_d D K hK R),
    MonoidHom.map_zpowers, modelEmbedding_z]

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion
