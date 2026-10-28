module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.AmbientCoordinates

/-!
# The Case IV model in the actual ambient group

The binary coordinate witness intertwines the dihedral action with the
original complement conjugation. Its semidirect-product map is injective,
and its range has order 128, so it is an ambient Sylow two-subgroup.
The kernel and actor inclusions are the literal maps from `AmbientCoordinates`.
No identification with the initially chosen Sylow subgroup is assumed.

Source: Janko, J. Algebra 9 (1968), Section 1, printed pp.2–3.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
universe u
variable {ρ : SymmetricFour →* MulAut BinaryFour}

public theorem actor_injective : Function.Injective actor := by decide +kernel

public theorem action_compatible (R : JankoCoordinates ρ .four) (s : DihedralGroup 4) (v : BinaryFour) :
    R.basis (action s v) = ρ (actor s) (R.basis v) := by
  let f := (MulAut.congr R.basis.symm).toMonoidHom.comp ρ
  have hb : f jankoB = bAut := by
    apply MulEquiv.ext
    intro w
    change R.basis.symm (ρ jankoB (R.basis w)) = bAut w
    rw [R.action_b, MulEquiv.symm_apply_apply]
    rfl
  have hd : f jankoD = dAut := by
    apply MulEquiv.ext
    intro w
    change R.basis.symm (ρ jankoD (R.basis w)) = dAut w
    rw [R.action_d, MulEquiv.symm_apply_apply]
    rfl
  have he : f (actor s) = action s := by
    cases s with
    | r i => change f ((jankoB * jankoD) ^ i.val) = (bAut * dAut) ^ i.val
             rw [map_pow, map_mul, hb, hd]
    | sr i => change f (jankoD * (jankoB * jankoD) ^ i.val) = dAut * (bAut * dAut) ^ i.val
              rw [map_mul, map_pow, map_mul, hb, hd]
  have hh := congrArg (fun e : MulAut BinaryFour => e v) he
  change R.basis.symm (ρ (actor s) (R.basis v)) = action s v at hh
  exact (congrArg R.basis hh).symm.trans (R.basis.apply_symm_apply _)

@[expose] public def toBinary (R : JankoCoordinates ρ .four) : Model →* BinaryFour ⋊[ρ] SymmetricFour :=
  SemidirectProduct.map R.basis.toMonoidHom actor (by
    intro s
    apply MonoidHom.ext
    intro v
    exact action_compatible R s v)

public theorem toBinary_injective (R : JankoCoordinates ρ .four) : Function.Injective (toBinary R) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact R.basis.injective (congrArg SemidirectProduct.left h)
  · exact actor_injective (congrArg SemidirectProduct.right h)

variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
  (R : JankoCoordinates (D.binaryAction K hK) .four)

@[expose] public noncomputable def into : Model →* G :=
  D.centralizer.subtype.comp ((D.binarySemidirectEquiv K hK).toMonoidHom.comp (toBinary R))

public theorem into_injective : Function.Injective (into D K hK R) :=
  D.centralizer.subtype_injective.comp ((D.binarySemidirectEquiv K hK).injective.comp
    (toBinary_injective R))

public theorem into_inl (v : BinaryFour) :
    into D K hK R (SemidirectProduct.inl v) = R.ambientBasis D K hK v := by
  change ((D.kernelBinaryEquiv.symm (R.basis v) : D.centralizer) : G) *
    (((D.complementEquiv K hK).symm (actor 1) : D.centralizer) : G) = _
  simp only [map_one, Subgroup.coe_one, mul_one]
  rfl

public theorem into_inr (s : DihedralGroup 4) :
    into D K hK R (SemidirectProduct.inr s) = jankoAmbientComplement D K hK (actor s) := by
  change ((D.kernelBinaryEquiv.symm (R.basis 1) : D.centralizer) : G) *
    (((D.complementEquiv K hK).symm (actor s) : D.centralizer) : G) = _
  simp only [map_one, Subgroup.coe_one, one_mul]
  rfl

/-- The marked involution d is the original complement transposition. -/
public theorem into_d : into D K hK R d = jankoAmbientComplement D K hK jankoD := by
  have h : actor (.sr 0) = jankoD := by decide +kernel
  exact (into_inr D K hK R (.sr 0)).trans
    (congrArg (jankoAmbientComplement D K hK) h)

/-- The marked involution a is the original double transposition. -/
public theorem into_a : into D K hK R a = jankoAmbientComplement D K hK jankoA := by
  have h : actor (.r 2) = jankoA := by decide +kernel
  exact (into_inr D K hK R (.r 2)).trans
    (congrArg (jankoAmbientComplement D K hK) h)

/-- The marked involution b has the source's fixed label. -/
public theorem into_b : into D K hK R b = jankoAmbientComplement D K hK jankoB := by
  have h : actor (.sr 3) = jankoB := by decide +kernel
  exact (into_inr D K hK R (.sr 3)).trans
    (congrArg (jankoAmbientComplement D K hK) h)

/-- The model vectors are the actual kernel basis vectors. -/
public theorem into_z (i : Fin 4) : into D K hK R (z i) =
    R.ambientBasis D K hK (Multiplicative.ofAdd (Pi.single i 1)) :=
  into_inl D K hK R _

@[expose] public noncomputable def T : Subgroup G := (into D K hK R).range

public theorem T_card : Nat.card (T D K hK R) = 128 :=
  (Nat.card_congr (MonoidHom.ofInjective (into_injective D K hK R)).toEquiv).symm.trans model_card

@[expose] public noncomputable def sylow : Sylow 2 G := Sylow.ofCard (T D K hK R) (by
  rw [T_card]
  exact D.sylow_card.symm.trans D.sylow.card_eq_multiplicity)

@[expose] public noncomputable def modelEquivSylow : Model ≃* sylow D K hK R :=
  MonoidHom.ofInjective (into_injective D K hK R)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
