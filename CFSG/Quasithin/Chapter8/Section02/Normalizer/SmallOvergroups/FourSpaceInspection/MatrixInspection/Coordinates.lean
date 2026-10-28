module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.Raw

/-!
# Transport from binary coordinates to the marked natural module

The fifth coordinate is the sum of the first four. This gives the even-weight
core, then `coreEquivNatural` supplies the literal deleted-permutation module.
The intertwiner is verified against the left coordinate-permutation action.
This is the A₅-module on U in 8.2.8(1), not the L₂(4)-module on B/U;
compare H.4.6(2), printed p.382/PDF p.393.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection

def extend (v : Fin 4 → ZMod 2) : Fin 5 → ZMod 2 :=
  ![v 0, v 1, v 2, v 3, v 0 + v 1 + v 2 + v 3]

theorem extend_mem : ∀ v, extend v ∈ BinaryPermutation.core (Fin 5) := by
  change ∀ v, ∑ i, extend v i = 0
  decide +kernel

theorem extend_restrict : ∀ v : Fin 5 → ZMod 2,
    ∑ i, v i = 0 → extend (fun i => v i.castSucc) = v := by decide +kernel

/-- Four coordinates identify the even-weight core, with the fifth coordinate their sum. -/
def coreCoordinates : (Fin 4 → ZMod 2) ≃+ BinaryPermutation.core (Fin 5) where
  toFun v := ⟨extend v, extend_mem v⟩
  invFun v i := v.val i.castSucc
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv v := Subtype.ext (extend_restrict v v.property)
  map_add' v w := by
    apply Subtype.ext
    exact (show ∀ v w, extend (v + w) = extend v + extend w by decide +kernel) v w

/-- The literal marked deleted-permutation module, via its even-weight core. -/
noncomputable def modelEquiv : Vector ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
  (coreCoordinates.trans
    (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).toAddEquiv).toMultiplicative

/-- Coordinate permutation transported through the actual module isomorphism. -/
noncomputable def permutationAction : Equiv.Perm (Fin 5) →* MulAut Vector :=
  (MulAut.congr modelEquiv.symm).toMonoidHom.comp (BinaryPermutation.naturalMulAction (Fin 5))

private theorem expanded_decode : ∀ x i,
    (if expandedBits x i then (1 : ZMod 2) else 0) = extend (decode x).toAdd i := by
  decide +kernel

private theorem extend_permute (σ : Equiv.Perm (Fin 5)) (x : Bits) :
    extend (decode (permuteBits σ x)).toAdd =
      BinaryPermutation.representation (Fin 5) σ (extend (decode x).toAdd) := by
  have hfirst : (decode (permuteBits σ x)).toAdd = fun i =>
      BinaryPermutation.representation (Fin 5) σ (extend (decode x).toAdd) i.castSucc := by
    rw [permuteBits, decode_fromBits]
    funext i
    exact expanded_decode x (σ.symm i.castSucc)
  rw [hfirst]
  exact extend_restrict _ (BinaryPermutation.core_invariant (Fin 5) σ (extend_mem _))

/-- The low-bit-first calculation uses the same left-action convention as the source marking. -/
theorem permutationAction_decode (σ : Equiv.Perm (Fin 5)) (x : Bits) :
    permutationAction σ (decode x) = decode (permuteBits σ x) := by
  apply modelEquiv.injective
  change modelEquiv (modelEquiv.symm
    (BinaryPermutation.naturalMulAction (Fin 5) σ (modelEquiv (decode x)))) = _
  rw [modelEquiv.apply_symm_apply]
  apply congrArg Multiplicative.ofAdd
  change BinaryPermutation.naturalRepresentation (Fin 5) σ
    (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
      (coreCoordinates (decode x).toAdd)) =
    BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
      (coreCoordinates (decode (permuteBits σ x)).toAdd)
  rw [← BinaryPermutation.coreEquivNatural_equivariant]
  apply congrArg (BinaryPermutation.coreEquivNatural (Fin 5) (by decide))
  exact Subtype.ext (extend_permute σ x).symm

/-- The finite permutation formula is the transported literal natural action. -/
theorem bitAction_permutationAction (σ : Equiv.Perm (Fin 5)) :
    bitAction (permutationAction σ) = permuteBits σ := by
  funext x
  change bitEquiv.symm (permutationAction σ (decode x)) = _
  rw [permutationAction_decode]
  exact bitEquiv.symm_apply_apply _

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection
