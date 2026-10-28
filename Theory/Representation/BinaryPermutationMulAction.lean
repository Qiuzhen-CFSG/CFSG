module

public import Theory.Representation.BinaryPermutation

/-!
# The natural permutation action in multiplicative notation

The additive group of the binary natural module is often realized as an
elementary abelian subgroup. This homomorphism writes the same permutation
representation as multiplicative automorphisms, retaining its pointwise formula.
In odd degree it is faithful: the full permutation module is the direct sum
of the augmentation kernel and the fixed constant line.

Source: Aschbacher–Smith, §B.3, the natural deleted-permutation module.
The faithfulness proof generalizes the degree-five argument in
`CFSG.Quasithin.ChapterE.Section06.AlternatingLocal.a5_natural_faithful`.
-/

@[expose] public section

namespace BinaryPermutation

variable (Ω : Type*) [Fintype Ω]

/-- The natural representation, acting on its multiplicative additive group. -/
noncomputable def naturalMulAction :
    Equiv.Perm Ω →* MulAut (Multiplicative (natural Ω)) where
  toFun g := (LinearEquiv.ofBijective (naturalRepresentation Ω g)
    ((naturalRepresentation Ω).apply_bijective g)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (naturalRepresentation Ω 1 v.toAdd) = v
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (naturalRepresentation Ω (g * h) v.toAdd) =
      Multiplicative.ofAdd (naturalRepresentation Ω g (naturalRepresentation Ω h v.toAdd))
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem naturalMulAction_apply (g : Equiv.Perm Ω)
    (v : Multiplicative (natural Ω)) :
    naturalMulAction Ω g v =
      Multiplicative.ofAdd (naturalRepresentation Ω g v.toAdd) := rfl

/-- In odd degree the natural permutation action is faithful. -/
theorem naturalMulAction_injective_of_odd (hodd : Odd (Fintype.card Ω)) :
    Function.Injective (naturalMulAction Ω) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  change g = 1
  have hn (v : natural Ω) : naturalRepresentation Ω g v = v := by
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hg (Multiplicative.ofAdd v))
  let e := coreEquivNatural Ω hodd
  have hc (v : core Ω) : coreRepresentation Ω g v = v := by
    apply e.injective
    exact (coreEquivNatural_equivariant Ω hodd g v).trans (hn (e v))
  have hf (v : Full Ω) : representation Ω g v = v := by
    let w := v - augmentation Ω v • allOne Ω
    have hw : w ∈ core Ω := by
      change augmentation Ω w = 0
      simp only [w, map_sub, map_smul, augmentation_allOne,
        hodd.natCast_zmod_two, smul_eq_mul, mul_one, sub_self]
    have he := congrArg Subtype.val (hc ⟨w, hw⟩)
    change representation Ω g w = w at he
    simpa only [w, map_sub, map_smul, permute_allOne, sub_left_inj] using he
  apply Equiv.ext
  intro i
  have hi := congrFun (hf (Pi.single i 1)) (g i)
  simpa [Pi.single_apply] using hi.symm

end BinaryPermutation

end
