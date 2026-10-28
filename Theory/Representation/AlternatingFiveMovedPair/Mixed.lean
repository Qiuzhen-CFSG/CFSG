module
public import Theory.Representation.TensorInvolutionDisplacement
public import Theory.Representation.SL2FourNaturalOrbits.NoTransvections
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines
public import Theory.Representation.BinaryPermutation.FiveLowRank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split

/-!
# The mixed natural/deleted A₅ pair

The two sixteen-dimensional summands are the binary external tensors N⊗D
and D⊗N, where N is the scalar-restricted SL₂(4) natural module and D is
the five-letter deleted module. The marked S₅ extensions use the natural
five-line action, retaining the same SL₂(4) factor markings. Every nontrivial
factor-preserving involution moves at least twelve dimensions. An involution
exchanging the two summands moves exactly sixteen dimensions.

The tensor involution displacement formula proves the bounds symbolically;
there is no enumeration of the thirty-two-dimensional linear group. These
are the model estimates for the moved mixed orbit in Aschbacher–Smith,
D.3.5, printed pp.195–196. Full linear-normalizer coverage is separate.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open Representation.BinaryOffender.NaturalTensor
namespace Representation.AlternatingFiveMovedPair.Mixed
open SL2FourNatural SL2FourNatural.SemilinearNormalizer
abbrev Sym := Equiv.Perm (Fin 5)
abbrev Natural := SL2FourNatural.V
abbrev Deleted := BinaryPermutation.natural (Fin 5)
abbrev ND := Natural ⊗[ZMod 2] Deleted
abbrev DN := Deleted ⊗[ZMod 2] Natural
abbrev Space := ND × DN

def naturalAction : Representation (ZMod 2) Sym Natural :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (specialField.subtype.comp symmetricFiveEquiv.symm.toMonoidHom)
abbrev deletedAction : Representation (ZMod 2) Sym Deleted :=
  BinaryPermutation.naturalRepresentation (Fin 5)
def first : Representation (ZMod 2) (Sym × Sym) ND :=
  Representation.tprod (naturalAction.comp (MonoidHom.fst _ _))
    (deletedAction.comp (MonoidHom.snd _ _))
def second : Representation (ZMod 2) (Sym × Sym) DN :=
  Representation.tprod (deletedAction.comp (MonoidHom.fst _ _))
    (naturalAction.comp (MonoidHom.snd _ _))
def extendedAction := first.prod second
def action : Representation (ZMod 2) (SL × SL) Space :=
  extendedAction.comp (specialFiveLines.prodMap specialFiveLines)

lemma finrank_natural : Module.finrank (ZMod 2) Natural = 4 := finrank_vector
lemma finrank_deleted : Module.finrank (ZMod 2) Deleted = 4 := by
  simpa using BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)
lemma finrank_nd : Module.finrank (ZMod 2) ND = 16 := by
  rw [Module.finrank_tensorProduct, finrank_natural, finrank_deleted]
lemma finrank_dn : Module.finrank (ZMod 2) DN = 16 := by
  rw [Module.finrank_tensorProduct, finrank_deleted, finrank_natural]
lemma finrank_space : Module.finrank (ZMod 2) Space = 32 := by
  rw [Module.finrank_prod, finrank_nd, finrank_dn]

lemma naturalAction_injective : Function.Injective naturalAction := by
  intro p q h
  apply symmetricFiveEquiv.symm.injective
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact h

lemma naturalAction_special (g : SL) :
    naturalAction (specialFiveLines g) = (SL2FourNatural.action g).toLinearMap := by
  let G : specialField := ⟨SL2FourNatural.action g,
    (show SL2FourNatural.action.range ≤ specialField from le_sup_left) ⟨g, rfl⟩⟩
  have hg : symmetricFiveEquiv.symm (specialFiveLines g) = G := by
    apply symmetricFiveEquiv.injective
    rw [MulEquiv.apply_symm_apply, symmetricFiveEquiv_special_apply]
  change (symmetricFiveEquiv.symm (specialFiveLines g)).val.toLinearMap = _
  rw [hg]

lemma naturalAction_normalizes (p : Sym) :
    (symmetricFiveEquiv.symm p).val ∈ normalizer := by
  apply (show specialField ≤ normalizer from ?_)
  · exact (symmetricFiveEquiv.symm p).property
  · apply sup_le SL2FourNatural.action.range.le_normalizer
    apply Subgroup.zpowers_le.mpr
    apply semilinear_le_normalizer
    exact ⟨fieldElement, natural_fieldElement⟩

lemma natural_displacement (p : Sym) (hp : p * p = 1) (hne : p ≠ 1) :
    operatorFixedCodim (naturalAction p) = 2 := by
  have h2 : naturalAction p * naturalAction p = 1 := by rw [← map_mul, hp, map_one]
  have hle := TensorInvolutionDisplacement.twice_displacement_le (naturalAction p) h2
  rw [finrank_natural] at hle
  have hnotone : operatorFixedCodim (naturalAction p) ≠ 1 := by
    exact normalizer_no_rank_one (symmetricFiveEquiv.symm p).val (naturalAction_normalizes p)
  have hnotzero : operatorFixedCodim (naturalAction p) ≠ 0 := by
    intro hz
    have hr : LinearMap.range (naturalAction p - 1) = ⊥ := Submodule.finrank_eq_zero.mp hz
    have he : naturalAction p = naturalAction 1 := by
      rw [map_one]
      exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp hr)
    exact hne (naturalAction_injective he)
  omega

lemma deleted_displacement_pos (p : Sym) (hne : p ≠ 1) :
    1 ≤ operatorFixedCodim (deletedAction p) := by
  have he := operatorFixedCodim_eq_of_equiv
    (BinaryPermutation.coreRepresentation (Fin 5) p) (deletedAction p)
    (BinaryPermutation.coreEquivNatural (Fin 5) (by decide))
    (BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) p)
  rw [← he]
  exact BinaryPermutation.FiveLowRank.rank_pos p hne

lemma deleted_displacement_le (p : Sym) (hp : p * p = 1) :
    operatorFixedCodim (deletedAction p) ≤ 2 := by
  have h2 : deletedAction p * deletedAction p = 1 := by rw [← map_mul, hp, map_one]
  have hle := TensorInvolutionDisplacement.twice_displacement_le (deletedAction p) h2
  rw [finrank_deleted] at hle
  omega

lemma first_displacement (p q : Sym) (hp : p * p = 1) (hq : q * q = 1)
    (hne : p ≠ 1) : operatorFixedCodim (first (p, q)) = 8 := by
  have hnp : naturalAction p * naturalAction p = 1 := by rw [← map_mul, hp, map_one]
  have hdq : deletedAction q * deletedAction q = 1 := by rw [← map_mul, hq, map_one]
  have hf := TensorInvolutionDisplacement.tensor_displacement_formula
    (naturalAction p) (deletedAction q) hnp hdq
  rw [finrank_natural, finrank_deleted, natural_displacement p hp hne] at hf
  change operatorFixedCodim (TensorProduct.map (naturalAction p) (deletedAction q)) = 8
  omega

lemma second_displacement (p q : Sym) (hp : p * p = 1) (hq : q * q = 1)
    (hne : q ≠ 1) : operatorFixedCodim (second (p, q)) = 8 := by
  have hdp : deletedAction p * deletedAction p = 1 := by rw [← map_mul, hp, map_one]
  have hnq : naturalAction q * naturalAction q = 1 := by rw [← map_mul, hq, map_one]
  have hf := TensorInvolutionDisplacement.tensor_displacement_formula
    (deletedAction p) (naturalAction q) hdp hnq
  rw [finrank_natural, finrank_deleted, natural_displacement q hq hne] at hf
  change operatorFixedCodim (TensorProduct.map (deletedAction p) (naturalAction q)) = 8
  omega

lemma pair_displacement (p q : Sym) :
    operatorFixedCodim (extendedAction (p,q)) =
      operatorFixedCodim (first (p,q)) + operatorFixedCodim (second (p,q)) :=
  RankTwo.Imprimitive.finrank_block _ _

lemma extended_displacement_ge_twelve (g : Sym × Sym) (hg : g * g = 1) (hne : g ≠ 1) :
    12 ≤ operatorFixedCodim (extendedAction g) := by
  obtain ⟨p, q⟩ := g
  have hp : p * p = 1 := congrArg Prod.fst hg
  have hq : q * q = 1 := congrArg Prod.snd hg
  rw [pair_displacement]
  by_cases hp1 : p = 1
  · subst p
    have hq1 : q ≠ 1 := by intro h; exact hne (Prod.ext rfl h)
    rw [second_displacement 1 q hp hq hq1]
    have hf := TensorInvolutionDisplacement.tensor_displacement_formula
      (naturalAction 1) (deletedAction q) (by simp) (by rw [← map_mul, hq, map_one])
    have hz : operatorFixedCodim (naturalAction 1) = 0 := by simp [operatorFixedCodim]
    rw [finrank_natural, finrank_deleted, hz] at hf
    have hd := deleted_displacement_pos q hq1
    change 12 ≤ operatorFixedCodim (TensorProduct.map (naturalAction 1) (deletedAction q)) + 8
    omega
  · rw [first_displacement p q hp hq hp1]
    by_cases hq1 : q = 1
    · subst q
      have hf := TensorInvolutionDisplacement.tensor_displacement_formula
        (deletedAction p) (naturalAction 1) (by rw [← map_mul, hp, map_one]) (by simp)
      have hz : operatorFixedCodim (naturalAction 1) = 0 := by simp [operatorFixedCodim]
      rw [finrank_natural, finrank_deleted, hz] at hf
      have hd := deleted_displacement_pos p hp1
      change 12 ≤ 8 + operatorFixedCodim (TensorProduct.map (deletedAction p) (naturalAction 1))
      omega
    · rw [second_displacement p q hp hq hq1]
      omega

lemma exchanging_displacement (t : Module.End (ZMod 2) Space)
    (a : ND →ₗ[ZMod 2] DN) (b : DN →ₗ[ZMod 2] ND)
    (ht : ∀ v w, t (v,w) = (b w, a v)) (ht2 : t * t = 1) :
    operatorFixedCodim t = 16 := by
  exact (RankTwo.Imprimitive.finrank_of_exchanges t a b ht ht2).trans finrank_nd

end Representation.AlternatingFiveMovedPair.Mixed
