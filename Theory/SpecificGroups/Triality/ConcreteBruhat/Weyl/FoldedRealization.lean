module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.MatrixRealization
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.DiagramFixed

/-!
# The folded Weyl group in the actual split matrices

The faithful matrix/root equivalence intertwines the actual graph-field action
with conjugation by the diagram permutation. Restricting it to fixed points
and using the exhaustive root-side calculation gives a dihedral equivalence
onto the whole fixed matrix Weyl subgroup. Its values are exactly the already
published representatives, so these words are multiplicative and faithful.

Source: GLS3 §§2.3.1–3 and 2.4.4 (`refs/KGroup/GLS3/chapter2.tex`).
All characteristic-two fields, including q = 2, are covered.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.ConcreteBruhat
open Parabolics
noncomputable section

/-- Fixedness of an actual matrix is exactly fixedness of its root permutation. -/
theorem splitWeylEquiv_mem_fixed_iff (P : Parameters) (hp : P.prime = 2) (w : splitWeylSubgroup P) :
    w ∈ fixedSplitWeylSubgroup P ↔ splitWeylEquiv P hp w ∈ fixedRootWeylSubgroup := by
  have hgf := splitWeylEquiv_graphField P hp w
  constructor
  · intro hw
    have hf : splitWeylGraphField P w = w := Subtype.ext hw
    have he := congrArg (fun v : splitWeylSubgroup P => (splitWeylEquiv P hp v).val) hf
    exact (mem_fixedRootWeylSubgroup _).mpr
      (mul_inv_eq_iff_eq_mul.mp (hgf.symm.trans he))
  · intro hw
    have hc := (mem_fixedRootWeylSubgroup _).mp hw
    have he : splitWeylEquiv P hp (splitWeylGraphField P w) = splitWeylEquiv P hp w :=
      Subtype.ext (hgf.trans (mul_inv_eq_iff_eq_mul.mpr hc))
    exact congrArg Subtype.val ((splitWeylEquiv P hp).injective he)

/-- The matrix/root isomorphism restricts to the actual fixed subgroups. -/
def fixedWeylEquiv (P : Parameters) (hp : P.prime = 2) :
    fixedSplitWeylSubgroup P ≃* fixedRootWeylSubgroup where
  toFun w := ⟨splitWeylEquiv P hp w.val, (splitWeylEquiv_mem_fixed_iff P hp w.val).mp w.property⟩
  invFun w := ⟨(splitWeylEquiv P hp).symm w.val, (splitWeylEquiv_mem_fixed_iff P hp _).mpr (by
    rw [MulEquiv.apply_symm_apply]
    exact w.property)⟩
  left_inv w := Subtype.ext ((splitWeylEquiv P hp).symm_apply_apply w.val)
  right_inv w := Subtype.ext ((splitWeylEquiv P hp).apply_symm_apply w.val)
  map_mul' v w := Subtype.ext (map_mul (splitWeylEquiv P hp) v.val w.val)

private def foldedSplit (P : Parameters) (hp : P.prime = 2) (a : Node) :
    splitWeylSubgroup P :=
  ⟨elementaryInclusion P (simpleElementary P hp a), elementaryInclusion_simple_mem P hp a⟩

private lemma foldedSplit_image (P : Parameters) (hp : P.prime = 2) (a : Node) :
    splitWeylEquiv P hp (foldedSplit P hp a) = foldedRootReflection a := by
  cases a with
  | arms =>
    have h : foldedSplit P hp .arms =
        splitWeylGenerator P 0 * splitWeylGenerator P 2 * splitWeylGenerator P 3 :=
      Subtype.ext (elementaryInclusion_simple_arms P hp)
    exact (congrArg (splitWeylEquiv P hp) h).trans (by
      simp only [map_mul, splitWeylEquiv_generator, foldedRootReflection])
  | central =>
    have h : foldedSplit P hp .central = splitWeylGenerator P 1 :=
      Subtype.ext (elementaryInclusion_simple_central P hp)
    exact (congrArg (splitWeylEquiv P hp) h).trans (splitWeylEquiv_generator P hp 1)

/-- The published split word realizes precisely the published root word. -/
theorem splitWeylEquiv_representative (P : Parameters) (hp : P.prime = 2) (w : DihedralGroup 6) :
    splitWeylEquiv P hp (fixedSplitRepresentative P hp w).val = rootRepresentative w := by
  cases w with
  | r i =>
    have h : (fixedSplitRepresentative P hp (.r i)).val =
        (foldedSplit P hp .arms * foldedSplit P hp .central) ^ i.val := by
      apply Subtype.ext
      exact (map_pow (elementaryInclusion P) _ _).trans
        (congrArg (fun x => x ^ i.val) (map_mul (elementaryInclusion P) _ _))
    exact (congrArg (splitWeylEquiv P hp) h).trans (by
      simp only [map_pow, map_mul, foldedSplit_image, rootRepresentative])
  | sr i =>
    have h : (fixedSplitRepresentative P hp (.sr i)).val = foldedSplit P hp .arms *
        (foldedSplit P hp .arms * foldedSplit P hp .central) ^ i.val := by
      apply Subtype.ext
      change elementaryInclusion P (_ * _ ^ _) = _
      simp only [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, foldedSplit]
    exact (congrArg (splitWeylEquiv P hp) h).trans (by
      simp only [map_pow, map_mul, foldedSplit_image, rootRepresentative])

/-- The published words exhaust the graph-field fixed matrix Weyl subgroup. -/
def splitDihedralEquiv (P : Parameters) (hp : P.prime = 2) :
    DihedralGroup 6 ≃* fixedSplitWeylSubgroup P :=
  rootDihedralEquiv.trans (fixedWeylEquiv P hp).symm

@[simp] theorem splitDihedralEquiv_apply (P : Parameters) (hp : P.prime = 2) (w : DihedralGroup 6) :
    splitDihedralEquiv P hp w = fixedSplitRepresentative P hp w := by
  apply (fixedWeylEquiv P hp).injective
  change fixedWeylEquiv P hp ((fixedWeylEquiv P hp).symm (rootDihedralEquiv w)) = _
  exact ((fixedWeylEquiv P hp).apply_symm_apply (rootDihedralEquiv w)).trans
    (Subtype.ext (splitWeylEquiv_representative P hp w).symm)


@[simp] theorem fixedWeylEquiv_val (P : Parameters) (hp : P.prime = 2)
    (w : fixedSplitWeylSubgroup P) :
    (fixedWeylEquiv P hp w).val = splitWeylEquiv P hp w.val := rfl

@[simp] theorem splitDihedralEquiv_val (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) :
    (splitDihedralEquiv P hp w).val.val = splitRepresentative P hp w :=
  congrArg (fun v : fixedSplitWeylSubgroup P => v.val.val) (splitDihedralEquiv_apply P hp w)

/-- Multiplicativity of the original split matrix representatives. -/
theorem splitRepresentative_mul (P : Parameters) (hp : P.prime = 2)
    (v w : DihedralGroup 6) :
    splitRepresentative P hp (v * w) = splitRepresentative P hp v * splitRepresentative P hp w := by
  simpa only [Subgroup.coe_mul, splitDihedralEquiv_val] using
    congrArg (fun x : fixedSplitWeylSubgroup P => x.val.val)
      (map_mul (splitDihedralEquiv P hp) v w)

/-- The original split matrix words are a homomorphism. -/
def splitRepresentativeHom (P : Parameters) (hp : P.prime = 2) :
    DihedralGroup 6 →* SplitGroup P where
  toFun := splitRepresentative P hp
  map_one' := splitRepresentative_one P hp
  map_mul' := splitRepresentative_mul P hp

@[simp] theorem splitRepresentativeHom_apply (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) : splitRepresentativeHom P hp w = splitRepresentative P hp w := rfl

/-- All twelve original split words are distinct. -/
theorem splitRepresentative_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (splitRepresentative P hp) := by
  intro v w h
  apply (splitDihedralEquiv P hp).injective
  apply Subtype.ext
  apply Subtype.ext
  exact (splitDihedralEquiv_val P hp v).trans (h.trans (splitDihedralEquiv_val P hp w).symm)

/-- Every fixed split Weyl matrix occurs among the published words. -/
theorem splitRepresentative_surjective_fixed (P : Parameters) (hp : P.prime = 2)
    (w : fixedSplitWeylSubgroup P) :
    ∃ v : DihedralGroup 6, splitRepresentative P hp v = w.val.val := by
  obtain ⟨v, rfl⟩ := (splitDihedralEquiv P hp).surjective w
  exact ⟨v, (splitDihedralEquiv_val P hp v).symm⟩

@[simp] theorem splitDihedralEquiv_sr_zero (P : Parameters) (hp : P.prime = 2) :
    (splitDihedralEquiv P hp (.sr 0)).val.val =
      weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1 :=
  (splitDihedralEquiv_val P hp (.sr 0)).trans
    ((splitRepresentative_simple P hp .arms).trans (elementaryInclusion_simple_arms P hp))

@[simp] theorem splitDihedralEquiv_sr_one (P : Parameters) (hp : P.prime = 2) :
    (splitDihedralEquiv P hp (.sr 1)).val.val = weylWord P 1 1 :=
  (splitDihedralEquiv_val P hp (.sr 1)).trans
    ((splitRepresentative_simple P hp .central).trans (elementaryInclusion_simple_central P hp))

/-- The entire graph-field fixed split Weyl subgroup has order twelve. -/
theorem fixedSplitWeylSubgroup_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (fixedSplitWeylSubgroup P) = 12 :=
  (Nat.card_congr (fixedWeylEquiv P hp).toEquiv).trans fixedRootWeylSubgroup_card

/-- The order of every published matrix word is exactly its dihedral order. -/
theorem orderOf_splitRepresentative (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) : orderOf (splitRepresentative P hp w) = orderOf w :=
  orderOf_injective (splitRepresentativeHom P hp) (splitRepresentative_injective P hp) w

/-- The actual four-factor matrix product has order six. -/
theorem orderOf_splitSimpleProduct (P : Parameters) (hp : P.prime = 2) :
    orderOf (weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1 * weylWord P 1 1) = 6 := by
  have h : splitRepresentative P hp (.r 1) =
      weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1 * weylWord P 1 1 := by
    change elementaryInclusion P ((_ * _) ^ (1 : ℕ)) = _
    simp only [pow_one, map_mul, elementaryInclusion_simple_arms,
      elementaryInclusion_simple_central]
  exact (congrArg orderOf h).symm.trans
    ((orderOf_splitRepresentative P hp (.r 1)).trans (DihedralGroup.orderOf_r_one (n := 6)))

end
end Triality.Standard.ConcreteBruhat
