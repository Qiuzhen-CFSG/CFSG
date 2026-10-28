module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Factors
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Scalar

/-!
# A limitation of the proposed diagonal uniqueness step

Let S = SL₂(4), j the flip matrix, x = diag(ω,ω²), and u the upper
unitriangular involution. The graphs of entrywise Frobenius and conjugation
by j are distinct full diagonal A₅ subgroups of S × S. Both contain
(j,j) and (x,x⁻¹), which generate an S₃ acting without fixed vectors.
Only the Frobenius graph contains (u,u).

The faithful action from `Factors` identifies (j,j) with the literal
`graph` action and (u,u) with `rootC 1`. Both diagonals commute with
the long SL₂ on coordinates (1,2) and (3,4). Thus the restriction to the
common S₃ alone cannot perform the diagonal selection asserted in
Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.284.

This is a counterexample to that linear uniqueness inference, not to the
full source theorem or the requested Leech construction. Neither diagonal
is asserted here to lift to the actual Leech quotient. The ambient order
obstruction in `OrderObstruction` is available to exclude unwanted lifts.
-/

open Matrix Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalAmbiguity
abbrev K := GoldenFour
abbrev S := SL(2,K)
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def cubic : S := ⟨!![goldenFourTau,0;0,goldenFourTau ^ 2], by decide +kernel⟩
def frob : S →* S := Matrix.SpecialLinearGroup.map (frobenius K 2)
def twist : S →* S := (MulAut.conj (flip (K := K))).toMonoidHom

def diagonal (f : S →* S) : Subgroup (S × S) := ((MonoidHom.id S).prod f).range

theorem mem_diagonal (f : S →* S) (a b : S) : (a,b) ∈ diagonal f ↔ f a = b := by
  constructor
  · rintro ⟨c, h⟩
    have h1 : c = a := congrArg Prod.fst h
    have h2 : f c = b := congrArg Prod.snd h
    exact h1 ▸ h2
  · intro h
    exact ⟨a, Prod.ext rfl h⟩

theorem frob_flip : frob (flip (K := K)) = flip := by decide +kernel
theorem twist_flip : twist (flip (K := K)) = flip := by simp [twist]
theorem frob_cubic : frob cubic = cubic⁻¹ := by decide +kernel
theorem twist_cubic : twist cubic = cubic⁻¹ := by decide +kernel
theorem frob_shear : frob shear = shear := by decide +kernel
theorem twist_shear : twist shear ≠ shear := by decide +kernel
theorem cubic_cube : cubic ^ 3 = 1 := by decide +kernel
theorem cubic_ne : cubic ≠ 1 := by decide +kernel

theorem frob_bijective : Function.Bijective frob := by
  have hi : Function.Involutive frob := by
    intro a
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change (a.val i j ^ 2) ^ 2 = a.val i j
    rw [← pow_mul]
    simpa only [goldenFour_card] using FiniteField.pow_card (a.val i j)
  exact hi.bijective

/-- The first projection identifies the graph with SL₂(4). -/
def diagonalEquiv (f : S →* S) : S ≃* diagonal f :=
  MonoidHom.ofInjective (show Function.Injective ((MonoidHom.id S).prod f) from
    fun _ _ h => congrArg Prod.fst h)

def diagonalAlt (f : S →* S) : diagonal f ≃* alternatingGroup (Fin 5) :=
  (diagonalEquiv f).symm.trans goldenFourSLAlternatingFive

theorem full_projections (f : S →* S) (hf : Function.Surjective f) :
    Function.Surjective (fun x : diagonal f => x.val.1) ∧
    Function.Surjective (fun x : diagonal f => x.val.2) := by
  constructor
  · intro a
    exact ⟨⟨(a, f a), (mem_diagonal f a (f a)).mpr rfl⟩, rfl⟩
  · intro a
    obtain ⟨b, rfl⟩ := hf a
    exact ⟨⟨(b, f b), (mem_diagonal f b (f b)).mpr rfl⟩, rfl⟩

/-- The Frobenius graph projects onto both SL₂ factors. -/
theorem frob_full_projections :
    Function.Surjective (fun x : diagonal frob => x.val.1) ∧
    Function.Surjective (fun x : diagonal frob => x.val.2) :=
  full_projections frob frob_bijective.surjective

/-- The other diagonal also projects onto both SL₂ factors. -/
theorem twist_full_projections :
    Function.Surjective (fun x : diagonal twist => x.val.1) ∧
    Function.Surjective (fun x : diagonal twist => x.val.2) :=
  full_projections twist (MulAut.conj (flip (K := K))).surjective

def common : Subgroup (S × S) :=
  Subgroup.closure {(flip (K := K),flip (K := K)), (cubic,cubic⁻¹)}

theorem common_le_frob : common ≤ diagonal frob := by
  apply (Subgroup.closure_le _).mpr
  rintro _ (rfl | rfl)
  · exact (mem_diagonal _ _ _).mpr frob_flip
  · exact (mem_diagonal _ _ _).mpr frob_cubic

theorem common_le_twist : common ≤ diagonal twist := by
  apply (Subgroup.closure_le _).mpr
  rintro _ (rfl | rfl)
  · exact (mem_diagonal _ _ _).mpr twist_flip
  · exact (mem_diagonal _ _ _).mpr twist_cubic

theorem shear_mem_frob : (shear (K := K),shear (K := K)) ∈ diagonal frob :=
  (mem_diagonal _ _ _).mpr frob_shear

theorem shear_not_mem_twist : (shear (K := K),shear (K := K)) ∉ diagonal twist := by
  simpa only [mem_diagonal] using twist_shear

theorem diagonals_ne : diagonal frob ≠ diagonal twist := by
  intro h
  exact shear_not_mem_twist (h ▸ shear_mem_frob)

theorem cubic_inv : cubic⁻¹ =
    (⟨!![goldenFourTau ^ 2,0;0,goldenFourTau], by decide +kernel⟩ : S) := by
  apply Subtype.ext
  change (!![goldenFourTau,0;0,goldenFourTau ^ 2] : Matrix (Fin 2) (Fin 2) K).adjugate = _
  simp [Matrix.adjugate_fin_two, CharTwo.neg_eq]

/-- The common order-three element has no nonzero fixed vector. -/
theorem cubic_no_fixed (v : Fin 6 → K)
    (h : pairRepresentation (cubic,cubic⁻¹) v = v) : v = 0 := by
  have hfirst : ∀ a : K, goldenFourTau * a = a → a = 0 := by decide +kernel
  have hsecond : ∀ a : K, goldenFourTau ^ 2 * a = a → a = 0 := by decide +kernel
  have he (i : Fin 6) : pairAction (cubic,cubic⁻¹) v i = v i := congrFun h i
  rw [cubic_inv] at he
  funext i
  fin_cases i
  · apply hfirst; simpa [pairAction, cubic] using he 0
  · apply hsecond; simpa [pairAction, cubic] using he 1
  · apply hsecond; simpa [pairAction, cubic] using he 2
  · apply hfirst; simpa [pairAction, cubic] using he 3
  · apply hfirst; simpa [pairAction, cubic] using he 4
  · apply hsecond; simpa [pairAction, cubic] using he 5

def longAction (a : S) (v : Fin 6 → K) : Fin 6 → K :=
  ![v 0, a.val 0 0 * v 1 + a.val 0 1 * v 2,
    a.val 1 0 * v 1 + a.val 1 1 * v 2,
    a.val 0 0 * v 3 + a.val 0 1 * v 4,
    a.val 1 0 * v 3 + a.val 1 1 * v 4, v 5]

theorem pairAction_commutes_long (p : S × S) (a : S) (v : Fin 6 → K) :
    pairAction p (longAction a v) = longAction a (pairAction p v) := by
  funext i
  fin_cases i <;> simp [pairAction, longAction] <;> ring

def longMatrix (a : S) : SL(3,K) :=
  ⟨!![1,0,0;0,a.val 0 0,a.val 0 1;0,a.val 1 0,a.val 1 1], by
    have hd := a.property
    rw [Matrix.det_fin_two] at hd
    simpa [Matrix.det_fin_three] using hd⟩

theorem longAction_eq (a : S) (v : Fin 6 → K) :
    longAction a v = Atlas.G2.ConwayRootFour.OctonionLocals.action
      (Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization.blockHom
        (longMatrix a)) v := by
  rw [Atlas.G2.ConwayRootFour.OctonionLocals.action_block]
  have hd : a.val 0 0 * a.val 1 1 - a.val 0 1 * a.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using a.property
  funext i
  fin_cases i <;>
    simp [longAction, longMatrix,
      Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization.cofactor,
      Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      CharTwo.neg_eq, hd, CharTwo.sub_eq_add] <;> ring_nf at *

theorem rootC_mem_frob :
    Atlas.G2.ConwayRootFour.OctonionLocals.action (Atlas.G2.rootC (1 : K)) ∈
      (diagonal frob).map pairRepresentation := by
  exact ⟨(shear (K := K),shear (K := K)), shear_mem_frob, LinearEquiv.ext shear_action⟩

theorem rootC_not_mem_twist :
    Atlas.G2.ConwayRootFour.OctonionLocals.action (Atlas.G2.rootC (1 : K)) ∉
      (diagonal twist).map pairRepresentation := by
  rintro ⟨p, hp, he⟩
  have hs : pairRepresentation (shear (K := K),shear (K := K)) =
      Atlas.G2.ConwayRootFour.OctonionLocals.action (Atlas.G2.rootC (1 : K)) :=
    LinearEquiv.ext shear_action
  have hh := pairRepresentation_injective (he.trans hs.symm)
  exact shear_not_mem_twist (hh ▸ hp)


def d3Value : DihedralGroup 3 → S
  | .r i => cubic ^ i.val
  | .sr i => flip * cubic ^ i.val

def d3Hom : DihedralGroup 3 →* S where
  toFun := d3Value
  map_one' := rfl
  map_mul' := by decide +kernel

theorem d3Hom_injective : Function.Injective d3Hom := by decide +kernel

def d3Pair : DihedralGroup 3 →* S × S :=
  ((MonoidHom.id S).prod frob).comp d3Hom

theorem d3Pair_injective : Function.Injective d3Pair := by
  intro a b h
  exact d3Hom_injective (congrArg Prod.fst h)

theorem d3Pair_r : d3Pair (.r 1) = (cubic,cubic⁻¹) := by decide +kernel

theorem d3Pair_sr : d3Pair (.sr 0) = (flip (K := K),flip (K := K)) := by decide +kernel

theorem common_eq_range : common = d3Pair.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ (rfl | rfl)
    · exact ⟨.sr 0, d3Pair_sr⟩
    · exact ⟨.r 1, d3Pair_r⟩
  · rintro _ ⟨a, rfl⟩
    have hr : d3Pair (.r 1) ∈ common := by
      rw [d3Pair_r]
      exact Subgroup.subset_closure (by simp)
    have hs : d3Pair (.sr 0) ∈ common := by
      rw [d3Pair_sr]
      exact Subgroup.subset_closure (by simp)
    cases a with
    | r i =>
      have hi : (DihedralGroup.r i : DihedralGroup 3) = (.r 1) ^ i.val := by
        simp
      rw [hi, map_pow]
      exact common.pow_mem hr _
    | sr i =>
      have hi : (DihedralGroup.sr i : DihedralGroup 3) = .sr 0 * (.r 1) ^ i.val := by
        simp
      rw [hi, map_mul, map_pow]
      exact common.mul_mem hs (common.pow_mem hr _)

theorem common_card : Nat.card common = 6 := by
  rw [common_eq_range, ← Nat.card_congr (MonoidHom.ofInjective d3Pair_injective).toEquiv]
  exact DihedralGroup.nat_card

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalAmbiguity
