module

public import Theory.SpecificGroups.G2.MultiplierFourBound.TwoPrimary.RootDefects
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
import Mathlib.Tactic.Group

/-!
# The common root defect in the G₂(4) cover

The explicit octonion calculation gives a useful part of the exceptional
small-field argument.  The A, B and E defects vanish, the C, D and F defects
are conjugate, and every positive-root defect is contained in the C defect.
The latter has order at most two by `RootDefects`.

The final cross-root collection identities are deliberately not asserted here:
they are the separate Griess calculation needed to prove `ProductCompatible`.
-/

@[expose] public section

open scoped commutatorElement
namespace Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary.ExceptionalRelations

open MultiplierOrdinary Subgroup Atlas.SplitOctonion Explicit Atlas.G2
open Atlas.G2.ShortRootProducts

private theorem commute_lifts_of_separating_scalar
    {F E G : Type*} [Field F] [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (u : Multiplicative F →* G) (v : E)
    (hcomm : ∀ x : F, Commute (u (.ofAdd x)) (f v))
    (t : G) (c : F) (hc : c ≠ 1)
    (hu : ∀ x : F, t * u (.ofAdd x) * t⁻¹ = u (.ofAdd (c * x)))
    (hv : t * f v * t⁻¹ = f v)
    {w : E} (hw : f w ∈ u.range) : Commute w v := by
  choose s hs using fun x : F => hf (u (.ofAdd x))
  let B : F → E := fun x => ⁅s x, v⁆
  have hB (x : F) : B x ∈ center E := by
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement, hs]
    exact (hcomm x).commutator_eq
  have hBa (x y : F) : B (x+y) = B x * B y := by
    have he : f (s (x+y)) = f (s x * s y) := by
      rw [map_mul, hs, hs, hs, ← map_mul]; rfl
    dsimp [B]
    rw [CentralExtension.commutator_eq_of_image_eq f hk he rfl,
      commutatorElement_mul_left_eq_conj_mul]
    change s x * B y * (s x)⁻¹ * B x = B x * B y
    rw [mem_center_iff.mp (hB y) (s x), mul_assoc (B y), mul_inv_cancel,
      mul_one, mem_center_iff.mp (hB x) (B y)]
  obtain ⟨z, hz⟩ := hf t
  have hBs (x : F) : B (c*x) = B x := by
    have hx : f (s (c*x)) = f (z * s x * z⁻¹) := by
      rw [map_mul, map_mul, map_inv, hs, hs, hz, hu]
    have hy : f v = f (z * v * z⁻¹) := by
      rw [map_mul, map_mul, map_inv, hz, hv]
    dsimp [B]
    rw [CentralExtension.commutator_eq_of_image_eq f hk hx hy,
      ← conjugate_commutatorElement]
    change z * B x * z⁻¹ = B x
    rw [mem_center_iff.mp (hB x) z, mul_assoc, mul_inv_cancel, mul_one]
  have hzero (y : F) : B ((c-1)*y) = 1 := by
    have H := hBs y
    rw [show c*y = (c-1)*y+y by ring, hBa] at H
    exact mul_right_cancel (H.trans (one_mul _).symm)
  obtain ⟨x, hx⟩ := hw
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← CentralExtension.commutator_eq_of_image_eq f hk
    ((hs x.toAdd).trans hx) (show f v = f v from rfl)]
  change B x.toAdd = 1
  simpa only [mul_inv_cancel_left₀ (sub_ne_zero.mpr hc)] using
    hzero ((c-1)⁻¹*x.toAdd)

variable {E : Type*} [Group E]

private theorem rootDefect_le_of_conjugate (f : E →* FourBase)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (i j : Fin 6) (g : FourBase)
    (h : ∀ x, g * positiveRoot i x * g⁻¹ = positiveRoot j x) :
    rootDefect f i ≤ rootDefect f j := by
  obtain ⟨z, hz⟩ := hf g
  apply commutator_le.mpr
  intro v hv w hw
  have hc (x : E) (hx : x ∈ rootPreimage f i) :
      z*x*z⁻¹ ∈ rootPreimage f j := by
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    change positiveRoot j a.toAdd = f (z*x*z⁻¹)
    rw [map_mul, map_mul, map_inv, hz, ← ha]
    exact (h a.toAdd).symm
  have H := commutator_mem_commutator (hc v hv) (hc w hw)
  rw [← conjugate_commutatorElement] at H
  have hcentral : ⁅v,w⁆ ∈ center E :=
    rootDefect_le_center f hk i (commutator_mem_commutator hv hw)
  simpa only [rootDefect, mem_center_iff.mp hcentral z, mul_assoc,
    mul_inv_cancel, mul_one] using H

private theorem rootDefect_eq_of_conjugate (f : E →* FourBase)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (i j : Fin 6) (g : FourBase)
    (h : ∀ x, g * positiveRoot i x * g⁻¹ = positiveRoot j x) :
    rootDefect f i = rootDefect f j := by
  apply le_antisymm (rootDefect_le_of_conjugate f hf hk i j g h)
  apply rootDefect_le_of_conjugate f hf hk j i g⁻¹
  intro x
  rw [← h x]
  group

private theorem weylS_rootC_four (a : FourField) :
    weylS * rootC a * weylS⁻¹ = rootD a := by
  rw [weylS_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [weylS,weylSEquiv,weylSLinear,weylSApply,
    rootC,rootCEquiv,rootCLinear,rootCApply,rootD,rootDEquiv,rootDLinear,rootDApply]
  all_goals ring

private theorem rootDefect_long_eq (f : E →* FourBase)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    rootDefect f 0 = rootDefect f 1 ∧ rootDefect f 1 = rootDefect f 4 := by
  constructor
  · exact rootDefect_eq_of_conjugate f hf hk 0 1 weylR weylR_rootA
  · exact rootDefect_eq_of_conjugate f hf hk 1 4 weylS weylS_rootB

private theorem rootDefect_short_eq (f : E →* FourBase)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    rootDefect f 2 = rootDefect f 3 ∧ rootDefect f 3 = rootDefect f 5 := by
  constructor
  · exact rootDefect_eq_of_conjugate f hf hk 2 3 weylS weylS_rootC_four
  · exact rootDefect_eq_of_conjugate f hf hk 3 5 weylR weylR_rootD

private theorem rootA_commute_short (j : Fin 6) (hj : j = 2 ∨ j = 3) (a b : FourField) :
    Commute (rootA a) (positiveRoot j b) := by
  rcases hj with rfl | rfl
  all_goals apply Subtype.ext; apply LinearEquiv.ext; intro x
  all_goals funext i; fin_cases i <;>
    simp [positiveRoot, rootA,rootAEquiv,rootALinear,rootAApply,
      rootC,rootCEquiv,rootCLinear,rootCApply,rootD,rootDEquiv,rootDLinear,rootDApply] <;> ring

private theorem rootA_lifts_commute_short (f : E →* FourBase)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (j : Fin 6) (hj : j = 2 ∨ j = 3) {v w : E}
    (hv : v ∈ rootPreimage f 0) (hw : w ∈ rootPreimage f j) : Commute v w := by
  obtain ⟨a, ha⟩ := hw
  have hcard : 1 < Nat.card FourFieldˣ := by
    rw [Nat.card_units, GaloisField.card 2 2 (by decide)]; decide
  let : Nontrivial FourFieldˣ := (Finite.one_lt_card_iff_nontrivial).mp hcard
  obtain ⟨c, hc⟩ := exists_ne (1 : FourFieldˣ)
  have hc' : (c : FourField) ≠ 1 := fun h => hc (Units.ext h)
  let t : FourBase := if j = 2 then torus 1 c else torus c 1
  apply commute_lifts_of_separating_scalar f hf hk (positiveRootHom 0) w
    (w := v) (c := (c : FourField)) (t := t) (hc := hc')
    (hcomm := ?_) (hu := ?_) (hv := ?_) hv
  · intro x
    rw [← ha]
    exact rootA_commute_short j hj x a.toAdd
  · intro x
    rcases hj with rfl | rfl
    · dsimp [t]
      change torus 1 c * rootA x * (torus 1 c)⁻¹ = rootA ((c : FourField) * x)
      rw [torus_rootA]
      simp
    · dsimp [t]
      change torus c 1 * rootA x * (torus c 1)⁻¹ = rootA ((c : FourField) * x)
      rw [torus_rootA]
      simp
  · rw [← ha]
    rcases hj with rfl | rfl
    · dsimp [t]
      change torus 1 c * rootC a.toAdd * (torus 1 c)⁻¹ = rootC a.toAdd
      rw [torus_rootC]
      simp
    · dsimp [t]
      change torus c 1 * rootD a.toAdd * (torus c 1)⁻¹ = rootD a.toAdd
      rw [torus_rootD]
      simp

private theorem rootD_rootC_commutator (a : FourField) :
    ⁅rootD (1 : FourField), rootC a⁆ = rootA a := by
  have h := product_rootC_conjugate (F := FourField) a (1 : FourField)
  have h' : rootC a * rootD (1 : FourField) * rootC a * (rootD 1)⁻¹ = rootA a := by
    simpa only [MulAut.conj_apply, mul_assoc, mul_one] using h
  have hCD : ⁅rootC a, rootD (1 : FourField)⁆ = rootA a := by
    rw [commutatorElement_def]
    have hc : (rootC a)⁻¹ = rootC a := by
      apply inv_eq_of_mul_eq_one_left
      calc
        rootC a * rootC a = rootC (a + a) := rootC_add a a
        _ = rootC 0 := by rw [CharTwo.add_self_eq_zero]
        _ = 1 := rootC_zero
    rw [hc]
    exact h'
  calc
    ⁅rootD (1 : FourField), rootC a⁆ = ⁅rootC a, rootD 1⁆⁻¹ :=
      (commutatorElement_inv _ _).symm
    _ = (rootA a)⁻¹ := congrArg Inv.inv hCD
    _ = rootA a := by
      apply inv_eq_of_mul_eq_one_left
      calc
        rootA a * rootA a = rootA (a + a) := rootA_add a a
        _ = rootA 0 := by rw [CharTwo.add_self_eq_zero]
        _ = 1 := rootA_zero

private theorem rootDefect_long_bot (f : E →* FourBase)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    rootDefect f 0 = ⊥ ∧ rootDefect f 1 = ⊥ ∧ rootDefect f 4 = ⊥ := by
  have hA : rootDefect f 0 = ⊥ := by
    apply le_bot_iff.mp
    apply commutator_le.mpr
    intro v hv w hw
    obtain ⟨a, ha⟩ := hv
    obtain ⟨c, hc⟩ := hf (rootC a.toAdd)
    obtain ⟨d, hd⟩ := hf (rootD (1 : FourField))
    have hdc : f ⁅d,c⁆ = f v := by
      rw [map_commutatorElement, hd, hc, rootD_rootC_commutator]
      exact ha
    have hwd : Commute w d := rootA_lifts_commute_short f hf hk 3 (Or.inr rfl) hw
      ⟨.ofAdd 1, hd.symm⟩
    have hwc : Commute w c := rootA_lifts_commute_short f hf hk 2 (Or.inl rfl) hw
      ⟨.ofAdd a.toAdd, hc.symm⟩
    change ⁅v,w⁆ = 1
    rw [CentralExtension.commutator_eq_of_image_eq f hk hdc.symm rfl]
    exact ((hwd.mul_right hwc).mul_right hwd.inv_right |>.mul_right hwc.inv_right).symm.commutator_eq
  obtain ⟨hAB, hBE⟩ := rootDefect_long_eq f hf hk
  exact ⟨hA, hAB.symm.trans hA, hBE.symm.trans (hAB.symm.trans hA)⟩

/-- Every positive-root defect is contained in the one short-root defect. -/
public theorem rootDefect_le_short (f : E →* FourBase)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) (i : Fin 6) :
    rootDefect f i ≤ rootDefect f 2 := by
  obtain ⟨hA,hB,hE⟩ := rootDefect_long_bot f hf hk
  obtain ⟨hCD,hDF⟩ := rootDefect_short_eq f hf hk
  fin_cases i
  · change rootDefect f 0 ≤ rootDefect f 2
    exact (by rw [hA]; exact bot_le)
  · change rootDefect f 1 ≤ rootDefect f 2
    exact (by rw [hB]; exact bot_le)
  · exact le_rfl
  · change rootDefect f 3 ≤ rootDefect f 2
    rw [← hCD]
  · change rootDefect f 4 ≤ rootDefect f 2
    exact (by rw [hE]; exact bot_le)
  · change rootDefect f 5 ≤ rootDefect f 2
    rw [← hDF, ← hCD]

end Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary.ExceptionalRelations

end
