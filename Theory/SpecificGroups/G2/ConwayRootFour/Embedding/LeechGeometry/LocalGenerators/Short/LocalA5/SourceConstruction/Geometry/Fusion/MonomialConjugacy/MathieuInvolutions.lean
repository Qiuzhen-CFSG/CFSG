module

public import Theory.SpecificGroups.G2.ConwayRootFour.MarkedLift
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialConjugacy.MathieuInvolutions.Bridge
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24FourTransitive
/-!
# Fixed-point-free involutions in the literal Mathieu code group

Every fixed-point-free coordinate involution is conjugate to the marked
hexacode translation `coordinateSwap`. Choose two permutation orbits and
use four-transitivity to place them on the first tetrad. The resulting
permutation lies in the marked-swap coset of its pointwise stabilizer.
The 960-parameter certificate reduces this coset to two representatives;
a separately checked Golay-preserving permutation fuses those representatives.

All conjugators belong to the original Golay coordinate automorphism group.
This supplies the Mathieu premise of the parent monomial fusion theorem.
Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, using 47.2, p.261 and the root-four conventions on p.269.
The four-transitivity and affine stabilizer APIs are the attributed ATLAS ports.
-/

@[expose] public section
open Atlas.Codes Atlas.G2.ConwayRootFour
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

namespace MathieuInvolutions

noncomputable def normalizedModel (a : Index) : Mathieu24CodeModel := coordinateSwap * model a

theorem swap_coordinates : ∀ x : Omega,
    pointEquiv (coordinateSwap.val x) = swap (pointEquiv x) := by decide

theorem normalized_coordinates (a : Index) (x : Omega) :
    pointEquiv ((normalizedModel a).val x) = norm a (pointEquiv x) := by
  change pointEquiv (coordinateSwap.val ((model a).val x)) = _
  rw [swap_coordinates, model_coordinates]
  rfl

theorem normalized_isConj (a : Index)
    (hp : Function.Involutive (normalizedModel a).val)
    (hfree : ∀ x, (normalizedModel a).val x ≠ x) :
    IsConj (normalizedModel a) coordinateSwap := by
  have hp' : ∀ x, norm a (norm a x) = x := by
    intro x
    obtain ⟨y,rfl⟩ := pointEquiv.surjective x
    rw [← normalized_coordinates, ← normalized_coordinates, hp]
  have hfree' : ∀ x, norm a x ≠ x := by
    intro x hx
    obtain ⟨y,rfl⟩ := pointEquiv.surjective x
    apply hfree y
    apply pointEquiv.injective
    rwa [normalized_coordinates]
  let w := model (witness a).2
  let r := if (witness a).1 then normalizedModel badIndex else coordinateSwap
  have hr (x : Omega) : pointEquiv (r.val x) =
      (if (witness a).1 then norm badIndex else swap) (pointEquiv x) := by
    dsimp only [r]
    split
    · exact normalized_coordinates _ _
    · exact swap_coordinates _
  have he : w * normalizedModel a = r * w := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply pointEquiv.injective
    change pointEquiv ((model (witness a).2).val ((normalizedModel a).val x)) =
      pointEquiv (r.val ((model (witness a).2).val x))
    rw [model_coordinates, normalized_coordinates, hr, model_coordinates]
    exact certificate a hp' hfree' (pointEquiv x)
  have hc : IsConj (normalizedModel a) r :=
    isConj_iff.mpr ⟨w,by rw [he]; simp [mul_assoc]⟩
  dsimp only [r] at hc
  split at hc
  · exact hc.trans bad_isConj
  · exact hc

end MathieuInvolutions

private theorem forward_involutive (p : Mathieu24CodeModel)
    (hp : Function.Involutive p.val.symm) : Function.Involutive p.val := by
  have he : p.val.symm = p.val := by
    simpa using (Function.Involutive.symm_eq_self_of_involutive p.val.symm hp).symm
  rwa [he] at hp

private theorem forward_free (p : Mathieu24CodeModel)
    (hfree : ∀ i, p.val.symm i ≠ i) : ∀ i, p.val i ≠ i := by
  intro i hi
  apply hfree i
  exact p.val.injective (by simpa using hi.symm)

private theorem two_orbits (p : Mathieu24CodeModel)
    (hp : Function.Involutive p.val) (hfree : ∀ i, p.val i ≠ i) :
    ∃ e : Fin 4 ↪ Omega, ∀ k, p.val (e k) = e (coordinateSwap.val ((0,0),k)).2 := by
  let a : Omega := ((0,0),0)
  have hex : ∃ b : Omega, b ≠ a ∧ b ≠ p.val a := by
    by_cases h : ((0,0),1) = p.val a
    · exact ⟨((0,0),2), by decide, by rw [← h]; decide⟩
    · exact ⟨((0,0),1), by decide, h⟩
  obtain ⟨b, hba, hbp⟩ := hex
  have hab : a ≠ b := hba.symm
  have hpa : p.val a ≠ a := hfree a
  have hpb : p.val b ≠ b := hfree b
  have hapb : a ≠ p.val b := by
    intro h
    apply hbp
    rw [h, hp]
  have hpapb : p.val a ≠ p.val b := fun h => hab (p.val.injective h)
  let e : Fin 4 ↪ Omega := ⟨![a,b,p.val a,p.val b], by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      dsimp at h ⊢ <;>
      first
      | rfl
      | contradiction
      | exact False.elim (hpa h.symm)
      | exact False.elim (hpb h.symm)
      | exact False.elim (hbp h.symm)
      | exact False.elim (hapb h.symm)
      | exact False.elim (hpapb h.symm)⟩
  refine ⟨e, ?_⟩
  intro k
  fin_cases k <;> dsimp [e]
  · rfl
  · rfl
  · exact hp a
  · exact hp b

/-- Four-transitivity moves two orbits to the marked first tetrad. -/
theorem mathieu_involution_normalize_tetrad (p : Mathieu24CodeModel)
    (hp : Function.Involutive p.val.symm) (hfree : ∀ i, p.val.symm i ≠ i) :
    ∃ a : Mathieu24CodeModel,
      ∃ s : TetradPointStabilizer (0,0),
        a * p * a⁻¹ = coordinateSwap * s.val := by
  have hp' := forward_involutive p hp
  obtain ⟨e, he⟩ := two_orbits p hp' (forward_free p hfree)
  obtain ⟨a, ha⟩ := orderedFour_to_tetrad e (0,0)
  let q := a * p * a⁻¹
  have hq (k : Fin 4) : q.val ((0,0),k) = coordinateSwap.val ((0,0),k) := by
    change a.val (p.val (a.val.symm ((0,0),k))) = _
    rw [show a.val.symm ((0,0),k) = e k from a.val.symm_apply_eq.mpr (ha k).symm, he, ha]
    have hcol : ∀ k : Fin 4, (coordinateSwap.val ((0,0),k)).1 = (0,0) := by decide
    exact Prod.ext (hcol k).symm rfl
  let s := coordinateSwap⁻¹ * q
  have hs : s ∈ TetradPointStabilizer (0,0) := by
    apply (tetradPointStabilizer_mem _ _).mpr
    intro k
    change coordinateSwap.val.symm (q.val ((0,0),k)) = _
    rw [hq, coordinateSwap.val.symm_apply_apply]
  refine ⟨a, ⟨s, hs⟩, ?_⟩
  change q = coordinateSwap * (coordinateSwap⁻¹ * q)
  simp

/-- Conjugacy in the actual Golay coordinate automorphism group. -/
theorem mathieu_fixedPointFree_involution_isConj_coordinateSwap (p : Mathieu24CodeModel)
    (hp : Function.Involutive p.val.symm) (hfree : ∀ i, p.val.symm i ≠ i) :
    IsConj p coordinateSwap := by
  obtain ⟨a,s,hs⟩ := mathieu_involution_normalize_tetrad p hp hfree
  obtain ⟨j,hj⟩ := MathieuInvolutions.stabilizerElement_surjective s
  let q := a * p * a⁻¹
  have hq : q = MathieuInvolutions.normalizedModel j := by
    change a * p * a⁻¹ = coordinateSwap * (MathieuInvolutions.stabilizerElement j).val
    rw [hj]
    exact hs
  have hp' := forward_involutive p hp
  have hfree' := forward_free p hfree
  have hqi : Function.Involutive q.val := by
    intro i
    change a.val (p.val (a.val.symm (a.val (p.val (a.val.symm i))))) = i
    rw [a.val.symm_apply_apply, hp', a.val.apply_symm_apply]
  have hqf : ∀ i, q.val i ≠ i := by
    intro i hi
    apply hfree' (a.val.symm i)
    apply a.val.injective
    exact hi.trans (a.val.apply_symm_apply i).symm
  exact (isConj_iff.mpr ⟨a,rfl⟩ : IsConj p q).trans
    (by rw [hq] at hqi hqf ⊢; exact MathieuInvolutions.normalized_isConj j hqi hqf)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
