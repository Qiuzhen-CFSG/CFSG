module
public import Theory.Representation.BinaryDoubledNaturalCentralizer
public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Trivial centralizer of the doubled binary row

Elementary transvections kill the off-diagonal maps between the natural and
contragredient summands. The existing natural-module scalar calculation then
identifies the diagonal blocks with binary scalars. Invertibility forces both
scalars to be one. The dot-product equivalence transports the calculation to
the actual natural-plus-dual action, keeping its original component marking.

DoubledOrbitNormalizer uses this result to identify the kernel of conjugation
on the component with the kernel of the literal normalizer action on W.
Source: Aschbacher--Smith, B.5.1(3), H.9 and 12.2.2, printed pp.99,389,795.
The block argument follows the existing SL3FourNaturalDual normalizer
centralizer calculation, with binary scalars and degrees four and five.
-/

public noncomputable section
open BinaryLinear.OuterCyclic BinaryNaturalDual
open scoped CharTwo
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit

private def elementary {n : ℕ} (i j : Fin n) (h : i ≠ j) : LinearGroup n :=
  BinaryLinear.transvection (Pi.single i 1) (LinearMap.proj j) (by simp [h.symm])

private theorem elementary_apply {n : ℕ} (i j : Fin n) (h : i ≠ j) (v : Space n) :
    elementary i j h v = v + Pi.single i (v j) := by
  change v + v j • Pi.single i 1 = _
  congr 1
  ext k
  by_cases hk : k = i <;> simp [hk]

private theorem graph_elementary {n : ℕ} (i j : Fin n) (h : i ≠ j) (v : Space n) :
    graphLinear n (elementary i j h) v = v + Pi.single j (v i) := by
  apply (dotProductEquiv (ZMod 2) (Fin n)).injective
  apply LinearMap.ext
  intro w
  have he := graphLinear_dotProduct (elementary i j h) v ((elementary i j h) w)
  have hs : elementary i j h (elementary i j h w) = w := by
    exact (elementary i j h).left_inv w
  rw [hs, elementary_apply] at he
  change dotProduct _ w = dotProduct _ w
  simpa [dotProduct_add, add_dotProduct, dotProduct_single, single_dotProduct, mul_comm] using he

private theorem natural_scalar {n : ℕ} (hn : n = 4 ∨ n = 5)
    (f : Space n →+ Space n)
    (hf : ∀ (g : LinearGroup n) v, f (g v) = g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let : NeZero n := ⟨by omega⟩
  exact Representation.BinaryDoubledNatural.natural_centralizer_scalar (by omega) f
    (fun g v => hf (slEquivLinear n g) v)

private theorem cross_zero {n : ℕ} (hn : n = 4 ∨ n = 5)
    (f : Space n →+ Space n)
    (hf : ∀ (g : LinearGroup n) v, f (g v) = graphLinear n g (f v)) : f = 0 := by
  have hsingle {i j : Fin n} (hij : i ≠ j) (a : ZMod 2) :
      f (Pi.single i a) = Pi.single j (f (Pi.single j a) i) := by
    have h := hf (elementary i j hij) (Pi.single j a)
    rw [elementary_apply, graph_elementary, map_add] at h
    simpa using add_left_cancel h
  have hs (i : Fin n) (a : ZMod 2) : f (Pi.single i a) = 0 := by
    funext k
    obtain ⟨j, hij, hkj⟩ : ∃ j : Fin n, i ≠ j ∧ k ≠ j := by
      rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases k <;> decide
    rw [hsingle hij]
    simp [Pi.single_eq_of_ne hkj]
  apply AddMonoidHom.ext
  intro v
  have hv : v = ∑ i : Fin n, Pi.single i (v i) := by
    funext i
    simp [Finset.sum_apply]
  rw [hv, map_sum]
  simp [hs]

private theorem graph_twice {n : ℕ} (g : LinearGroup n) :
    graphLinear n (graphLinear n g) = g := by
  change (graphLinear n * graphLinear n) g = g
  rw [← pow_two, graphLinear_sq]
  rfl

private theorem pair_scalars {n : ℕ} (hn : n = 4 ∨ n = 5)
    (f : Module.End (ZMod 2) (Space n × Space n))
    (hf : ∀ (g : LinearGroup n) v,
      f (g v.1, graphLinear n g v.2) = (g (f v).1, graphLinear n g (f v).2)) :
    ∃ a b : ZMod 2, ∀ v, f v = (a • v.1, b • v.2) := by
  let f₁₁ := ((LinearMap.fst _ _ _).comp (f.comp (LinearMap.inl _ _ _))).toAddMonoidHom
  let f₁₂ := ((LinearMap.fst _ _ _).comp (f.comp (LinearMap.inr _ _ _))).toAddMonoidHom
  let f₂₁ := ((LinearMap.snd _ _ _).comp (f.comp (LinearMap.inl _ _ _))).toAddMonoidHom
  let f₂₂ := ((LinearMap.snd _ _ _).comp (f.comp (LinearMap.inr _ _ _))).toAddMonoidHom
  have h₁₁ (g : LinearGroup n) (v : Space n) : f₁₁ (g v) = g (f₁₁ v) := by
    simpa [f₁₁] using congrArg Prod.fst (hf g (v,0))
  have h₁₂ (g : LinearGroup n) (v : Space n) : f₁₂ (g v) = graphLinear n g (f₁₂ v) := by
    simpa [f₁₂, graph_twice] using congrArg Prod.fst (hf (graphLinear n g) (0,v))
  have h₂₁ (g : LinearGroup n) (v : Space n) : f₂₁ (g v) = graphLinear n g (f₂₁ v) := by
    simpa [f₂₁] using congrArg Prod.snd (hf g (v,0))
  have h₂₂ (g : LinearGroup n) (v : Space n) : f₂₂ (g v) = g (f₂₂ v) := by
    simpa [f₂₂, graph_twice] using congrArg Prod.snd (hf (graphLinear n g) (0,v))
  obtain ⟨a, ha⟩ := natural_scalar hn f₁₁ h₁₁
  obtain ⟨b, hb⟩ := natural_scalar hn f₂₂ h₂₂
  have hz₁ := cross_zero hn f₁₂ h₁₂
  have hz₂ := cross_zero hn f₂₁ h₂₁
  refine ⟨a,b,fun v => ?_⟩
  have he : f v = f (v.1,0) + f (0,v.2) := by rw [← map_add]; simp
  have h₁ : (f (0,v.2)).1 = 0 := DFunLike.congr_fun hz₁ v.2
  have h₂ : (f (v.1,0)).2 = 0 := DFunLike.congr_fun hz₂ v.1
  rw [he]
  exact Prod.ext (by simpa [h₁, f₁₁] using ha v.1) (by simpa [h₂, f₂₂] using hb v.2)

private def pairCoordinates (n : ℕ) : (Space n × Space n) ≃ₗ[ZMod 2] CoordinateSpace n :=
  (LinearEquiv.refl (ZMod 2) (Space n)).prodCongr (dotProductEquiv (ZMod 2) (Fin n))

private theorem pairCoordinates_action {n : ℕ} (g : LinearGroup n) (v : Space n × Space n) :
    pairCoordinates n (g v.1, graphLinear n g v.2) =
      naturalDualRepresentation g (pairCoordinates n v) := by
  rw [naturalDualRepresentation_apply]
  refine Prod.ext rfl ?_
  apply LinearMap.ext
  intro w
  change dotProduct (graphLinear n g v.2) w = dotProduct v.2 (g.symm w)
  simpa only [g.apply_symm_apply] using graphLinear_dotProduct g v.2 (g.symm w)

/-- The only invertible binary operator commuting with the natural-plus-dual
component in degrees four and five is the identity. -/
theorem naturalDual_centralizer_trivial {n : ℕ} (hn : n = 4 ∨ n = 5)
    (f : CoordinateSpace n ≃ₗ[ZMod 2] CoordinateSpace n)
    (hf : ∀ (g : LinearGroup n) v,
      f (naturalDualRepresentation g v) = naturalDualRepresentation g (f v)) :
    f = 1 := by
  let e := pairCoordinates n
  let q := (e.trans f).trans e.symm
  have hq (g : LinearGroup n) v :
      q (g v.1, graphLinear n g v.2) = (g (q v).1, graphLinear n g (q v).2) := by
    apply e.injective
    change e (e.symm (f (e _))) = e _
    rw [e.apply_symm_apply, pairCoordinates_action, hf, pairCoordinates_action]
    congr 1
    exact (e.apply_symm_apply (f (e v))).symm
  obtain ⟨a,b,hab⟩ := pair_scalars hn q.toLinearMap hq
  have hz (c : ZMod 2) : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  have ha : a = 1 := by
    rcases hz a with ha | ha
    · have he := hab ((fun _ => 1),0)
      simp only [ha, zero_smul, smul_zero] at he
      have hc := q.injective (he.trans q.map_zero.symm)
      have h := congrArg (fun v : Space n × Space n => v.1 ⟨0,by omega⟩) hc
      exact (one_ne_zero h).elim
    · exact ha
  have hb : b = 1 := by
    rcases hz b with hb | hb
    · have he := hab (0,(fun _ => 1))
      simp only [hb, zero_smul, smul_zero] at he
      have hc := q.injective (he.trans q.map_zero.symm)
      have h := congrArg (fun v : Space n × Space n => v.2 ⟨0,by omega⟩) hc
      exact (one_ne_zero h).elim
    · exact hb
  apply LinearEquiv.ext
  intro v
  have he := congrArg e (hab (e.symm v))
  simpa [q, ha, hb] using he
end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
