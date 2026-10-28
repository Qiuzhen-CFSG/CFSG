module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.Tactic.NormNum

/-!
# Quotient and annihilator orbits of binary-plane stabilizers in SL₂(4)

For every binary plane W in the actual natural module F₄², its stabilizer
is transitive both on the nonzero vectors of V/W and on the nonzero binary
functionals vanishing on W. The latter action uses composition with the
inverse of the natural action.

Choose distinct nonzero u, v in W and move u to the first coordinate vector.
An explicit determinant-one matrix cycles u, v, u+v and satisfies T² = T+1
on all of V. The only finite certificate checks this matrix identity for
the sixteen possible normalized second vectors. Conjugation returns the
matrix to the original coordinates. The identity descends to V/W and to
its dual annihilator; on each four-element space it forces a single orbit
on the three nonzero elements.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), J.2.2–3 and J.2.8, printed
pp.432–434,437–438. These are the model calculations used by the literal
transport adapters in ChapterJ/Section01To02/Fusion/CoreOrbit/Transport;
the ambient-group hypotheses and final source assembly belong there.
-/

public section
namespace Representation.SL2FourNatural

private theorem four_span {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (hc : Nat.card M = 4) (u v : M) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) (w : M) : w = 0 ∨ w = u ∨ w = v ∨ w = u + v := by
  classical
  let := Fintype.ofFinite M
  have huv0 : u + v ≠ 0 := by
    intro h
    have he := congrArg (u + ·) h
    rw [← add_assoc, ZModModule.add_self, zero_add, add_zero] at he
    exact huv he.symm
  have hs : ({0, u, v, u + v} : Finset M).card = 4 := by
    simp [hu, hv, huv, Ne.symm hu, Ne.symm hv,
      Ne.symm huv0]
  have he := Finset.eq_univ_of_card ({0, u, v, u + v} : Finset M)
    (by simpa only [← Nat.card_eq_fintype_card, hc] using hs)
  have hw := Finset.mem_univ w
  rw [← he] at hw
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hw

private theorem exists_pair {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (hc : Nat.card M = 4) : ∃ u v : M, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  classical
  let := Fintype.ofFinite M
  have hc' : (Finset.univ : Finset M).card = 4 := by
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hc
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_ne (by omega : 1 < (Finset.univ : Finset M).card) (0 : M)
  have hex : ∃ v : M, v ≠ 0 ∧ v ≠ u := by
    by_contra! h
    have hs : (Finset.univ : Finset M) ⊆ {0, u} := by
      intro v _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hv : v = 0
      · exact Or.inl hv
      · exact Or.inr (h v hv)
    have hb := Finset.card_le_card hs
    simp only [hc', Finset.card_pair hu.symm] at hb
    omega
  obtain ⟨v, hv, hvu⟩ := hex
  exact ⟨u, v, hu, hv, hvu.symm⟩

private theorem cyclic_four {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (hc : Nat.card M = 4) (T : M →ₗ[ZMod 2] M)
    (hp : ∀ x, T (T x) = T x + x) (a b : M) (ha : a ≠ 0) (hb : b ≠ 0) :
    b = a ∨ b = T a ∨ b = T (T a) := by
  have hTa : T a ≠ 0 := by
    intro h
    have h' := hp a
    rw [h, map_zero, zero_add] at h'
    exact ha h'.symm
  have hne : a ≠ T a := by
    intro h
    have h' := hp a
    rw [← h] at h'
    rw [← h, ZModModule.add_self] at h'
    exact ha h'
  rcases four_span hc a (T a) ha hTa hne b with h | h | h | h
  · exact (hb h).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.trans ((add_comm _ _).trans (hp a).symm)))
/-- A trace-one matrix sending the first coordinate vector to v. The zero
second-coordinate case is precisely the F₄-line case. -/
private def cycleMatrix (v : V) : Matrix (Fin 2) (Fin 2) F :=
  !![v 0, if v 1 = 0 then 0 else (v 0 ^ 2 + v 0 + 1) / v 1;
     v 1, v 0 + 1]

private theorem cycleMatrix_spec : ∀ v : V, v ≠ 0 → v ≠ ![1, 0] →
    (cycleMatrix v).det = 1 ∧
    (cycleMatrix v).mulVec ![1, 0] = v ∧
    (cycleMatrix v) * (cycleMatrix v) = cycleMatrix v + 1 := by
  decide +kernel

private theorem cycle_on_pair (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∃ g : SL, action g u = v ∧ action g v = u + v ∧
      ∀ x, action g (action g x) = action g x + x := by
  obtain ⟨A, hA⟩ := exists_first_column u hu
  let v' := action A⁻¹ v
  have hv' : v' ≠ 0 := by
    intro h
    apply hv
    exact (action A⁻¹).injective (h.trans (map_zero _).symm)
  have hv'e : v' ≠ ![1, 0] := by
    intro h
    have he : v = u := by simpa [v', hA] using congrArg (action A) h
    exact huv he.symm
  obtain ⟨hd, he, hp⟩ := cycleMatrix_spec v' hv' hv'e
  let c : SL := ⟨cycleMatrix v', hd⟩
  have hc (x : V) : action c (action c x) = action c x + x := by
    change (cycleMatrix v').mulVec ((cycleMatrix v').mulVec x) =
      (cycleMatrix v').mulVec x + x
    rw [Matrix.mulVec_mulVec, hp, Matrix.add_mulVec, Matrix.one_mulVec]
  have hce : action c ![1, 0] = v' := he
  have hcv : action c v' = ![1, 0] + v' := by
    rw [← hce, hc, add_comm]
  refine ⟨A * c * A⁻¹, ?_, ?_, ?_⟩
  · simp only [map_mul, LinearEquiv.mul_apply]
    rw [← hA]
    rw [show action A⁻¹ (action A ![1, 0]) = ![1, 0] by simp, hce]
    dsimp [v']
    simp
  · simp only [map_mul, LinearEquiv.mul_apply]
    change action A (action c v') = u + v
    rw [hcv, map_add, hA]
    dsimp [v']
    simp
  · intro x
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [show action A⁻¹ (action A (action c (action A⁻¹ x))) =
      action c (action A⁻¹ x) by simp]
    rw [hc, map_add]
    simp

/-- A cubic in the actual plane stabilizer, with its polynomial identity
on the entire natural module. -/
private theorem plane_cycle (W : Submodule (ZMod 2) V) (hW : Nat.card W = 4) :
    ∃ g : SL, (∀ w ∈ W, action g w ∈ W) ∧
      ∀ x, action g (action g x) = action g x + x := by
  obtain ⟨u, v, hu, hv, huv⟩ := exists_pair hW
  obtain ⟨g, hgu, hgv, hp⟩ := cycle_on_pair (u : V) (v : V)
    (fun h => hu (Subtype.ext h)) (fun h => hv (Subtype.ext h))
    (fun h => huv (Subtype.ext h))
  refine ⟨g, ?_, hp⟩
  intro w hw
  rcases four_span hW u v hu hv huv ⟨w, hw⟩ with h | h | h | h
  · have he : w = 0 := congrArg Subtype.val h
    rw [he, map_zero]
    exact W.zero_mem
  · have he : w = u := congrArg Subtype.val h
    rw [he, hgu]
    exact v.property
  · have he : w = v := congrArg Subtype.val h
    rw [he, hgv]
    exact W.add_mem u.property v.property
  · have he : w = (u : V) + v := congrArg Subtype.val h
    rw [he, map_add, hgu, hgv]
    exact W.add_mem v.property (W.add_mem u.property v.property)

/-- The stabilizer of a binary plane is transitive on the three nonzero
cosets in the actual natural-module quotient. -/
theorem plane_quotient_transitive (W : Submodule (ZMod 2) V) (hW : Nat.card W = 4)
    (a b : V) (ha : a ∉ W) (hb : b ∉ W) :
    ∃ g : SL, (∀ w ∈ W, action g w ∈ W) ∧ b - action g a ∈ W := by
  classical
  obtain ⟨g, hg, hp⟩ := plane_cycle W hW
  let T := W.mapQ W (action g).toLinearMap hg
  have hT (x : V) : T (W.mkQ x) = W.mkQ (action g x) := rfl
  have hpoly : ∀ x, T (T x) = T x + x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change W.mkQ (action g (action g x)) = W.mkQ (action g x) + W.mkQ x
      rw [hp, map_add]
  have hq : Nat.card (V ⧸ W) = 4 := by
    have hc := W.card_eq_card_quotient_mul_card
    rw [show Nat.card V = 16 by rw [Nat.card_eq_fintype_card, card_vector], hW] at hc
    omega
  have ha' : W.mkQ a ≠ 0 := fun he => ha ((Submodule.Quotient.mk_eq_zero W).mp he)
  have hb' : W.mkQ b ≠ 0 := fun he => hb ((Submodule.Quotient.mk_eq_zero W).mp he)
  rcases cyclic_four hq T hpoly (W.mkQ a) (W.mkQ b) ha' hb' with h | h | h
  · refine ⟨1, ?_, ?_⟩
    · intro w hw
      simpa using hw
    · simpa using (Submodule.Quotient.eq W).mp h
  · refine ⟨g, hg, ?_⟩
    exact (Submodule.Quotient.eq W).mp h
  · refine ⟨g * g, ?_, ?_⟩
    · intro w hw
      simpa only [map_mul, LinearEquiv.mul_apply] using hg _ (hg w hw)
    · rw [hT, hT] at h
      rw [map_mul, LinearEquiv.mul_apply]
      exact (Submodule.Quotient.eq W).mp h

private theorem plane_annihilator_card (W : Submodule (ZMod 2) V) (hW : Nat.card W = 4) :
    Nat.card W.dualAnnihilator = 4 := by
  have hd : Module.finrank (ZMod 2) W = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hW, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      (show (2 : ℕ) ^ 2 = 2 ^ Module.finrank (ZMod 2) W from hc)).symm
  have hd' : Module.finrank (ZMod 2) W.dualAnnihilator = 2 := by
    have hs := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    rw [hd, finrank_vector] at hs
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd',
    Nat.card_eq_fintype_card, ZMod.card]
  norm_num

/-- The same plane stabilizer is transitive on nonzero functionals vanishing
on the plane, with the literal contragredient convention. -/
theorem plane_annihilator_transitive (W : Submodule (ZMod 2) V) (hW : Nat.card W = 4)
    (f k : Module.Dual (ZMod 2) V) (hf : f ≠ 0) (hk : k ≠ 0)
    (hfW : ∀ w ∈ W, f w = 0) (hkW : ∀ w ∈ W, k w = 0) :
    ∃ g : SL, (∀ w ∈ W, action g w ∈ W) ∧
      f.comp (action g⁻¹).toLinearMap = k := by
  classical
  obtain ⟨g, hg, hp⟩ := plane_cycle W hW
  have hcube (x : V) : action g (action g (action g x)) = x := by
    rw [hp, hp, add_right_comm, ZModModule.add_self, zero_add]
  have hinv (x : V) : action g⁻¹ x = action g (action g x) := by
    apply (action g).injective
    rw [hcube]
    simp
  let T : W.dualAnnihilator →ₗ[ZMod 2] W.dualAnnihilator := {
    toFun φ := ⟨φ.val.comp (action g).toLinearMap, by
      apply (W.mem_dualAnnihilator _).mpr
      intro w hw
      exact (W.mem_dualAnnihilator _).mp φ.property _ (hg w hw)⟩
    map_add' φ ψ := by apply Subtype.ext; rfl
    map_smul' c φ := by apply Subtype.ext; rfl }
  have hpoly (φ : W.dualAnnihilator) : T (T φ) = T φ + φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change φ.val (action g (action g x)) = φ.val (action g x) + φ.val x
    rw [hp, map_add]
  let f' : W.dualAnnihilator := ⟨f, (W.mem_dualAnnihilator f).mpr hfW⟩
  let k' : W.dualAnnihilator := ⟨k, (W.mem_dualAnnihilator k).mpr hkW⟩
  have hf' : f' ≠ 0 := fun h => hf (congrArg Subtype.val h)
  have hk' : k' ≠ 0 := fun h => hk (congrArg Subtype.val h)
  have : Finite W.dualAnnihilator := Nat.finite_of_card_ne_zero (by
    rw [plane_annihilator_card W hW]
    decide)
  rcases cyclic_four (plane_annihilator_card W hW) T hpoly f' k' hf' hk' with h | h | h
  · refine ⟨1, ?_, ?_⟩
    · intro w hw
      simpa using hw
    · have he : k = f := congrArg Subtype.val h
      simpa using he.symm
  · refine ⟨g⁻¹, ?_, ?_⟩
    · intro w hw
      rw [hinv]
      exact hg _ (hg w hw)
    · have he : k = f.comp (action g).toLinearMap := congrArg Subtype.val h
      simpa using he.symm
  · refine ⟨g, hg, ?_⟩
    have he : k = (f.comp (action g).toLinearMap).comp (action g).toLinearMap :=
      congrArg Subtype.val h
    apply LinearMap.ext
    intro x
    rw [he]
    change f (action g⁻¹ x) = f (action g (action g x))
    rw [hinv]

end Representation.SL2FourNatural
