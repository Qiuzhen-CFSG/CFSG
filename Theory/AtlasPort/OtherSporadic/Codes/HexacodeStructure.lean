/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Hexacode
public import Theory.AtlasPort.OtherSporadic.Codes.Weight

/-!
The two cosets and displayed basis of the constructed hexacode.
Coordinate recovery identifies the gluing spaces and separates the twisting coset;
the generators give evenness and the concrete basis.

Source: `Atlas/Codes/HexacodeStructure.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

theorem phiWord_injective : Function.Injective phiWord := by
  intro x y h
  funext i
  exact phi_injective (funext (fun j => congrFun h (i,j)))

theorem phiWord_quadratic (x : TrioWord) : wordQ qK (phiWord x) = wordQ qL x := by
  rw [wordQ, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => phi_quadratic (x i))

theorem phiWord_polar (x y : TrioWord) : wordPolar (phiWord x) (phiWord y) = wordPolar x y := by
  rw [wordPolar_apply, Fintype.sum_prod_type, wordPolar_apply]
  exact Finset.sum_congr rfl (fun i _ => phi_polar (x i) (y i))

theorem pairParityEncoder_range (r : Fin 3 → Bit) :
    (∃ t, pairParityEncoder t = r) ↔ ∑ i, r i = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp [pairParityEncoder, Fin.sum_univ_succ]
  · intro hr
    refine ⟨![r 1, r 2], ?_⟩
    funext i
    fin_cases i
    · change r 1 + r 2 = r 0
      have hh := congrArg (fun x : Bit => r 0 + x) hr
      simpa [Fin.sum_univ_succ, ← add_assoc] using hh
    · rfl
    · rfl

theorem E0_description (w : HexWord) :
    w ∈ E0 ↔ ∃ r : Fin 3 → Bit, (∑ i, r i = 0) ∧ equalPairs r = w := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨pairParityEncoder t, (pairParityEncoder_range _).mp ⟨t, rfl⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨t, rfl⟩ := (pairParityEncoder_range r).mpr hr
    exact ⟨t, rfl⟩

noncomputable def eEquiv : (Fin 2 → Bit) ≃ₗ[Bit] E0 :=
  LinearEquiv.ofInjective eEncoder eEncoder_injective
noncomputable def h0Equiv : ((Fin 3 → Bit) × (Fin 2 → Bit)) ≃ₗ[Bit] H0 :=
  LinearEquiv.ofInjective h0Encoder h0Encoder_injective
noncomputable def firstGluing : (trio × E0) ≃ₗ[Bit] H0 :=
  (trioEquiv.symm.prodCongr eEquiv.symm).trans h0Equiv
noncomputable def firstTwist : (trio × E0 × Bit) ≃ₗ[Bit] hexacode :=
  (trioEquiv.symm.prodCongr (eEquiv.symm.prodCongr (LinearEquiv.refl Bit Bit))).trans hexEquiv

theorem firstGluing_apply (x : trio) (e : E0) :
    (firstGluing (x, e) : HexWord) = phiWord x + e := by
  change phiWord (trioEncoder (trioEquiv.symm x)) + eEncoder (eEquiv.symm e) = _
  have hx := congrArg Subtype.val (trioEquiv.apply_symm_apply x)
  have he := congrArg Subtype.val (eEquiv.apply_symm_apply e)
  exact congrArg₂ (fun v w => phiWord v + w) hx he

theorem firstTwist_apply (x : trio) (e : E0) (ε : Bit) :
    (firstTwist (x, e, ε) : HexWord) = phiWord x + e + ε • tau := by
  change phiWord (trioEncoder (trioEquiv.symm x)) + eEncoder (eEquiv.symm e) + ε • tau = _
  have hx := congrArg Subtype.val (trioEquiv.apply_symm_apply x)
  have he := congrArg Subtype.val (eEquiv.apply_symm_apply e)
  change trioEncoder (trioEquiv.symm x) = x at hx
  change eEncoder (eEquiv.symm e) = e at he
  rw [hx, he]

theorem tau_not_mem_H0 : tau ∉ H0 := by
  rintro ⟨t, ht⟩
  have h : hexEncoder (t.1, t.2, 0) = hexEncoder (0, 0, 1) := by
    simpa [hexEncoder, h0Encoder] using ht
  have hh := congrArg (fun u : HexParameters => u.2.2) (hexEncoder_injective h)
  exact zero_ne_one hh

theorem hexacode_cosets (w : HexWord) :
    w ∈ hexacode ↔ w ∈ H0 ∨ ∃ v ∈ H0, w = v + tau := by
  constructor
  · rintro ⟨⟨x, r, ε⟩, rfl⟩
    rcases bit_cases ε with h | h
    · left; exact ⟨(x, r), by simp [hexEncoder, h]⟩
    · right; exact ⟨h0Encoder (x, r), ⟨(x, r), rfl⟩, by simp [hexEncoder, h]⟩
  · rintro (⟨⟨x, r⟩, rfl⟩ | ⟨_, ⟨⟨x, r⟩, rfl⟩, rfl⟩)
    · exact ⟨(x, r, 0), by simp [hexEncoder]⟩
    · exact ⟨(x, r, 1), by simp [hexEncoder]⟩

theorem hexacode_cosets_disjoint (w : HexWord) (hw : w ∈ H0) :
    ¬ ∃ v ∈ H0, w = v + tau := by
  rintro ⟨v, hv, h⟩
  apply tau_not_mem_H0
  have hh := H0.sub_mem hw hv
  rwa [h, add_sub_cancel_left] at hh

def hexFlatParameters : (Fin 6 → Bit) ≃ₗ[Bit] HexParameters where
  toFun t := (![t 0, t 1, t 2], ![t 3, t 4], t 5)
  invFun t := ![t.1 0, t.1 1, t.1 2, t.2.1 0, t.2.1 1, t.2.2]
  left_inv := by intro t; funext i; fin_cases i <;> rfl
  right_inv := by
    rintro ⟨x, r, ε⟩
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl
  map_add' := by intros; ext i <;> (try fin_cases i) <;> rfl
  map_smul' := by intros; ext i <;> (try fin_cases i) <;> rfl

noncomputable def hexBasis : Module.Basis (Fin 6) Bit hexacode :=
  (Pi.basisFun Bit (Fin 6)).map (hexFlatParameters.trans hexEquiv)

def hexGenerators : Fin 6 → HexWord := fun i p =>
  ![![![b,b], ![a,0], ![a,0]], ![![a,0], ![b,b], ![a,0]],
    ![![a,0], ![a,0], ![b,b]], ![![a,a], ![a,a], ![0,0]],
    ![![a,a], ![0,0], ![a,a]], ![![b,0], ![b,0], ![c,a]]] i p.1 p.2

theorem hexBasis_coe (i : Fin 6) : (hexBasis i : HexWord) = hexGenerators i := by
  change hexEncoder (hexFlatParameters ((Pi.basisFun Bit (Fin 6)) i)) = _
  rw [Pi.basisFun_apply]
  revert i
  decide

theorem hexGenerators_weight : ∀ i, hammingNorm (hexGenerators i) = 4 := by decide
theorem hexGenerators_orthogonal : ∀ i j, wordPolar (hexGenerators i) (hexGenerators j) = 0 := by decide
theorem hexGenerators_isotropic : ∀ i, wordQ qK (hexGenerators i) = 0 := by decide

theorem hexacode_even (w : HexWord) (hw : w ∈ hexacode) : Even (hammingNorm w) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [← wordQ_K_weight]
  exact hexacode_isotropic w hw

end Atlas.Codes
