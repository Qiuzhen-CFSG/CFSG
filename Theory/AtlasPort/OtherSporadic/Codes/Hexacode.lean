/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Trio

/-!
The hexacode on six Kleinian coordinates, constructed by gluing the trio.
Explicit decoding proves injectivity and cardinality; isotropy and half dimension
then prove self-duality.

Source: `Atlas/Codes/Hexacode.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
abbrev HexIndex := Fin 3 × Fin 2
abbrev HexWord := HexIndex → K
abbrev HexParameters := (Fin 3 → Bit) × (Fin 2 → Bit) × Bit

def phi : L →ₗ[Bit] (Fin 2 → K) where
  toFun u := ![u, (0, u.2)]
  map_add' := by intros; ext i <;> fin_cases i <;> simp
  map_smul' := by intros; ext i <;> fin_cases i <;> simp

theorem phi_injective : Function.Injective phi := by
  intro u v h
  exact congrFun h 0

theorem phi_quadratic : ∀ u, wordQ qK (phi u) = qL u := by decide
theorem phi_polar : ∀ u v, wordPolar (phi u) (phi v) = polar u v := by decide

def phiWord : TrioWord →ₗ[Bit] HexWord where
  toFun w p := phi (w p.1) p.2
  map_add' := by intros; funext p; exact congrFun (phi.map_add _ _) p.2
  map_smul' := by intros; funext p; exact congrFun (phi.map_smul _ _) p.2

def pairParityEncoder : (Fin 2 → Bit) →ₗ[Bit] (Fin 3 → Bit) where
  toFun t := ![t 0 + t 1, t 0, t 1]
  map_add' := by intros; ext i; fin_cases i <;> simp; ring
  map_smul' := by intros; ext i; fin_cases i <;> simp [mul_add]

def equalPairs : (Fin 3 → Bit) →ₗ[Bit] HexWord where
  toFun r p := (r p.1, 0)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def eEncoder : (Fin 2 → Bit) →ₗ[Bit] HexWord := equalPairs.comp pairParityEncoder
@[simp] theorem eEncoder_apply (r : Fin 2 → Bit) (p : HexIndex) :
    eEncoder r p = (pairParityEncoder r p.1, 0) := rfl
def E0 : Submodule Bit HexWord := eEncoder.range

def tau : HexWord := fun p => ![![b, 0], ![b, 0], ![c, a]] p.1 p.2

def h0Encoder : ((Fin 3 → Bit) × (Fin 2 → Bit)) →ₗ[Bit] HexWord where
  toFun t := phiWord (trioEncoder t.1) + eEncoder t.2
  map_add' := by intros; simp; abel
  map_smul' := by intros; simp [smul_add]

def H0 : Submodule Bit HexWord := h0Encoder.range

def hexEncoder : HexParameters →ₗ[Bit] HexWord where
  toFun t := h0Encoder (t.1, t.2.1) + t.2.2 • tau
  map_add' := by intros; simp [h0Encoder, add_smul]; abel
  map_smul' := by intros; simp [h0Encoder, smul_add, mul_smul]

def hexacode : Submodule Bit HexWord := hexEncoder.range

/-- The displayed coordinate recovery, before any choice of a range inverse. -/
def hexDecoder (w : HexWord) : HexParameters :=
  (fun i => (w (i, 1)).2,
    ![(w (1, 1)).1, (w (2, 1)).1 + (w (0, 0)).2 + (w (0, 1)).2],
    (w (0, 0)).2 + (w (0, 1)).2)

theorem hex_decode_encode (t : HexParameters) : hexDecoder (hexEncoder t) = t := by
  rcases t with ⟨x, r, e⟩
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [hexDecoder, hexEncoder, h0Encoder, phiWord, phi,
      trioEncoder, eEncoder_apply, pairParityEncoder, tau, a, b, c]
  · apply Prod.ext
    · funext i
      fin_cases i <;> simp [hexDecoder, hexEncoder, h0Encoder, phiWord, phi,
        trioEncoder, eEncoder_apply, pairParityEncoder, tau, a, b, c]; ring_nf; simp
    · simp [hexDecoder, hexEncoder, h0Encoder, phiWord, phi,
        trioEncoder, eEncoder_apply, pairParityEncoder, tau, a, b, c]
      ring_nf
      simp

theorem hexEncoder_injective : Function.Injective hexEncoder :=
  Function.LeftInverse.injective hex_decode_encode

noncomputable def hexEquiv : HexParameters ≃ₗ[Bit] hexacode :=
  LinearEquiv.ofInjective hexEncoder hexEncoder_injective

theorem h0Encoder_injective : Function.Injective h0Encoder := by
  intro x y h
  have hh : hexEncoder (x.1, x.2, 0) = hexEncoder (y.1, y.2, 0) := by
    simpa [hexEncoder] using h
  have he := hexEncoder_injective hh
  exact Prod.ext (congrArg (fun t : HexParameters => t.1) he) (congrArg (fun t : HexParameters => t.2.1) he)

theorem eEncoder_injective : Function.Injective eEncoder := by
  intro x y h
  have hh : h0Encoder (0, x) = h0Encoder (0, y) := by simpa [h0Encoder] using h
  exact congrArg Prod.snd (h0Encoder_injective hh)

theorem E0_finrank : Module.finrank Bit E0 = 2 := by
  rw [E0, LinearMap.finrank_range_of_inj eEncoder_injective]
  simp

theorem H0_finrank : Module.finrank Bit H0 = 5 := by
  rw [H0, LinearMap.finrank_range_of_inj h0Encoder_injective]
  simp [Module.finrank_prod]

theorem hexacode_finrank : Module.finrank Bit hexacode = 6 := by
  rw [← hexEquiv.finrank_eq]
  simp [HexParameters, Module.finrank_prod]

theorem hexacode_card : Nat.card hexacode = 64 := by
  rw [← Nat.card_congr hexEquiv.toEquiv]
  norm_num [HexParameters, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

/-- Polynomial verification of evenness, uniformly in the six binary parameters. -/
theorem hexacode_isotropic (w : HexWord) (hw : w ∈ hexacode) : wordQ qK w = 0 := by
  obtain ⟨⟨x, r, e⟩, rfl⟩ := hw
  simp [wordQ, Fintype.sum_prod_type, Fin.sum_univ_succ, hexEncoder, h0Encoder,
    phiWord, phi, trioEncoder, eEncoder_apply, pairParityEncoder, tau, a, b, c, qK]
  ring_nf
  simp

theorem hexacode_selfDual : hexacode = dual hexacode := by
  apply selfDual_of_half_dimension wordPolar wordPolar_nondegenerate
  · intro w hw u hu
    have h := wordQ_polar qK qK_polar u w
    rw [hexacode_isotropic _ (hexacode.add_mem hu hw), hexacode_isotropic _ hu,
      hexacode_isotropic _ hw] at h
    simpa using h.symm
  · rw [hexacode_finrank]
    simp [HexIndex, Letter, Module.finrank_pi_fintype, Module.finrank_prod]

end Atlas.Codes
