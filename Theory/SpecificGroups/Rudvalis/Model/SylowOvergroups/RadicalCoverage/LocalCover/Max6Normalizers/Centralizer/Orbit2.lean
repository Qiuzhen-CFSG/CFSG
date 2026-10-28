module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Orbit1

/-!
# Max6 words covering the 2-th point orbit

The ATLAS inverse-action words and the certified Rudvalis orbital are unchanged.
These generated witnesses are untrusted until their Lean kernel checks pass.
Source: RuG1-max6W1 and degree-4060 permutations, attributed in
SylowOvergroups.Definitions and Model.PermutationData; GLS3 Table 5.3r,
and [Asc86b] as cited on quasithin printed p.511.
See Centralizer/source/Generate.py for witness generation.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
open Rudvalis.OuterNormalizer
open Rudvalis.OuterNormalizer.InvarianceCertificate
open Rudvalis.OuterNormalizer.RigidityCertificate

set_option maxRecDepth 30000
set_option Elab.async false

@[expose] public def gen2_0 : Model :=
  ([3, 5, 1, 0, 0].map letters1).prod

public theorem gen2_0_mem : gen2_0 ∈ max6 :=
  word_mem letters1 letters1_mem _

@[expose] public def letters2 : Fin 2 → Model :=
  ![gen2_0, gen2_0⁻¹]

public theorem letters2_mem (i : Fin 2) : letters2 i ∈ max6 := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact gen2_0_mem
  · exact max6.inv_mem gen2_0_mem

@[expose] public def words2 : Array (List (Fin 2)) := #[
[],
[0]]

@[expose] public def rep2 (i : Fin 2) : Model :=
  ((words2[i.val]!).map letters2).prod

public theorem rep2_mem (i : Fin 2) : rep2 i ∈ max6 :=
  word_mem letters2 letters2_mem _

@[expose] public def point2Data : Array Nat := #[
3395586]

@[expose] public def point2 (x : Fin 2) : Fin 4060 :=
  ⟨((point2Data[x.val / 64]! >>> (11 * (x.val % 64))) % 2048) % 4060, Nat.mod_lt _ (by decide)⟩

@[expose] public def pointInv2Data : Array Nat := #[
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
288230376151711744,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0]

@[expose] public def pointInv2 (x : Fin 4060) : Fin 2 :=
  ⟨((pointInv2Data[x.val / 64]! >>> (1 * (x.val % 64))) % 2) % 2, Nat.mod_lt _ (by decide)⟩

public theorem rep2_point : ∀ i : Fin 2, (rep2 i).val 2 = point2 i := by
  decide +kernel

public theorem rep2_fix : ∀ i : Fin 2, ∀ x : Fin 4060, x.val < 2 → (rep2 i).val x = x := by
  have h0 : ∀ i : Fin 2, (rep2 i).val 0 = 0 := by decide +kernel
  have h1 : ∀ i : Fin 2, (rep2 i).val 1 = 1 := by decide +kernel
  intro i x hx
  have h : x.val = 0 ∨ x.val = 1 := by omega
  rcases h with h | h
  · have he : x = 0 := Fin.ext h
    subst x
    exact h0 i
  · have he : x = 1 := Fin.ext h
    subst x
    exact h1 i


end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
