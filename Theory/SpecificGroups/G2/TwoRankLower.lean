module

public import Theory.AtlasPort.LinearGroups.G2.Torus
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.SpecificGroups.G2Even.TwoRank.Elementary
public import Mathlib.FieldTheory.Finite.Basic

/-!
# An elementary eight in the split-octonion G₂ model

In odd characteristic, the binary split torus commutes with the longest Weyl
element. The coordinate reversal of that Weyl element detects its parameter,
and two remaining octonion coordinates detect the torus parameters. Thus
these actual automorphisms embed an elementary eight. In characteristic two,
the existing three-root subgroup supplies the same lower bound.

This excludes the full G₂ family in the rank-two known-simple sieve of
Aschbacher–Smith A.2.12, printed p.36. The coordinate maps use the licensed
ATLAS octonion construction; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

namespace Atlas.G2.OddTwoRank
open Atlas.SplitOctonion
variable {F : Type*} [Field F]

private def binaryHom {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) :
    Multiplicative (ZMod 2) →* G where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : Multiplicative (ZMod 2),
        x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]

private def longest : Model F := (weylR * weylS) ^ 3
private theorem longest_apply (x : Carrier F) :
    (longest : Model F).val x = ![x 7,x 6,x 5,x 4,x 3,x 2,x 1,x 0] := by
  ext i
  fin_cases i <;>
    simp [longest, pow_succ, weylR, weylS, weylREquiv, weylSEquiv,
      weylRLinear, weylSLinear, weylRApply, weylSApply]

private theorem longest_sq : (longest : Model F) ^ 2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (longest : Model F).val ((longest : Model F).val x) = x
  simp only [longest_apply]
  ext i
  fin_cases i <;> rfl

private def signHom : Multiplicative (ZMod 2) →* Fˣ :=
  binaryHom (-1) (by simp)
private def torusBinary :
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* Model F :=
  torusHom.comp ((signHom (F := F)).prodMap signHom)
private def weylBinary : Multiplicative (ZMod 2) →* Model F :=
  binaryHom longest longest_sq

private theorem binary_commute (a : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (b : Multiplicative (ZMod 2)) : Commute (torusBinary (F := F) a) (weylBinary b) := by
  change Commute (torus (signHom a.1) (signHom a.2))
    (if b.toAdd = 0 then 1 else longest)
  split_ifs
  · exact Commute.one_right _
  change torus (signHom a.1) (signHom a.2) * longest =
    longest * torus (signHom a.1) (signHom a.2)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (torus (signHom a.1) (signHom a.2)).val ((longest : Model F).val x) =
    (longest : Model F).val ((torus (signHom a.1) (signHom a.2)).val x)
  simp only [longest_apply]
  ext i
  by_cases ha : a.1 = 1 <;> by_cases hb : a.2 = 1 <;>
    fin_cases i <;> simp [torus, torusEquiv, torusLinear, torusWeights, signHom, binaryHom, ha, hb]

private abbrev E :=
  (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)

public def embedding :
    ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) →* Model F :=
  torusBinary.noncommCoprod weylBinary binary_commute

public theorem embedding_injective (hF : (2 : F) ≠ 0) :
    Function.Injective (embedding (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  rintro ⟨⟨a,b⟩,c⟩ hx
  have h := hx
  change embedding ((a,b),c) = 1 at h
  have h3 := congrArg (fun g : Model F => g.val (basisVector 3) 3) h
  have h0 := congrArg (fun g : Model F => g.val (basisVector 0) 0) h
  have h1 := congrArg (fun g : Model F => g.val (basisVector 1) 1) h
  change (torus (signHom a) (signHom b)).val ((weylBinary c).val (basisVector 3)) 3 = 1 at h3
  change (torus (signHom a) (signHom b)).val ((weylBinary c).val (basisVector 0)) 0 = 1 at h0
  change (torus (signHom a) (signHom b)).val ((weylBinary c).val (basisVector 1)) 1 = 1 at h1
  have hc : c = 1 := by
    by_contra hc
    simp [weylBinary, binaryHom,
      hc, longest_apply, torus, torusEquiv, torusLinear, torusWeights,
      basisVector] at h3
  have hneg : (-1 : F) ≠ 1 := by
    intro hneg
    apply hF
    simpa only [neg_add_cancel, one_add_one_eq_two] using congrArg (fun x : F => x + 1) hneg.symm
  have ha : a = 1 := by
    by_contra ha
    simp [weylBinary, binaryHom,
      hc, signHom, ha, torus, torusEquiv, torusLinear, torusWeights,
      basisVector, hneg] at h0
  have hb : b = 1 := by
    by_contra hb
    simp [weylBinary, binaryHom,
      hc, signHom, hb, torus, torusEquiv, torusLinear, torusWeights,
      basisVector, hneg] at h1
  change ((a,b),c) = 1
  exact Prod.ext (Prod.ext ha hb) hc

end Atlas.G2.OddTwoRank

namespace Atlas.G2.OddTwoRank
variable {F : Type*} [Field F] [Finite F]

public theorem three_le_primeRank (hF : (2 : F) ≠ 0) : 3 ≤ primeRank 2 (Model F) := by
  apply primeRank_ge_of_elementary_embedding (f := embedding (F := F))
    (hf := embedding_injective hF)
  · rintro ⟨⟨a,b⟩,c⟩
    have hs : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide +kernel
    exact Prod.ext (Prod.ext (hs a) (hs b)) (hs c)
  · simp
end Atlas.G2.OddTwoRank

namespace Atlas.G2
/-- Every finite-field split G₂ carrier has an elementary eight. -/
public theorem three_le_primeRank_two (F : Type*) [Field F] [Finite F] :
    3 ≤ primeRank 2 (Model F) := by
  by_cases hF : (2 : F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr hF
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨n, _, hn⟩ := FiniteField.card F 2
    have hr := EvenTwoRank.rank_ge F (by simpa only [Nat.card_eq_fintype_card] using hn)
    have hn0 := n.pos
    omega
  · exact OddTwoRank.three_le_primeRank hF
end Atlas.G2
