module

public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.ZMod.Basic

/-!
# An elementary nine in characteristic-two G₂

The long-root element `E(1) r` and the orthogonal short-root element
`C(1) (rs)³ r` commute and have cube one. Their explicit actions on the
split octonions distinguish the nine products, embedding C₃ × C₃ over every
characteristic-two field. In the binary model their images under the hexagon
sign character are trivial: they have exponent three, while the sign group
has exponent two. The sign kernel is the actual commutator subgroup.

This gives three-rank at least two without using group orders, simplicity,
or an exceptional isomorphism. The root elements and Weyl conventions are
from Gerald Höhn and the ATLAS contributors' licensed port, specifically
`Atlas/LinearGroups/G2/WeylMaps.lean` and `RootGroups.lean`, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. See LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. The commuting cubic construction and rank
arguments here are additions to that port.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, A.2.3–4, printed p.33, and the
rank-one component inspection in the proof of 15.3.38, printed p.1137.
-/

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open scoped CharTwo
namespace Atlas.G2.EvenThreeRank
variable {K : Type*} [Field K] [CharP K 2]
def long : Model K := rootE 1 * weylR
def short : Model K := rootC 1 * ((weylR * weylS)^3 * weylR)

theorem long_apply (v : Carrier K) :
    (long : Model K).val v = ![v 0, v 1 + v 2, v 1, v 3, v 4, v 5 + v 6, v 5, v 7] := by
  funext i
  fin_cases i <;> simp [long, rootE, rootEEquiv, rootELinear, rootEApply,
    weylR, weylREquiv, weylRLinear, weylRApply, CharTwo.neg_eq, CharTwo.sub_eq_add, add_comm]

theorem short_apply (v : Carrier K) :
    (short : Model K).val v =
      ![v 0 + v 3 + v 4 + v 7, v 1 + v 5, v 2 + v 6, v 0 + v 4,
        v 0 + v 3, v 1, v 2, v 0] := by
  funext i
  fin_cases i <;> simp [short, rootC, rootCEquiv, rootCLinear, rootCApply,
    weylR, weylREquiv, weylRLinear, weylRApply,
    weylS, weylSEquiv, weylSLinear, weylSApply, pow_succ, CharTwo.neg_eq, CharTwo.sub_eq_add, add_comm, add_assoc]


theorem long_cube : (long : Model K)^3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (long : Model K).val ((long : Model K).val ((long : Model K).val v)) = v
  rw [long_apply, long_apply, long_apply]
  funext i
  fin_cases i <;> simp [CharTwo.add_self_eq_zero, CharTwo.add_cancel_left, add_left_comm, add_comm]

private theorem short_cube_of_apply (g : Model K)
    (hg : ∀ v : Carrier K, g.val v =
      ![v 0 + v 3 + v 4 + v 7, v 1 + v 5, v 2 + v 6, v 0 + v 4,
        v 0 + v 3, v 1, v 2, v 0]) : g^3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.val (g.val (g.val v)) = v
  rw [hg, hg, hg]
  funext i
  fin_cases i <;> simp <;> abel_nf <;> simp

theorem short_cube : (short : Model K)^3 = 1 :=
  short_cube_of_apply short short_apply

theorem long_short : Commute (long : Model K) short := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (long : Model K).val ((short : Model K).val v) =
    (short : Model K).val ((long : Model K).val v)
  rw [long_apply, short_apply, long_apply, short_apply]
  funext i
  fin_cases i <;> simp [add_assoc, add_left_comm]

private def cubicHom (g : Model K) (hg : g^3=1) : Multiplicative (ZMod 3) →* Model K where
  toFun a := g ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    change g ^ (a.toAdd + b.toAdd).val = g ^ a.toAdd.val * g ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg).symm

private abbrev E := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
def embedding : E →* Model K :=
  (cubicHom long long_cube).noncommCoprod (cubicHom short short_cube)
    (fun a b => long_short.pow_pow a.toAdd.val b.toAdd.val)


theorem embedding_injective : Function.Injective (embedding (K := K)) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨a,b⟩ hab
  have h0 := congrArg (fun g : Model K => g.val (basisVector 0) 7) hab
  have h1 := congrArg (fun g : Model K => g.val (basisVector 1) 2) hab
  change (long ^ a.toAdd.val * short ^ b.toAdd.val).val (basisVector 0) 7 = (0 : K) at h0
  change (long ^ a.toAdd.val * short ^ b.toAdd.val).val (basisVector 1) 2 = (0 : K) at h1
  have ha : a.toAdd.val < 3 := ZMod.val_lt a.toAdd
  have hb : b.toAdd.val < 3 := ZMod.val_lt b.toAdd
  interval_cases hai : a.toAdd.val <;> interval_cases hbi : b.toAdd.val <;>
    simp [pow_succ, long_apply, short_apply, basisVector] at h0 h1
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    exact hai
  · apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    exact hbi

private theorem cube (a : E) : a ^ 3 = 1 := by
  apply Prod.ext <;>
    apply Multiplicative.toAdd.injective <;>
    change 3 • _ = (0 : ZMod 3) <;>
    simp only [nsmul_eq_mul]
  all_goals exact zero_mul _

private theorem card : Nat.card E = 3^2 := by
  simp [E, Nat.card_eq_fintype_card]

/-- Every finite characteristic-two octonion automorphism group contains an elementary nine. -/
public theorem two_le_primeRank [Finite K] : 2 ≤ primeRank 3 (Model K) :=
  primeRank_ge_of_elementary_embedding cube card embedding embedding_injective


private def derivedEmbedding : E →* commutator (Model (ZMod 2)) :=
  (embedding (K := ZMod 2)).codRestrict _ (by
    intro a
    rw [BinaryParabolicPair.commutator_eq_longRootClosure,
      ← BinaryException.lineSign_kernel]
    change Binary.lineSign (embedding a) = 1
    have h3 : Binary.lineSign (embedding a) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, cube, map_one, map_one]
    have h2 := Int.units_sq (Binary.lineSign (embedding a))
    simpa [pow_succ, h2] using h3)

private theorem derivedEmbedding_injective : Function.Injective derivedEmbedding := by
  intro a b h
  exact embedding_injective (congrArg Subtype.val h)

/-- The same elementary nine lies in the actual binary derived subgroup. -/
public theorem two_le_primeRank_derived : 2 ≤ primeRank 3 (commutator (Model (ZMod 2))) :=
  primeRank_ge_of_elementary_embedding cube card derivedEmbedding derivedEmbedding_injective

end Atlas.G2.EvenThreeRank
