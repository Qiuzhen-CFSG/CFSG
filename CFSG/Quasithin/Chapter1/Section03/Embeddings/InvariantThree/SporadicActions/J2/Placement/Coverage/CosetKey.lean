module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Coverage.Words
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# A coset invariant from two marked subsets of the J₂ permutation domain

The seven fixed generators preserve an eight-point set and a four-point set.
Taking the preimage of their setwise stabilizers proves that every element of
`Seed.s` preserves them. The binary codes of their images are consequently
constant on right multiplication by `Seed.s`. No global injectivity of this
invariant, subgroup normality, or Sylow assertion is required.

Source: the fixed ATLAS degree-100 words; Aschbacher–Smith, printed p.511,
and GLS3 Table 5.3g. The finite preservation checks use kernel reduction.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open Theory.GroupTheory

open scoped Pointwise

def markedOrbit : Fin 2 → Finset (Fin 100) :=
  ![{0, 20, 33, 51, 61, 71, 82, 83}, {4, 26, 63, 81}]

set_option maxRecDepth 100000 in
theorem seedMap_preserves : ∀ i j, (markedOrbit i).image (seedMap j) = markedOrbit i := by
  decide +kernel

theorem seed_preserves (i : Fin 2) {s : Carrier} (hs : s ∈ Seed.s) :
    (markedOrbit i).image (inclusion s) = markedOrbit i := by
  have hsub : Seed.s ≤
      (MulAction.stabilizer (Equiv.Perm (Fin 100)) (markedOrbit i)).comap inclusion := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨j, rfl⟩
    change (markedOrbit i).image (inclusion (Seed.sGenerator j)) = markedOrbit i
    have hmap : (inclusion (Seed.sGenerator j) : Fin 100 → Fin 100) = seedMap j :=
      funext (seedGenerator_apply j)
    rw [hmap]
    exact seedMap_preserves i j
  exact hsub hs

def orbitCode (i : Fin 2) (g : Fin 100 → Fin 100) : Nat :=
  ∑ x ∈ markedOrbit i, (1 <<< (g x).val)

def cosetKey (g : Carrier) : Nat :=
  orbitCode 0 (inclusion g) * (1 <<< 100) + orbitCode 1 (inclusion g)

theorem orbitCode_mul (i : Fin 2) (g s : Carrier) (hs : s ∈ Seed.s) :
    orbitCode i (inclusion (g * s)) = orbitCode i (inclusion g) := by
  unfold orbitCode
  simp only [map_mul, Equiv.Perm.mul_apply]
  have he := Finset.sum_image (s := markedOrbit i) (g := inclusion s)
    (f := fun x : Fin 100 => (1 : Nat) <<< ((inclusion g) x).val)
    (fun x _ y _ h => (inclusion s).injective h)
  rw [seed_preserves i hs] at he
  exact he.symm

theorem key_mul (g s : Carrier) (hs : s ∈ Seed.s) : cosetKey (g * s) = cosetKey g := by
  simp only [cosetKey, orbitCode_mul _ g s hs]

theorem key_eq_of_coset_eq {g h : Carrier}
    (he : (QuotientGroup.mk g : Carrier ⧸ Seed.s) = QuotientGroup.mk h) :
    cosetKey g = cosetKey h := by
  have hm : g⁻¹ * h ∈ Seed.s := QuotientGroup.eq.mp he
  simpa only [mul_inv_cancel_left] using (key_mul g (g⁻¹ * h) hm).symm

def explicitKey (g : Fin 100 → Fin 100) : Nat :=
  ((1 <<< (g 0).val) + (1 <<< (g 20).val) + (1 <<< (g 33).val) + (1 <<< (g 51).val) +
   (1 <<< (g 61).val) + (1 <<< (g 71).val) + (1 <<< (g 82).val) + (1 <<< (g 83).val)) * (1 <<< 100) +
  ((1 <<< (g 4).val) + (1 <<< (g 26).val) + (1 <<< (g 63).val) + (1 <<< (g 81).val))

theorem cosetKey_explicit (g : Carrier) : cosetKey g = explicitKey (inclusion g) := by
  simp [cosetKey, orbitCode, markedOrbit, explicitKey, Nat.add_assoc]


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
