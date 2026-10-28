module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Coordinates
-- Internal extension of the positive-duality construction: positivity of the flipped base.
import all Theory.AlgebraicGroup.RootSystems.ExceptionalDuality

/-!
# Weyl equivariance of the exceptional F4 duality

Diagram reversal identifies the F4 Cartan matrix with its transpose. The resulting
isomorphism to the dual root pairing has the specification of the unique positive
exceptional duality. Its linear root map therefore proves equivariance under
reflections, without any assumption on Chevalley matrices.

This extends the construction in `ExceptionalDuality` and the convention in
`ReeF4.ExceptionalEndomorphism.RootDuality` (Aschbacher–Smith, Remark A.2.4).
-/

namespace ReeF4.WordRelations

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

private noncomputable def reversedBaseEquiv : typeF4RootPairing_base.support ≃
    typeF4RootPairing_base.flip.support :=
  simplePermutation.trans (Equiv.setCongr (congrArg
    (fun s : Finset typeF4Roots => (s : Set typeF4Roots))
    typeF4RootPairing_base.flip_support.symm))

private theorem reversedBaseEquiv_val (i : typeF4RootPairing_base.support) :
    (reversedBaseEquiv i).val = (simplePermutation i).val := rfl

private theorem reversedBaseEquiv_cartan (i j : typeF4RootPairing_base.support) :
    typeF4RootPairing_base.flip.cartanMatrix (reversedBaseEquiv i) (reversedBaseEquiv j) =
      typeF4RootPairing_base.cartanMatrix i j := by
  change typeF4RootPairing_base.cartanMatrix (simplePermutation j) (simplePermutation i) = _
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
  simp only [simplePermutation_numbered, typeF4RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases j <;> norm_num [typeF4CartanMatrix, Fin.revPerm, Fin.rev, Fin.last]

private noncomputable def dualEquiv : typeF4RootPairing.Equiv typeF4RootPairing.flip :=
  typeF4RootPairing_base.equivOfCartanMatrixEq typeF4RootPairing_base.flip
    reversedBaseEquiv reversedBaseEquiv_cartan

private theorem dualEquiv_simple (i : typeF4RootPairing_base.support) :
    dualEquiv.toHom.indexEquiv i = (simplePermutation i).val := by
  apply typeF4RootPairing.flip.root.injective
  rw [← RootPairing.Hom.root_weightMap_apply typeF4RootPairing typeF4RootPairing.flip i]
  change (typeF4RootPairing_base.toWeightBasis.equiv
    typeF4RootPairing_base.flip.toWeightBasis reversedBaseEquiv)
      (typeF4RootPairing.root i) = typeF4RootPairing.flip.root (reversedBaseEquiv i)
  rw [← typeF4RootPairing_base.toWeightBasis_apply i, Module.Basis.equiv_apply,
    typeF4RootPairing_base.flip.toWeightBasis_apply]

private theorem dualEquiv_reflection (r s : typeF4Roots) :
    dualEquiv.toHom.indexEquiv (typeF4RootPairing.reflectionPerm r s) =
      typeF4RootPairing.reflectionPerm (dualEquiv.toHom.indexEquiv r)
        (dualEquiv.toHom.indexEquiv s) := by
  apply typeF4RootPairing.flip.root.injective
  rw [← RootPairing.Hom.root_weightMap_apply,
    typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root,
    map_sub, map_smul, RootPairing.Hom.root_weightMap_apply,
    RootPairing.Hom.root_weightMap_apply,
    ← typeF4RootPairing.flip_reflectionPerm,
    typeF4RootPairing.flip.root_reflectionPerm,
    typeF4RootPairing.flip.reflection_apply_root,
    RootPairing.Equiv.pairing_eq]

private theorem dualEquiv_pos (r : typeF4Roots)
    (hr : typeF4RootPairing_base.IsPos r) :
    typeF4RootPairing_base.IsPos (dualEquiv.toHom.indexEquiv r) := by
  apply (flip_isPos_iff typeF4RootPairing_base _).mp
  apply hr.induction_on_add
  · intro i hi
    rw [dualEquiv_simple ⟨i, hi⟩]
    exact typeF4RootPairing_base.flip.isPos_of_mem_support (simplePermutation ⟨i, hi⟩).property
  · intro i j k h hi hj
    apply hi.add (typeF4RootPairing_base.flip.isPos_of_mem_support
      (show dualEquiv.toHom.indexEquiv j ∈ typeF4RootPairing_base.flip.support by
        rw [dualEquiv_simple ⟨j, hj⟩]
        exact (simplePermutation ⟨j, hj⟩).property))
    rw [← RootPairing.Hom.root_weightMap_apply,
      ← RootPairing.Hom.root_weightMap_apply,
      ← RootPairing.Hom.root_weightMap_apply, h, map_add]

private theorem dualEquiv_pairingIn (r s : typeF4Roots) :
    typeF4RootPairing.pairingIn ℤ (dualEquiv.toHom.indexEquiv r)
      (dualEquiv.toHom.indexEquiv s) = typeF4RootPairing.pairingIn ℤ s r := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
  change algebraMap ℤ ℝ _ = algebraMap ℤ ℝ _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing.algebraMap_pairingIn]
  exact RootPairing.Equiv.pairing_eq dualEquiv s r

private theorem dualEquiv_spec :
    typeF4RootPairing.IsPositiveRootDuality typeF4RootPairing_base
      dualEquiv.toHom.indexEquiv := by
  let ρ := dualEquiv.toHom.indexEquiv
  have hswap (r s : typeF4Roots) :
      typeF4RootPairing.pairingIn ℤ (ρ r) (ρ s) =
        typeF4RootPairing.pairingIn ℤ s r := dualEquiv_pairingIn r s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    constructor
    · intro hr
      rw [dualEquiv_simple ⟨r, hr⟩]
      exact (simplePermutation ⟨r, hr⟩).property
    · intro hr
      obtain ⟨i, hi⟩ := simplePermutation.surjective ⟨ρ r, hr⟩
      have he : ρ i = ρ r := (dualEquiv_simple i).trans (congrArg Subtype.val hi)
      exact ρ.injective he ▸ i.property
  · intro r
    constructor
    · exact dualEquiv_pos r
    · intro hr
      by_contra hn
      let _ := typeF4RootPairing.indexNeg
      have hp := dualEquiv_pos (-r)
        ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hn)
      have he : ρ (-r) = -ρ r := dualEquiv_reflection r r
      rw [he] at hp
      exact ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base (ρ r)).mp hp) hr
  · intro r
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨ρ s, by rw [hswap, hswap]; exact hs⟩
    · rintro ⟨s, hs⟩
      obtain ⟨s, rfl⟩ := ρ.surjective s
      refine ⟨s, ?_⟩
      change |typeF4RootPairing.pairingIn ℤ (ρ s) (ρ r)| <
        |typeF4RootPairing.pairingIn ℤ (ρ r) (ρ s)| at hs
      simpa only [hswap] using hs
  · intro r
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨ρ s, by rw [hswap, hswap]; exact hs⟩
    · rintro ⟨s, hs⟩
      obtain ⟨s, rfl⟩ := ρ.surjective s
      refine ⟨s, ?_⟩
      change |typeF4RootPairing.pairingIn ℤ (ρ r) (ρ s)| <
        |typeF4RootPairing.pairingIn ℤ (ρ s) (ρ r)| at hs
      simpa only [hswap] using hs
  · intro r s
    rw [hswap, hswap, mul_comm]

/-- Exceptional duality transposes the integer root-coroot pairing. This is
the coefficient identity used by the long and short simple-root comparisons. -/
public theorem exceptionalRootPermutation_pairingIn (r s : typeF4Roots) :
    typeF4RootPairing.pairingIn ℤ (exceptionalRootPermutation r)
      (exceptionalRootPermutation s) = typeF4RootPairing.pairingIn ℤ s r := by
  rw [← exceptionalRootPermutation_unique dualEquiv_spec]
  exact dualEquiv_pairingIn r s

/-- The exceptional duality intertwines reflection in any root with reflection
in its dual root. -/
public theorem exceptionalRootPermutation_reflection (r s : typeF4Roots) :
    exceptionalRootPermutation (typeF4RootPairing.reflectionPerm r s) =
      typeF4RootPairing.reflectionPerm (exceptionalRootPermutation r)
        (exceptionalRootPermutation s) := by
  rw [← exceptionalRootPermutation_unique dualEquiv_spec]
  exact dualEquiv_reflection r s

/-- In numbered simple roots, the reflecting generator is reversed. -/
public theorem exceptionalRootPermutation_simple_reflection (i : Fin 4) (r : typeF4Roots) :
    exceptionalRootPermutation (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) =
      typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex (Fin.revPerm i))
        (exceptionalRootPermutation r) := by
  rw [exceptionalRootPermutation_reflection, exceptionalRootPermutation_simple]

/-- Duality preserves opposite roots. -/
public theorem exceptionalRootPermutation_neg (r : typeF4Roots) :
    letI := typeF4RootPairing.indexNeg
    exceptionalRootPermutation (-r) = -exceptionalRootPermutation r :=
  exceptionalRootPermutation_reflection r r

/-- Diagram reversal intertwines the Weyl permutation of every simple word. -/
public theorem exceptionalRootPermutation_wordProd
    (word : List typeF4RootPairing_base.support) (r : typeF4Roots) :
    exceptionalRootPermutation
        (typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd word) r) =
      typeF4RootPairing.weylGroupToPerm
        (typeF4RootPairing_base.wordProd (word.map simplePermutation))
        (exceptionalRootPermutation r) := by
  induction word with
  | nil => simp only [List.map_nil, RootPairing.Base.wordProd_nil, map_one,
      Equiv.Perm.one_apply]
  | cons i word ih =>
    rw [List.map_cons, RootPairing.Base.wordProd_cons,
      RootPairing.Base.wordProd_cons]
    change exceptionalRootPermutation (typeF4RootPairing.reflectionPerm i
      (typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd word) r)) =
      typeF4RootPairing.reflectionPerm (simplePermutation i)
        (typeF4RootPairing.weylGroupToPerm
          (typeF4RootPairing_base.wordProd (word.map simplePermutation))
          (exceptionalRootPermutation r))
    rw [exceptionalRootPermutation_reflection, ih, simplePermutation_val]

/-- The same Weyl identity on the root summand of the concrete 52 coordinates. -/
public theorem coordinatePermutation_wordProd
    (word : List typeF4RootPairing_base.support) (r : typeF4Roots) :
    coordinatePermutation (Sum.inr
        (typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd word) r)) =
      Sum.inr (typeF4RootPairing.weylGroupToPerm
        (typeF4RootPairing_base.wordProd (word.map simplePermutation))
        (exceptionalRootPermutation r)) := by
  rw [coordinatePermutation_inr, exceptionalRootPermutation_wordProd]

/-- Positivity is preserved by the exceptional duality. -/
public theorem exceptionalRootPermutation_isPos (r : typeF4Roots) :
    typeF4RootPairing_base.IsPos (exceptionalRootPermutation r) ↔
      typeF4RootPairing_base.IsPos r :=
  (exceptionalRootPermutation_spec.2.1 r).symm

end ReeF4.WordRelations
