module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.Basic

/-!
# Root transport in the middle-node normalizer

Simple reflections at nodes 1 and 2 preserve the signed B₂ support. The
nonzero rank-one words have the same root permutation as their parameter-one
lifts: conjugation by a simple-coroot diagonal matrix changes the parameter.
Composition and inversion preserve the support and opposite-root identities.
These additional properties keep the later Bruhat factors in the Levi.

Source: GLS3 1.12.1(g,h), 2.3.8(b), and Table 2.4 type V,
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction WordRelations
open Subgroup LargeLocalSeeds PairNormalization.OppositionCell.FixedBruhatCover
open PairNormalization.OppositionCell NormalizerGeometry
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
namespace SuzukiSplitNormalForm
variable {m : ℕ}

def Supported (r : F4Chevalley.Root) : Prop :=
  ∀ i, i ∉ leviNodes .suzuki → typeF4SimpleCoefficient r.val i = 0

private theorem neg_val (r : F4Chevalley.Root) : (-r).val = -r.val := by
  change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
  simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

theorem supported_neg {r : F4Chevalley.Root} (hr : Supported r) : Supported (-r) := by
  intro i hi
  rw [neg_val]
  have h := hr i hi
  fin_cases i <;> simp_all [typeF4SimpleCoefficient] <;> linarith

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val - (typeF4CorootScale (typeF4SimpleRootIndex i) *
        dot r.val (typeF4SimpleRoot i)) • typeF4SimpleRoot i := by
  change typeF4RootPairing.root _ = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing]
  rfl

theorem reflection_supported (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
    {r : F4Chevalley.Root} (hr : Supported r) :
    Supported (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) := by
  intro j hj
  have h := hr j hj
  have hi' : i = 1 ∨ i = 2 := by simpa [leviNodes] using hi
  have hj' : j = 0 ∨ j = 3 := by fin_cases j <;> simp_all [leviNodes]
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
    rw [reflection_val] <;>
    simpa [typeF4SimpleCoefficient, typeF4SimpleRoot, basisVector] using h

theorem reflection_neg (i r : F4Chevalley.Root) :
    typeF4RootPairing.reflectionPerm i (-r) = -typeF4RootPairing.reflectionPerm i r := by
  apply Subtype.ext
  rw [neg_val]
  change typeF4RootPairing.root _ = -typeF4RootPairing.root _
  rw [RootPairing.root_reflectionPerm]
  change typeF4RootPairing.reflection i (-r).val = _
  rw [neg_val, map_neg, RootPairing.root_reflectionPerm]
  rfl

/-- The exact root action also preserves the middle support and opposite roots. -/
structure Transport (n : SplitGroup m) : Type extends RootTransport n where
  supported : ∀ r, Supported r → Supported (perm r)
  neg : ∀ r, perm (-r) = -perm r

private theorem simple_transport (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
    (t : (CoefficientField m)ˣ) :
    Nonempty (Transport (rankOneRepresentative m (typeF4SimpleRootIndex i) t)) := by
  obtain ⟨v, hv⟩ : ∃ v : (CoefficientField m)ˣ, v ^ 2 = t := by
    apply Finite.surjective_of_injective (f := fun v : (CoefficientField m)ˣ => v ^ 2)
    intro u v huv
    apply Units.ext
    exact CharTwo.sq_injective (congrArg Units.val huv)
  let j := typeF4RootPairing_baseEquiv i
  let p := integralChevalleySimpleCorootParameter (b := typeF4RootPairing_base) j v
  let D := F4Chevalley.torusConjugation.torusElement p
  let S := titsUnit (S := CoefficientField m) [j]
  let c := integralChevalleyRootScale (P := typeF4RootPairing) p
  let R := typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i)
  have hc (q : F4Chevalley.Root) (a : CoefficientField m) :
      D⁻¹ * F4Chevalley.rootCurve q a * D = F4Chevalley.rootCurve q ((c q : CoefficientField m) * a) :=
    F4Chevalley.rootCurve_torus_conjugation p q a
  have hci (q : F4Chevalley.Root) (a : CoefficientField m) :
      D * F4Chevalley.rootCurve q a * D⁻¹ = F4Chevalley.rootCurve q (((c q)⁻¹ : (CoefficientField m)ˣ) * a) := by
    have h := hc q (((c q)⁻¹ : (CoefficientField m)ˣ) * a)
    simp only [← mul_assoc, Units.mul_inv, one_mul] at h
    rw [← h]
    group
  have hp (a : CoefficientField m) :
      D⁻¹ * F4Chevalley.rootCurve j.val a * D = F4Chevalley.rootCurve j.val ((t : CoefficientField m) * a) := by
    simpa only [RootPairing.pairingIn_same, zpow_ofNat, hv] using
      F4Chevalley.rootCurve_simpleCoroot_conjugation j v j.val a
  have hn (a : CoefficientField m) :
      D⁻¹ * F4Chevalley.rootCurve (-j.val) a * D =
        F4Chevalley.rootCurve (-j.val) (((t⁻¹ : (CoefficientField m)ˣ) : CoefficientField m) * a) := by
    simpa only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left,
      RootPairing.pairingIn_same, zpow_neg, zpow_ofNat, hv] using
      F4Chevalley.rootCurve_simpleCoroot_conjugation j v (-j.val) a
  have he : (rankOneRepresentative m (typeF4SimpleRootIndex i) t).val = D⁻¹ * S * D := by
    change F4Chevalley.rootCurve j.val (t : CoefficientField m) *
      F4Chevalley.rootCurve (-j.val) (-((t⁻¹ : (CoefficientField m)ˣ) : CoefficientField m)) *
      F4Chevalley.rootCurve j.val (t : CoefficientField m) = _
    have hs : S = F4Chevalley.rootCurve j.val 1 * F4Chevalley.rootCurve (-j.val) (-1) *
        F4Chevalley.rootCurve j.val 1 := by simp [S, titsUnit_cons, titsUnit_nil]
    calc
      _ = (D⁻¹ * F4Chevalley.rootCurve j.val 1 * D) *
          (D⁻¹ * F4Chevalley.rootCurve (-j.val) (-1) * D) *
          (D⁻¹ * F4Chevalley.rootCurve j.val 1 * D) := by rw [hp, hn]; simp
      _ = _ := by rw [hs]; group
  refine ⟨{ perm := R
            scale := fun q => c (R q) * (c q)⁻¹
            conj_root := ?_
            supported := fun r hr => reflection_supported i hi hr
            neg := fun r => reflection_neg _ r }⟩
  intro q a
  apply Subtype.ext
  change (rankOneRepresentative m (typeF4SimpleRootIndex i) t).val *
    F4Chevalley.rootCurve q a * (rankOneRepresentative m (typeF4SimpleRootIndex i) t).val⁻¹ = _
  rw [he]
  calc
    _ = D⁻¹ * (S * (D * F4Chevalley.rootCurve q a * D⁻¹) * S⁻¹) * D := by group
    _ = _ := by
      rw [hci, NormalizerGeometry.RankOneTransport.simple_conj, hc]
      simp only [Units.val_mul, mul_assoc]
      rfl

/-- Every word in the prescribed normalizer preserves the signed B₂ subsystem. -/
theorem transport {n : SplitGroup m} (hn : n ∈ splitSuzukiNormalizer m) :
    Nonempty (Transport n) := by
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
    obtain ⟨i, hi, t, rfl⟩ := hn
    exact simple_transport i hi t
  | one => exact ⟨{ toRootTransport := rootTransport_one m
                    supported := fun _ h => h
                    neg := fun _ => rfl }⟩
  | mul n k _ _ hn hk =>
    obtain ⟨a⟩ := hn
    obtain ⟨b⟩ := hk
    exact ⟨{ toRootTransport := rootTransport_mul a.toRootTransport b.toRootTransport
             supported := fun r hr => a.supported _ (b.supported _ hr)
             neg := fun r => by change a.perm (b.perm (-r)) = _; rw [b.neg, a.neg]; rfl }⟩
  | inv n _ hn =>
    obtain ⟨a⟩ := hn
    have hback (r : F4Chevalley.Root) (hr : Supported r) : Supported (a.perm.symm r) := by
      have hsurj := Finite.surjective_of_injective
        (f := fun r : {r : F4Chevalley.Root // Supported r} =>
          (⟨a.perm r.val, a.supported _ r.property⟩ : {r : F4Chevalley.Root // Supported r}))
        (by intro x y h; exact Subtype.ext (a.perm.injective (congrArg Subtype.val h)))
      obtain ⟨s, hs⟩ := hsurj ⟨r, hr⟩
      have he : s.val = a.perm.symm r := by
        simpa using congrArg (fun s : {r : F4Chevalley.Root // Supported r} => a.perm.symm s.val) hs
      exact he ▸ s.property
    refine ⟨{ toRootTransport := rootTransport_inv a.toRootTransport
              supported := hback
              neg := ?_ }⟩
    intro r
    apply a.perm.injective
    change a.perm (a.perm.symm (-r)) = a.perm (-a.perm.symm r)
    rw [a.neg, a.perm.apply_symm_apply, a.perm.apply_symm_apply]
end SuzukiSplitNormalForm
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
