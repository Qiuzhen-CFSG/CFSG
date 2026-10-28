module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.SmallNormalizer
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
import Mathlib.Tactic.Group

/-!
# Lifting the four-group normalizer choice through an actual A₆ section

Transport a Klein four-group F ≤ A through a supplied equivalence A ≃ A₆.
Conjugation by N_G(A) ∩ N_G(F) then lands in the normalizer of its inner image
in Aut(A₆). The fixed-subgroup models for transpositions discharge the premise
of the S₄ × C₂ normalizer theorem. The small-normalizer commuting choice lifts
back to G because both choices for the second actor lie in the centerless A.
No faithfulness of the full ambient normalizer action is needed.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 5.1, pp.235--236.
The actual A₆ normalizer model is supplied by the four-group geometry of
Aschbacher--Smith, printed pp.567--570; its transposition premise is proved
by `AlternatingSix.ShadowLocal.swapFixedEquiv`.
-/

open Subgroup Equiv AlternatingSix.ShadowLocal
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
namespace CommutingChoice

variable {G : Type*} [Group G] (A : Subgroup G) (j : A ≃* A6)

private def action : normalizer (A : Set G) →* AutA6 :=
  (MulAut.congr j).toMonoidHom.comp A.normalizerMonoidHom

private theorem action_apply (n : normalizer (A : Set G)) (x : A) :
    action A j n (j x) = j (A.normalizerMonoidHom n x) := by
  change j (A.normalizerMonoidHom n (j.symm (j x))) = _
  rw [j.symm_apply_apply]

private theorem action_inner (n : normalizer (A : Set G)) (hn : (n : G) ∈ A) :
    action A j n = MulAut.conj (j ⟨n, hn⟩) := by
  ext x
  obtain ⟨x, rfl⟩ := j.surjective x
  rw [action_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

private theorem action_injective_on_section (n t : normalizer (A : Set G))
    (hn : (n : G) ∈ A) (ht : (t : G) ∈ A)
    (h : action A j n = action A j t) : n = t := by
  rw [action_inner A j n hn, action_inner A j t ht] at h
  exact Subtype.ext (congrArg (fun x : A => (x : G)) (j.injective (inner_injective h)))

private theorem commute_of_action_commute (n t : normalizer (A : Set G))
    (ht : (t : G) ∈ A) (h : Commute (action A j n) (action A j t)) :
    Commute (n : G) (t : G) := by
  have he : n * t * n⁻¹ = t := by
    apply action_injective_on_section A j
    · exact (mem_normalizer_iff.mp n.property _).mp ht
    · exact ht
    · rw [map_mul, map_mul, map_inv, h.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hv := congrArg (fun z : normalizer (A : Set G) => (z : G)) he
  exact (mul_inv_eq_iff_eq_mul.mp hv : (n : G) * t = t * n)

private def modelFour (F : Subgroup G) : Subgroup A6 := (F.subgroupOf A).map j.toMonoidHom

private theorem modelFour_klein (F : Subgroup G) [IsKleinFour F] (hFA : F ≤ A) :
    IsKleinFour (modelFour A j F) := by
  let q : F ≃* modelFour A j F :=
    (subgroupOfEquivOfLe hFA).symm.trans
      ((F.subgroupOf A).equivMapOfInjective j.toMonoidHom j.injective)
  constructor
  · rw [← Nat.card_congr q.toEquiv, IsKleinFour.card_four]
  · rw [← Monoid.exponent_eq_of_mulEquiv q, IsKleinFour.exponent_two]

private theorem action_normalizes (F : Subgroup G) (n : normalizer (A : Set G))
    (hn : (n : G) ∈ normalizer (F : Set G)) :
    action A j n ∈ normalizer
      ((modelFour A j F).map (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
  rw [FourNormalizers.mem_inner_normalizer_iff]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨A.normalizerMonoidHom n y, ?_, (action_apply A j n y).symm⟩
    exact (mem_normalizer_iff.mp hn _).mp hy
  · rw [card_map_of_injective (action A j n).injective]

private def actingNormalizer (F : Subgroup G) : Subgroup G :=
  normalizer (A : Set G) ⊓ normalizer (F : Set G)

private def normalizerAction (F : Subgroup G) : actingNormalizer A F →*
    normalizer ((modelFour A j F).map (MulAut.conj : A6 →* AutA6) : Set AutA6) :=
  ((action A j).comp (inclusion inf_le_left)).codRestrict _
    (fun n => action_normalizes A j F ⟨n, n.property.1⟩ n.property.2)

private theorem normalizerAction_ne_one (F : Subgroup G) (n : actingNormalizer A F)
    (hn : (n : G) ∈ A) (hne : (n : G) ≠ 1) : normalizerAction A j F n ≠ 1 := by
  intro h
  apply hne
  have h' : action A j ⟨n, n.property.1⟩ = action A j 1 := by
    rw [map_one]
    exact congrArg (fun x : normalizer ((modelFour A j F).map
      (MulAut.conj : A6 →* AutA6) : Set AutA6) => (x : AutA6)) h
  exact congrArg Subtype.val (action_injective_on_section A j _ _ hn A.one_mem h')

private theorem commute_of_normalizerAction (F : Subgroup G) (n t : actingNormalizer A F)
    (ht : (t : G) ∈ A)
    (h : Commute (normalizerAction A j F n) (normalizerAction A j F t)) :
    Commute (n : G) (t : G) :=
  commute_of_action_commute A j ⟨n, n.property.1⟩ ⟨t, t.property.1⟩ ht
    (h.map (normalizer ((modelFour A j F).map
      (MulAut.conj : A6 →* AutA6) : Set AutA6)).subtype)

include j in
/-- Two cubic actors inverted by the same marked dihedral involution commute
up to conjugating the second by the central involution of that dihedral group.
All normalizers here refer to the actual subgroups of G. -/
public theorem choice_of_normalized_four
    (F : Subgroup G) [IsKleinFour F] (hFA : F ≤ A)
    (u v d : G) (c k : F)
    (huA : u ∈ normalizer (A : Set G)) (hvA : v ∈ A)
    (hdA : d ∈ normalizer (A : Set G))
    (huF : u ∈ normalizer (F : Set G)) (hvF : v ∈ normalizer (F : Set G))
    (hdF : d ∈ normalizer (F : Set G))
    (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (hd : d ^ 2 = 1)
    (hc : (c : G) ^ 2 = 1) (hk : (k : G) ^ 2 = 1) (hkne : (k : G) ≠ 1)
    (hdihedral : d * c * d * c = k)
    (hdu : d * u * d = u⁻¹) (hdv : d * v * d = v⁻¹) :
    Commute u v ∨ Commute u ((k : G)⁻¹ * v * k) := by
  let U : actingNormalizer A F := ⟨u, huA, huF⟩
  let V : actingNormalizer A F := ⟨v, le_normalizer hvA, hvF⟩
  let T : actingNormalizer A F := ⟨d, hdA, hdF⟩
  let C : actingNormalizer A F := ⟨c, le_normalizer (hFA c.property), le_normalizer c.property⟩
  let K : actingNormalizer A F := ⟨k, le_normalizer (hFA k.property), le_normalizer k.property⟩
  let f := normalizerAction A j F
  have hUK : U ^ 3 = 1 := Subtype.ext hu
  have hVK : V ^ 3 = 1 := Subtype.ext hv
  have hTK : T ^ 2 = 1 := Subtype.ext hd
  have hCK : C ^ 2 = 1 := Subtype.ext hc
  have hKK : K ^ 2 = 1 := Subtype.ext hk
  have hD : T * C * T * C = K := Subtype.ext hdihedral
  have hTU : T * U * T = U⁻¹ := Subtype.ext hdu
  have hTV : T * V * T = V⁻¹ := Subtype.ext hdv
  let := modelFour_klein A j F hFA
  obtain ⟨q⟩ := FourNormalizers.aut_normalizer_equiv_symmetric_prod
    (fun σ hσ => ⟨swapFixedEquiv σ hσ⟩) (modelFour A j F)
  have hchoice := commuting_choice_in_symmetricFour_times_two q (f U) (f V) (f T) (f C)
    (by rw [← map_pow, hUK, map_one]) (by rw [← map_pow, hVK, map_one])
    (by rw [← map_pow, hTK, map_one]) (by rw [← map_pow, hCK, map_one])
    (by rw [← map_mul, ← map_mul, ← map_mul, hD, ← map_pow, hKK, map_one])
    (by rw [← map_mul, ← map_mul, ← map_mul, hD]
        exact normalizerAction_ne_one A j F K (hFA k.property) hkne)
    (by rw [← map_mul, ← map_mul, hTU, map_inv])
    (by rw [← map_mul, ← map_mul, hTV, map_inv])
  rcases hchoice with h | h
  · exact Or.inl (commute_of_normalizerAction A j F U V hvA h)
  · rw [← map_mul, ← map_mul, ← map_mul, hD] at h
    have h' : Commute (f U) (f (K⁻¹ * V * K)) := by
      simpa only [map_mul, map_inv] using h
    exact Or.inr (commute_of_normalizerAction A j F U (K⁻¹ * V * K)
      (A.mul_mem (A.mul_mem (A.inv_mem (hFA k.property)) hvA) (hFA k.property)) h')

end CommutingChoice
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
