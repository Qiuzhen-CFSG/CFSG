module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.Extension

/-!
# The literal nine-group quotient and the Sylow action

A nine-group in S₆ embeds as a Sylow three-subgroup of the specified
extension. Its normalizer inside the extension is exactly the relative
subgroup in `M10.ActionFacts`. Sylow conjugacy identifies its coset space
with the actual Sylow three-subgroups, equivariantly for left multiplication
on cosets and conjugation on Sylow subgroups.

Consequently, a count of ten Sylow subgroups gives the normalizer order 72,
and three-transitivity of their action gives precisely the required quotient
action. The final lemma obtains the double-coset cover for every outside
representative from two-transitivity. The finite count and three-transitivity
are explicit premises here, to be discharged by the concrete action calculation.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 4.9 and the degree-ten action in 4.10, pp.41–42.
-/

@[expose] public section

open Subgroup
namespace AlternatingSix.M10.Action
open ShadowLocal

/-- The given nine-group as a Sylow subgroup of the literal extension. -/
noncomputable def markedSylow (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    Sylow 3 extension :=
  Sylow.ofCard ((nine D).subgroupOf extension) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe (nine_le_extension D hD)).toEquiv,
      card_nine D hD, card_extension]
    decide +kernel)

theorem markedSylow_normalizer (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    normalizer (markedSylow D hD : Set extension) = (stabilizer D).subgroupOf extension := by
  have h := Subgroup.comap_normalizer_eq_of_le_range
    (f := extension.subtype) (H := nine D) (by simpa using nine_le_extension D hD)
  change normalizer ((nine D).comap extension.subtype : Set extension) = _
  rw [← h]
  ext x
  simp only [mem_comap, stabilizer, mem_subgroupOf, mem_inf, x.property, true_and, Subgroup.subtype_apply]

/-- The canonical equivariant map, with precisely the contract's quotient. -/
noncomputable def cosetToSylow (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    (extension ⧸ (stabilizer D).subgroupOf extension) →[extension] Sylow 3 extension where
  toFun c := Quotient.liftOn' c (fun g : extension => g • markedSylow D hD) (by
    intro x y hxy
    have hn : x⁻¹ * y ∈ normalizer (markedSylow D hD : Set extension) := by
      rw [markedSylow_normalizer]
      exact QuotientGroup.leftRel_apply.mp hxy
    have hs := Sylow.smul_eq_iff_mem_normalizer.mpr hn
    calc
      x • markedSylow D hD = x • ((x⁻¹ * y) • markedSylow D hD) := congrArg (x • ·) hs.symm
      _ = y • markedSylow D hD := by rw [← mul_smul, mul_inv_cancel_left])
  map_smul' x c := by
    induction c using Quotient.inductionOn' with | h y =>
      exact mul_smul x y (markedSylow D hD)

theorem cosetToSylow_bijective (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    Function.Bijective (cosetToSylow D hD) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn' with | h x =>
      induction b using Quotient.inductionOn' with | h y =>
        intro he
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply, ← markedSylow_normalizer]
        apply Sylow.smul_eq_iff_mem_normalizer.mp
        change x • markedSylow D hD = y • markedSylow D hD at he
        rw [mul_smul, ← he, inv_smul_smul]
  · intro P
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq extension (markedSylow D hD) P
    exact ⟨(g : extension ⧸ (stabilizer D).subgroupOf extension), hg⟩

theorem card_quotient_of_card_sylow
    (hc : Nat.card (Sylow 3 extension) = 10)
    (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    Nat.card (extension ⧸ (stabilizer D).subgroupOf extension) = 10 := by
  rw [Nat.card_congr (Equiv.ofBijective _ (cosetToSylow_bijective D hD)), hc]

theorem card_stabilizer_of_card_sylow
    (hc : Nat.card (Sylow 3 extension) = 10)
    (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    Nat.card (stabilizer D) = 72 := by
  have hh := ((stabilizer D).subgroupOf extension).card_mul_index
  rw [Subgroup.index_eq_card, card_quotient_of_card_sylow hc D hD,
    Nat.card_congr (subgroupOfEquivOfLe (show stabilizer D ≤ extension from inf_le_left)).toEquiv,
    card_extension] at hh
  omega

theorem quotient_threeTransitive_of_sylow
    (ht : MulAction.IsMultiplyPretransitive extension (Sylow 3 extension) 3)
    (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    MulAction.IsMultiplyPretransitive extension
      (extension ⧸ (stabilizer D).subgroupOf extension) 3 := by
  exact (MulAction.IsPretransitive.of_embedding_congr (f := cosetToSylow D hD)
    Function.surjective_id (cosetToSylow_bijective D hD)).mpr ht

theorem doubleCoset_cover_of_twoTransitive
    (D : Subgroup (Equiv.Perm (Fin 6)))
    (ht : MulAction.IsMultiplyPretransitive extension
      (extension ⧸ (stabilizer D).subgroupOf extension) 2)
    (r : AutA6) (hr : r ∈ extension) (hrK : r ∉ stabilizer D)
    (l : AutA6) (hl : l ∈ extension) :
    l ∈ stabilizer D ∨ l ∈ DoubleCoset.doubleCoset r (stabilizer D) (stabilizer D) := by
  classical
  by_cases hlK : l ∈ stabilizer D
  · exact Or.inl hlK
  right
  let rE : extension := ⟨r, hr⟩
  let lE : extension := ⟨l, hl⟩
  let K := (stabilizer D).subgroupOf extension
  have hrne : ((1 : extension) : extension ⧸ K) ≠ rE := by
    intro he
    apply hrK
    change rE ∈ K
    simpa only [inv_one, one_mul] using QuotientGroup.eq.mp he
  have hlne : ((1 : extension) : extension ⧸ K) ≠ lE := by
    intro he
    apply hlK
    change lE ∈ K
    simpa only [inv_one, one_mul] using QuotientGroup.eq.mp he
  obtain ⟨a, ha, har⟩ := MulAction.is_two_pretransitive_iff.mp ht hrne hlne
  have haK : a ∈ K := by
    rw [← MulAction.stabilizer_quotient K]
    exact ha
  have har' : (((a * rE : extension)) : extension ⧸ K) = lE := har
  have hk : (a * rE)⁻¹ * lE ∈ K := QuotientGroup.eq.mp har'
  refine DoubleCoset.mem_doubleCoset.mpr
    ⟨(a : AutA6), haK, (((a * rE)⁻¹ * lE : extension) : AutA6), hk, ?_⟩
  change l = (a : AutA6) * r * (((a : AutA6) * r)⁻¹ * l)
  group

end AlternatingSix.M10.Action
