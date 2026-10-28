module
public import Theory.GroupTheory.RegularKernelSplitting
public import Theory.Representation.BinaryAlternatingFiveFlag.Coordinates

/-!
# Splitting the marked natural binary A₅ extension

The five-point augmentation core restricts to the regular module for the
Klein four-group fixing the last point: its first four coordinates determine
the fifth. Evaluating on the orbit of the first point gives the literal
regular marking. The regular-kernel splitting theorem and Gaschütz over
this index-fifteen subgroup produce an actual complement in the extension.

Source: Aschbacher–Smith, the single alternating case of 2.4.29.
-/

public section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup AlternatingFiveFlag
local notation "A5" => alternatingGroup (Fin 5)
local notation "V" => Multiplicative (core (Fin 5))
private def T : Subgroup A5 := four.subgroupOf A5
private instance : DecidablePred (· ∈ T) := fun g => inferInstanceAs (Decidable (g.val ∈ four))
private instance : Fintype T := Subtype.fintype _

private def coordinates : V →* (T → Multiplicative (ZMod 2)) where
  toFun v t := Multiplicative.ofAdd (v.toAdd.val (t.val.val 0))
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem coordinates_bijective : Function.Bijective coordinates := by
  decide +kernel

private noncomputable def regular : V ≃* (T → Multiplicative (ZMod 2)) :=
  MulEquiv.ofBijective coordinates coordinates_bijective

private theorem card_T : Nat.card T = 4 :=
  (Nat.card_congr (subgroupOfEquivOfLe four_even).toEquiv).trans four_card

/-- Every extension of A₅ by its marked binary five-point core splits. -/
theorem exists_complement {G : Type*} [Group G] [Finite G]
    (q : G →* A5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd)) :
    ∃ K : Subgroup G, q.ker.IsComplement' K := by
  apply exists_complement_of_regular_preimage q hq T (e.trans regular)
  · intro g v x
    change coordinates (e (MulAut.conjNormal (g : G) v)) x =
      coordinates (e v) ((⟨q g, g.property⟩ : T)⁻¹ * x)
    rw [he]
    rfl
  · have hc : Nat.card q.ker = 16 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      decide +kernel
    have hi : T.index = 15 := by
      have hh := T.card_mul_index
      rw [card_T, nat_card_alternatingGroup] at hh
      norm_num [Nat.factorial] at hh
      omega
    rw [hc, T.index_comap_of_surjective hq, hi]
    decide
end BinaryPermutation.AlternatingFiveExtension
