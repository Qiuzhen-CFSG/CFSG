module
public import Theory.SpecificGroups.ReeTwo.FixingActionCensus

/-!
# The standard half of the root-fixing action census

Ten of the twenty squaring actions differ from the specified action only by
conjugation by a power of the five-action and multiplication by the inner
action of root 2. The finite certificates below exhibit both corrections.
This does not claim that an arbitrary fixing action belongs to this half.

Source: the checked Shinoda (1975), pp.81–83, root-action tables in
`FixingActionRepresentatives`.
-/

@[expose] public section
namespace ReeTwo.Core.FixingActionCensus
open CensusPacked

/-- The census entries obtainable from the standard action by a five-power
coordinate change and a fixed-root correction of the actor. -/
def IsStandard (i : Fin 20) : Prop := i ∈ ({0,1,3,5,9,10,11,13,15,19} : Finset (Fin 20))

instance (i : Fin 20) : Decidable (IsStandard i) := inferInstanceAs (Decidable (_ ∈ _))

private def power (i : Fin 20) : Fin 5 :=
  ![4,3,0,4,0,1,0,0,0,0,3,2,0,1,0,2,0,0,0,0] i
private def shift (i : Fin 20) : Fin 2 :=
  ![0,0,0,1,0,1,0,0,0,1,1,1,0,0,0,0,0,0,0,0] i
private def aCodes : CoreRoot → Nat :=
  ![1015,862,4,24,16,864,960,384,256,512]

private theorem aCodes_eq (j : CoreRoot) : aCodes j = code (a (root j)) :=
  (by decide +kernel : ∀ j, aCodes j = code (a (root j))) j

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem table : ∀ (i : Fin 20), IsStandard i → ∀ j : CoreRoot,
    act (representativeCodes i) ((cAct^[(power i).val]) (code (root j))) =
      pmul (pmul (ppow 4 (shift i).val)
        ((cAct^[(power i).val]) (aCodes j))) (pinv (ppow 4 (shift i).val)) := by
  decide +kernel

/-- An explicit five-power coordinate change and fixed-root correction turn
each standard census entry into the specified four-action. -/
theorem standard_intertwine (i : Fin 20) (hi : IsStandard i) :
    ∃ (k : Fin 5) (b : Fin 2),
      representative i * c ^ k.val =
        MulAut.conj ((root 2) ^ b.val) * c ^ k.val * a := by
  refine ⟨power i, shift i, aut_ext (fun j => ?_)⟩
  apply code_injective
  change code (representative i ((c ^ (power i).val) (root j))) =
    code ((root 2) ^ (shift i).val *
      (c ^ (power i).val) (a (root j)) * ((root 2) ^ (shift i).val)⁻¹)
  rw [representative_apply, representativeMap_code, ← cAct_iterate_code,
    ← pmul_code, ← pmul_code, ← pinv_code, ← ppow_code,
    ← cAct_iterate_code, ← aCodes_eq]
  exact table i hi j

/-- Standard census entries can be corrected inside the actual group,
retaining the five-element and the fourth-power relation. -/
theorem exists_standard_actor
    {H : Type*} [Group H] (f : H →* MulAut Core) (c a t : H)
    (ha4 : a ^ 4 = 1) (ht4 : t ^ 4 = 1)
    (hac : a * c * a⁻¹ = c ^ 2) (hct : Commute c t) (hat : Commute a t)
    (hc : f c = Core.c) (ht : f t = MulAut.conj (root 2))
    (i : Fin 20) (hi : IsStandard i) (ha : f a = representative i) :
    ∃ b : H, b ^ 4 = 1 ∧ b * c * b⁻¹ = c ^ 2 ∧ f b = Core.a := by
  obtain ⟨k, r, hr⟩ := standard_intertwine i hi
  let u := t ^ r.val
  let v := c ^ k.val
  let d : MulAut H := MulAut.conj v⁻¹
  have hu4 : u ^ 4 = 1 := by
    dsimp [u]
    rw [← pow_mul, Nat.mul_comm, pow_mul, ht4, one_pow]
  have hua : Commute u⁻¹ a := ((hat.pow_right r.val).symm).inv_left
  have huc : Commute u⁻¹ c := ((hct.pow_right r.val).symm).inv_left
  have hd : d c = c := by
    change v⁻¹ * c * (v⁻¹)⁻¹ = c
    rw [((Commute.refl c).pow_left k.val).inv_left.eq, mul_inv_cancel_right]
  have he : (u⁻¹ * a) * c * (u⁻¹ * a)⁻¹ = c ^ 2 := by
    calc
      _ = u⁻¹ * (a * c * a⁻¹) * u := by group
      _ = u⁻¹ * c ^ 2 * u := by rw [hac]
      _ = c ^ 2 := by rw [(huc.pow_right 2).eq]; group
  have hv : f v = Core.c ^ k.val := by rw [map_pow, hc]
  have hu : f u = MulAut.conj ((root 2) ^ r.val) := by
    dsimp [u]
    rw [map_pow, ht, ← map_pow]
  refine ⟨d (u⁻¹ * a), ?_, ?_, ?_⟩
  · rw [← map_pow, hua.mul_pow, inv_pow, hu4, ha4, inv_one, _root_.one_mul, map_one]
  · have hh := congrArg d he
    simpa only [map_mul, map_inv, map_pow, hd] using hh
  · change f (v⁻¹ * (u⁻¹ * a) * (v⁻¹)⁻¹) = Core.a
    simp only [map_mul, map_inv, inv_inv]
    have hh : f a * f v = f u * f v * Core.a := by rw [hu, hv, ha]; exact hr
    calc
      _ = (f v)⁻¹ * (f u)⁻¹ * (f a * f v) := by group
      _ = Core.a := by rw [hh]; group
end ReeTwo.Core.FixingActionCensus
