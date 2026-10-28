module

public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction

/-!
# Coprime action kernels and fixed indices on Frattini quotients

For a finite group A acting on a finite p-group P, with |A| coprime to p,
the supplied action and its induced action on P / Φ(P) have the same kernel.
Thus every subgroup of A acting nontrivially on P still acts nontrivially
on the Frattini quotient; faithfulness of the original action is not needed.
Apply the faithful coprime Frattini-action theorem to the image of the
supplied homomorphism, whose order divides |A|.

For any subgroup H of A, the H-fixed subgroup index on P / Φ(P) divides
the H-fixed subgroup index on P. This second assertion requires neither
finiteness, the p-group hypothesis nor coprimality: the quotient map takes
H-fixed elements to H-fixed elements, and subgroup indices divide under
inclusion and surjective images. Both actions are installed from the
literal supplied homomorphisms before restriction to H.

Source: the Burnside basis-kernel theorem, in the form proved in
`Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel`. These reductions
are used in the fixed-subgroup index argument of Lyons,
*A Characterization of the Group U₃(4)* (1972), p.386.
-/

namespace MonoidHom

/-- A possibly nonfaithful coprime action has the same kernel on a finite
p-group and its Frattini quotient. -/
public theorem ker_frattini_action_of_coprime
    {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
    {p : ℕ} (hP : IsPGroup p P) (ρ : A →* MulAut P)
    (hcop : Nat.Coprime (Nat.card A) p) :
    ((Subgroup.quotientAut (frattini P)).comp ρ).ker = ρ.ker := by
  have hi := injective_frattini_action_of_coprime hP ρ.range.subtype
    ρ.range.subtype_injective (hcop.coprime_dvd_left (Subgroup.card_range_dvd ρ))
  ext a
  constructor
  · intro ha
    change Subgroup.quotientAut (frattini P) (ρ a) = 1 at ha
    have he : ρ.rangeRestrict a = 1 := hi (by
      change Subgroup.quotientAut (frattini P) (ρ a) =
        Subgroup.quotientAut (frattini P) 1
      rw [map_one]
      exact ha)
    exact congrArg Subtype.val he
  · intro ha
    change ρ a = 1 at ha
    change Subgroup.quotientAut (frattini P) (ρ a) = 1
    rw [ha, map_one]

/-- Any actor subgroup acting nontrivially still acts nontrivially on the
Frattini quotient under the coprimality hypothesis. -/
public theorem not_le_ker_frattini_action_of_coprime
    {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
    {p : ℕ} (hP : IsPGroup p P) (ρ : A →* MulAut P)
    (hcop : Nat.Coprime (Nat.card A) p) (H : Subgroup A)
    (hH : ¬ H ≤ ρ.ker) :
    ¬ H ≤ ((Subgroup.quotientAut (frattini P)).comp ρ).ker := by
  rwa [ker_frattini_action_of_coprime hP ρ hcop]

/-- For the literal supplied action and its induced Frattini action, the
H-fixed index on the quotient divides the H-fixed index upstairs. No
finiteness or coprimality hypothesis is needed. -/
public theorem fixedPointSubgroup_frattini_index_dvd
    {A P : Type*} [Group A] [Group P]
    (ρ : A →* MulAut P) (H : Subgroup A) :
    letI : MulDistribMulAction A P := MulDistribMulAction.compHom P ρ
    letI : MulDistribMulAction A (P ⧸ frattini P) :=
      MulDistribMulAction.compHom (P ⧸ frattini P)
        ((Subgroup.quotientAut (frattini P)).comp ρ)
    (fixedPointSubgroup H (P ⧸ frattini P)).index ∣
      (fixedPointSubgroup H P).index := by
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P ρ
  let : MulDistribMulAction A (P ⧸ frattini P) :=
    MulDistribMulAction.compHom (P ⧸ frattini P)
      ((Subgroup.quotientAut (frattini P)).comp ρ)
  have hle : (fixedPointSubgroup H P).map (QuotientGroup.mk' (frattini P)) ≤
      fixedPointSubgroup H (P ⧸ frattini P) := by
    rintro _ ⟨x, hx, rfl⟩ h
    change Subgroup.quotientAut (frattini P) (ρ (h : A))
      (QuotientGroup.mk' (frattini P) x) = QuotientGroup.mk' (frattini P) x
    rw [Subgroup.quotientAut_apply_mk]
    exact congrArg (QuotientGroup.mk' (frattini P)) (hx h)
  exact (Subgroup.index_dvd_of_le hle).trans
    ((fixedPointSubgroup H P).index_map_dvd (QuotientGroup.mk'_surjective _))

end MonoidHom
