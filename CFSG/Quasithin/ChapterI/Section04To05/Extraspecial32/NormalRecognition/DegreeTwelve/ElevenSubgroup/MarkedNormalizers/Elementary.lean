module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.Inputs
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The marked nine-group and faithful symmetric-group normalizer

The two cubic subgroups have trivial intersection because the distinguished
involution fixes one and inverts the other. Their commuting product is thus
an elementary abelian group of order nine, with its literal embedding in S.
The self-centralizing fusion eight forces C_G(S) into S, and the trivial
center of S₆ then makes the normalizer action faithful. We also identify
the central involution candidate b = uz and retain the literal relative
normalizer K = L ∩ N_G(D).

These are preliminary consequences of the published symmetric-six input;
they do not assert that the normalizer has the full automorphism image.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 4.8–4.9 and the proof of 4.10, pp.41–42.
-/

@[expose] public section

open Subgroup DoubleCoset
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
namespace SymmetricSixData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} (s : SymmetricSixData h a)

theorem card_cubicInG : Nat.card (cubicInG h) = 3 := by
  rw [cubicInG, card_map_of_injective (Centralizer z).subtype_injective]
  exact h.sylow_three_card

theorem cubic_disjoint : Disjoint (cubicInG h) s.X1 := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  have hxz : z * x = x * z :=
    (mem_centralizer_singleton_iff.mp ((map_subtype_le _) hx.1)).symm
  have hxi : x = x⁻¹ := by
    calc
      x = z * x * z⁻¹ := by rw [hxz, mul_inv_cancel_right]
      _ = x⁻¹ := s.z_inverts_X1 x hx.2
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    conv_lhs => lhs; rw [hxi]
    exact inv_mul_cancel x
  have hx3 : x ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x, hx.2⟩ : s.X1))
    rw [s.card_X1] at hh
    exact congrArg Subtype.val hh
  have hx1 : x = 1 := by
    simpa [pow_succ, hx2] using hx3
  exact mem_bot.mpr hx1

def markedNine : Subgroup G := cubicInG h ⊔ s.X1

theorem markedNine_le : s.markedNine ≤ s.S := by
  rw [markedNine, s.generated]
  exact sup_le_sup le_sup_right le_rfl

theorem card_markedNine : Nat.card s.markedNine = 9 := by
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (cubicInG h) s.X1 s.cubic_disjoint (le_centralizer_iff.mp s.X1_centralizes_X)
  rw [markedNine, ← Nat.card_congr e.toEquiv, Nat.card_prod, card_cubicInG, s.card_X1]

theorem elementary_markedNine : IsElementaryAbelian 3 s.markedNine := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic (cubicInG h) := isCyclic_of_prime_card (card_cubicInG (h := h))
  let : IsCyclic s.X1 := isCyclic_of_prime_card s.card_X1
  let : IsElementaryAbelian 3 (cubicInG h) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      simpa only [card_cubicInG] using (pow_card_eq_one' (x := x)) }
  let : IsElementaryAbelian 3 s.X1 := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      simpa only [s.card_X1] using (pow_card_eq_one' (x := x)) }
  exact IsElementaryAbelian.sup_of_le_centralizer s.X1_centralizes_X

theorem u_commutes_z : Commute s.u z := by
  have hu : Commute a.u z := mem_centralizer_singleton_iff.mp a.u_centralizes
  rcases s.u_choice with he | he
  · rw [he]
    exact hu
  · rw [he]
    exact hu.mul_left (Commute.refl z)

/-- Both permitted choices of u still invert the originally chosen X. -/
theorem u_inverts_cubicInG (x : G) (hx : x ∈ cubicInG h) : s.u * x * s.u⁻¹ = x⁻¹ := by
  obtain ⟨y, hy, rfl⟩ := hx
  change s.u * (y : G) * s.u⁻¹ = (y : G)⁻¹
  have hu := a.u_inverts_X (⟨y, hy⟩ : h.X)
  have hz : z * (y : G) = (y : G) * z :=
    (mem_centralizer_singleton_iff.mp y.property).symm
  rcases s.u_choice with he | he
  · simpa only [he] using hu
  · rw [he, mul_inv_rev]
    calc
      a.u * z * (y : G) * (z⁻¹ * a.u⁻¹) = a.u * (z * y * z⁻¹) * a.u⁻¹ := by group
      _ = a.u * (y : G) * a.u⁻¹ := by rw [hz, mul_inv_cancel_right]
      _ = (y : G)⁻¹ := hu
theorem uz_sq : (s.u * z) ^ 2 = 1 := by
  rw [s.u_commutes_z.mul_pow]
  have hu : s.u ^ 2 = 1 := s.u_order ▸ pow_orderOf_eq_one s.u
  have hz : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
  rw [hu, hz, one_mul]

theorem uz_ne_one : s.u * z ≠ 1 := by
  intro hb
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two, h.involution] using pow_orderOf_eq_one z)
  have hu : s.u = z := (eq_inv_of_mul_eq_one_left hb).trans hz
  rcases s.u_choice with he | he
  · exact a.u_not_core (he ▸ hu.symm ▸ h.involution_mem_coreInG)
  · have hau : a.u = 1 := by
      apply mul_right_cancel (b := z)
      simpa only [one_mul] using he.symm.trans hu
    exact a.u_not_core (hau ▸ (coreInG z).one_mem)

theorem uz_order : orderOf (s.u * z) = 2 := by
  exact orderOf_eq_prime_iff.mpr ⟨s.uz_sq, s.uz_ne_one⟩

private theorem perm_eq_one_of_central (p : Equiv.Perm (Fin 6))
    (hp : ∀ q, q * p = p * q) : p = 1 := by
  apply Equiv.ext
  intro i
  change p i = i
  by_contra hn
  obtain ⟨j, hji, hjp⟩ := Fin.exists_ne_and_ne_of_two_lt i (p i) (by decide)
  have hh := congrArg (fun q : Equiv.Perm (Fin 6) => q i)
    (hp (Equiv.swap (p i) j))
  simp only [Equiv.Perm.mul_apply] at hh
  rw [Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hn) hji.symm] at hh
  exact hjp hh

theorem centralizer_eq_bot (d : FusionEightData z) : centralizer (s.S : Set G) = ⊥ := by
  have hf : fusionCore z ≤ s.S := by
    rw [s.generated]
    exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  apply bot_unique
  intro x hx
  have hxF : x ∈ fusionCore z := by
    rw [← d.centralizer_eq]
    exact centralizer_le hf hx
  have hxS := hf hxF
  have hc : s.equiv ⟨x, hxS⟩ = 1 := by
    apply perm_eq_one_of_central
    intro q
    obtain ⟨y, rfl⟩ := s.equiv.surjective q
    rw [← map_mul, ← map_mul]
    exact congrArg s.equiv (Subtype.ext (hx y y.property))
  have hx1 : (⟨x, hxS⟩ : s.S) = 1 := s.equiv.injective (hc.trans s.equiv.map_one.symm)
  exact mem_bot.mpr (congrArg Subtype.val hx1)

theorem normalizerAction_injective (d : FusionEightData z) :
    Function.Injective s.S.normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [normalizerMonoidHom_ker, s.centralizer_eq_bot d]
  simp

/-- The ambient image of the relative normalizer N_L(D). -/
def markedK (L : Subgroup G) : Subgroup G :=
  L ⊓ normalizer (s.markedNine : Set G)

theorem markedK_le (L : Subgroup G) : s.markedK L ≤ L := inf_le_left

/-- The action quotient uses exactly the intrinsic normalizer in L. -/
theorem markedK_subgroupOf (L : Subgroup G) (hDL : s.markedNine ≤ L) :
    (s.markedK L).subgroupOf L = normalizer (s.markedNine.subgroupOf L : Set L) := by
  rw [markedK, inf_subgroupOf_left, subgroupOf_normalizer_eq hDL]

end SymmetricSixData
end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
