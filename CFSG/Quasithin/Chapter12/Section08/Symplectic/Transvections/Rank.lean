module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.QuotientTransport
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The exact transvection rank identity

The hat image has kernel E∩Z(U), and X → Xdot/Z(U)^g-dot has kernel
EZ(U)^g. Count the normalized product EZ(U)^g and use |X|=|W|,
|Z(U)^g|=|Z(U)|, |U:W|=2, and the equal center-intersection orders.
This gives 2|Ehat||Xdot/Z(U)^g-dot|=|Uhat|. Elementary abelianness then
converts the cardinal identity to the source prime-rank identity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
12.8.11(5), printed p.854 / PDF p.871. The source assembly discharges
the index and center-order premises using the geometric modules.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem binary_card (A : Type*) [Group A] [Finite A] [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ primeRank 2 A := by
  have hc : Nat.card A = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A))
  have hu := IsElementaryAbelian.primeRank_le_of_card_le A hc.le
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a.val }
  have hl := (primeRank_le_iff_elementary_card_le A).mp (le_refl (primeRank 2 A))
    (⊤ : Subgroup A) inferInstance
  rw [card_top, hc] at hl
  have he := le_antisymm hu ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hl)
  rw [hc, he]

private theorem card_subgroupOf_inf (A B : Subgroup G) :
    Nat.card (A.subgroupOf B) = Nat.card (A ⊓ B : Subgroup G) := by
  rw [← card_map_of_injective (K := A.subgroupOf B) B.subtype_injective, subgroupOf_map_subtype]

/-- The exact dimension identity, once the earlier hyperplane and center cuts
are given. No desired rank is included among its hypotheses. -/
theorem rank_identity_of_center_orders (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    (ρ : F.H →* MulAut F.Uhat) (hX : F.X g ≤ F.H)
    [IsElementaryAbelian 2 (dotImage F ρ (F.X g))]
    (hker : (ρ.comp (inclusion hX)).ker = (F.E g).subgroupOf (F.X g))
    (hindex : F.W.relIndex F.U = 2)
    (hcuts : Nat.card (F.E g ⊓ F.ZU : Subgroup G) =
      Nat.card (F.E g ⊓ conjugate F.ZU g : Subgroup G)) :
    primeRank 2 (hatImage F (F.E g)) + primeRank 2 (XdotCenterQuotient F ρ g) =
      primeRank 2 F.Uhat - 1 := by
  let E := F.E g
  let Z := F.ZU
  let Zg := conjugate F.ZU g
  have hEU : E ≤ F.U := inf_le_left.trans inf_le_left
  have hEcard := (hatMap F E hEU).ker.index_mul_card
  rw [index_ker, MonoidHom.range_eq_top.mpr (hatMap_surjective F E hEU),
    card_top, hatMap_ker, card_subgroupOf_inf, inf_comm F.ZU E] at hEcard
  have hQcard := card_centerQuotient_mul_card F ρ g hX hker
  have hZUcard : Nat.card (center F.U) = Nat.card Z := by
    exact (card_map_of_injective (K := center F.U) F.U.subtype_injective).symm
  have hUcard := (center F.U).index_mul_card
  rw [index_eq_card, hZUcard] at hUcard
  have hWcard := (F.W.subgroupOf F.U).index_mul_card
  rw [show (F.W.subgroupOf F.U).index = F.W.relIndex F.U from rfl,
    hindex, Nat.card_congr (subgroupOfEquivOfLe (show F.W ≤ F.U from inf_le_left)).toEquiv] at hWcard
  have hXcard : Nat.card (F.X g) = Nat.card F.W :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hZgcard : Nat.card Zg = Nat.card Z :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcentral : Zg ≤ centralizer (E : Set G) := by
    have hE : E ≤ conjugate F.U g :=
      inf_le_right.trans (map_mono (show F.W ≤ F.U from inf_le_left))
    have hZcentral : F.ZU ≤ centralizer (F.U : Set G) := by
      rintro z ⟨u,hu,rfl⟩ a ha
      exact congrArg Subtype.val (mem_center_iff.mp hu ⟨a,ha⟩)
    have hc : Zg ≤ centralizer (conjugate F.U g : Set G) :=
      (map_mono hZcentral).trans
        (map_centralizer_le_centralizer_image _ _)
    exact hc.trans (centralizer_le hE)
  have hproduct := card_mul_eq_card_inf_mul_card_sup_of_normalizes E Zg
    (hcentral.trans (centralizer_le_normalizer _))
  have hposZ : 0 < Nat.card Z := Nat.card_pos
  have hposI : 0 < Nat.card (E ⊓ Z : Subgroup G) := Nat.card_pos
  have hm : 2 * Nat.card (hatImage F E) * Nat.card (XdotCenterQuotient F ρ g) =
      Nat.card F.Uhat := by
    apply Nat.eq_of_mul_eq_mul_right hposZ
    apply Nat.eq_of_mul_eq_mul_right hposI
    calc
      _ = 2 * Nat.card (XdotCenterQuotient F ρ g) *
          (Nat.card (hatImage F E) * Nat.card (E ⊓ Z : Subgroup G)) * Nat.card Z := by ring
      _ = 2 * Nat.card (XdotCenterQuotient F ρ g) * (Nat.card E * Nat.card Zg) := by
        rw [hEcard, hZgcard]; ring
      _ = 2 * Nat.card (XdotCenterQuotient F ρ g) *
          (Nat.card (E ⊓ Zg : Subgroup G) * Nat.card (E ⊔ Zg : Subgroup G)) := by rw [hproduct]
      _ = 2 * (Nat.card (XdotCenterQuotient F ρ g) * Nat.card (E ⊔ Zg : Subgroup G)) *
          Nat.card (E ⊓ Zg : Subgroup G) := by ring
      _ = Nat.card F.U * Nat.card (E ⊓ Z : Subgroup G) := by
        rw [hQcard, hXcard, ← hWcard, ← hcuts]
      _ = _ := by rw [hUcard]
  let : IsElementaryAbelian 2 (hatImage F E) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 F.Uhat) a.val }
  rw [binary_card (hatImage F E), binary_card (XdotCenterQuotient F ρ g),
    binary_card F.Uhat, mul_assoc, ← pow_add, ← pow_succ'] at hm
  have he := Nat.pow_right_injective (by decide : 2 ≤ 2) hm
  change primeRank 2 (hatImage F E) + primeRank 2 (XdotCenterQuotient F ρ g) = primeRank 2 F.Uhat - 1
  exact Nat.eq_sub_of_add_eq he

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
