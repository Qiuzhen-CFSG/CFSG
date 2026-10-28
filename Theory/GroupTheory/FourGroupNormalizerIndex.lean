module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

/-!
# Four-group normalizer indices

Two disjoint conjugate hyperplanes force their nontrivial original subgroup
to have order two. For a subgroup N normalizing a four-group E, the orbit
of a nonidentity z in E bounds |N:C_N(z)| by three. If N contains an ambient
Sylow two-subgroup fixing z and moves z, this index is exactly three.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 12.4.6, printed p.814. The ambient Sylow hypothesis is essential to
exclude index two; no full automorphism-group identification is required.
-/

public section
open Subgroup
namespace Subgroup
set_option linter.style.haveILetI false

/-- Disjoint conjugate hyperplanes force a line in a four-group. -/
theorem card_eq_two_of_disjoint_conjugate_hyperplane {G : Type*} [Group G] [Finite G]
    (Z E : Subgroup G) (hZE : Z ≤ E) (hZ : Z ≠ ⊥)
    (hi : Z.relIndex E = 2) (g : G) (hg : g ∈ normalizer (E : Set G))
    (hd : Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥) :
    Nat.card Z = 2 ∧ Nat.card E = 4 := by
  have he : E.map (MulAut.conj g).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.mp hg
  have hi' : (Z.map (MulAut.conj g).toMonoidHom).relIndex E = 2 := by
    rw [← he, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hi]
  have hb := relIndex_inf_le (H := Z) (K := Z.map (MulAut.conj g).toMonoidHom) (L := E)
  rw [hd, relIndex_bot_left, hi, hi'] at hb
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) Z E bot_le hZE
  rw [relIndex_bot_left, relIndex_bot_left, hi] at hc
  have hlo : 1 < Nat.card Z := by
    by_contra hn
    have hh : Subsingleton Z := Finite.card_le_one_iff_subsingleton.mp (by omega)
    apply hZ
    apply _root_.eq_bot_iff.mpr
    intro z hz
    exact congrArg Subtype.val (@Subsingleton.elim Z hh ⟨z,hz⟩ 1)
  omega

/-- Conjugation embeds the orbit of z into the nonidentity elements of E. -/
theorem centralizer_relIndex_le_card_sub_one {G : Type*} [Group G] [Finite G]
    (N E : Subgroup G) (hNE : N ≤ normalizer (E : Set G))
    (z : G) (hz : z ∈ E) (hz1 : z ≠ 1) :
    (centralizer ({z} : Set G)).relIndex N ≤ Nat.card E - 1 := by
  classical
  let f : N →* MulAut E := E.normalizerMonoidHom.comp (inclusion hNE)
  letI : MulDistribMulAction N E := MulDistribMulAction.compHom E f
  let z' : E := ⟨z,hz⟩
  have hs : MulAction.stabilizer N z' = (centralizer ({z} : Set G)).subgroupOf N := by
    ext n
    change (f n z' = z') ↔ (n : G) ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hn
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hn)
    · intro hn
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr hn
  have ho : Nat.card (MulAction.orbit N z') ≤ Nat.card {e : E // e ≠ 1} := by
    let j : MulAction.orbit N z' → {e : E // e ≠ 1} := fun w => ⟨w.val, by
      intro hw
      obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp w.property
      have he : f n z' = 1 := hn.trans hw
      have he' := (f n).injective (he.trans (map_one _).symm)
      exact hz1 (congrArg Subtype.val he')⟩
    apply Nat.card_le_card_of_injective j
    intro a b he
    apply Subtype.ext
    exact congrArg (fun x : {e : E // e ≠ 1} => x.val) he
  have hcard : Nat.card {e : E // e ≠ 1} = Nat.card E - 1 := by
    letI : Fintype E := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  rw [relIndex, ← hs, MulAction.index_stabilizer]
  simpa only [Nat.card_coe_set_eq, hcard] using ho

/-- The moving orbit has size three because its stabilizer has odd index. -/
theorem centralizer_relIndex_eq_three_of_four {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (N E : Subgroup G) (hTN : (T : Subgroup G) ≤ N)
    (hNE : N ≤ normalizer (E : Set G)) (hfour : Nat.card E = 4)
    (z : G) (hz : z ∈ E) (hz1 : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hN : ¬ N ≤ centralizer ({z} : Set G)) :
    (N ⊓ centralizer ({z} : Set G)).relIndex N = 3 := by
  rw [inf_relIndex_left]
  have hb := centralizer_relIndex_le_card_sub_one N E hNE z hz hz1
  rw [hfour] at hb
  have hi : ¬ 2 ∣ (T : Subgroup G).relIndex N := (T.subtype hTN).not_dvd_index
  have hc : ¬ 2 ∣ (centralizer ({z} : Set G)).relIndex N :=
    fun h => hi (h.trans (relIndex_dvd_of_le_left N hTz))
  have hn : (centralizer ({z} : Set G)).relIndex N ≠ 1 :=
    fun he => hN (relIndex_eq_one.mp he)
  have hp : 0 < (centralizer ({z} : Set G)).relIndex N :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : (centralizer ({z} : Set G)).relIndex N ≠ 2 := by
    intro he
    apply hc
    rw [he]
  omega

end Subgroup
