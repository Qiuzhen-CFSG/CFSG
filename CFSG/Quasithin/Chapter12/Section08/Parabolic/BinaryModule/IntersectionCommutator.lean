module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The commutator of the original intersection with I₂

The action of U on V₂ is nontrivial because |U:C_U(V₂)|=2. Its
commutator is therefore the whole point V₁. The original conjugator
moves that point to a different line of the four-group V₂, so the two
point commutators generate V₂. Both lie in [E,I₂]. Conversely, the two
U-generators centralize E modulo V₂; the commutator-preimage subgroup
extends this bound to all of I₂.

This proves the remaining equality [E,I₂]=V₂ of Aschbacher–Smith
12.8.9(2), printed p.853, from the actual preceding source inputs. No
quotient-module recognition is used.
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The nontrivial U-action on the marked plane has the whole point as
its commutator subgroup. -/
public theorem binary_point_commutator
    (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hindex : F.W.relIndex F.U = 2) :
    ⁅F.U, F.Vi 2⁆ = F.Vi 1 := by
  have hle : ⁅F.U, F.Vi 2⁆ ≤ F.Vi 1 :=
    (commutator_mono le_rfl ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))).trans hcomm
  have hne : ⁅F.U, F.Vi 2⁆ ≠ ⊥ := by
    intro he
    have hc : F.U ≤ centralizer (F.Vi 2 : Set G) := commutator_eq_bot_iff_le_centralizer.mp he
    have hUW : F.U ≤ F.W := le_inf le_rfl hc
    have hi : F.W.relIndex F.U = 1 := relIndex_eq_one.mpr hUW
    omega
  apply eq_of_le_of_card_ge hle
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  rw [hc]
  exact (⁅F.U, F.Vi 2⁆.one_lt_card_iff_ne_bot.mpr hne)

/-- The two original point lines fill the marked plane. -/
public theorem binary_plane_point_span
    (F : InvariantFlag T V n) [IsMulCommutative V] (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 := by
  have hgV := F.P_le_seed_normalizer L hL hgP
  have hgG := F.P_le_G₂ hn L hL hgP
  have hp : F.Vi 1 ≤ F.Vi 2 := F.monotone (by omega)
  have hpg : conjugate (F.Vi 1) g ≤ F.Vi 2 := conjugate_le_of_normalizes hp g hgG
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  have hcg : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hc]
  have hne : F.Vi 1 ≠ conjugate (F.Vi 1) g :=
    fun he => hgH ((conjugate_eq_iff _ _).mp he.symm)
  have hd : Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) :=
    disjoint_iff.mpr (inf_eq_bot_of_card_two_of_ne _ _ hc hcg hne)
  have hcentral : F.Vi 1 ≤ centralizer (conjugate (F.Vi 1) g : Set G) :=
    (F.le_seed 1).trans ((le_centralizer V).trans
      (centralizer_le (conjugate_le_of_normalizes (F.le_seed 1) g hgV)))
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcentral
  have hcs : Nat.card ↥(F.Vi 1 ⊔ conjugate (F.Vi 1) g) = 4 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hc, hcg]
  apply eq_of_le_of_card_ge (sup_le hp hpg)
  rw [F.card 2 hn, hcs]
  norm_num

/-- The actual E=W∩W^g has the source commutator [E,I₂]=V₂. -/
public theorem binary_intersection_commutator
    (F : InvariantFlag T V n) [IsMulCommutative V] (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hindex : F.W.relIndex F.U = 2) :
    ⁅F.E g, F.I₂ L⁆ = F.Vi 2 := by
  have hgV := F.P_le_seed_normalizer L hL hgP
  have hgG := F.P_le_G₂ hn L hL hgP
  have hpoint : F.Vi 1 ≤ F.Vi 2 := F.monotone (by omega)
  have hUI : F.U ≤ F.I₂ L := le_sup_left.trans hgen.le
  have hUgI : conjugate F.U g ≤ F.I₂ L := le_sup_right.trans hgen.le
  have hUG : F.U ≤ F.Gi 2 := F.U_le_G₂_of_commutator hcomm
  have hIG : F.I₂ L ≤ F.Gi 2 := by
    rw [← hgen]
    exact sup_le hUG (conjugate_le_of_normalizes hUG g ((F.Gi 2).le_normalizer hgG))
  have hUE : ⁅F.U, F.E g⁆ ≤ F.Vi 2 :=
    ((commutator_mono le_rfl (show F.E g ≤ F.U from inf_le_left.trans inf_le_left)).trans
      hcomm).trans hpoint
  have hconj : ⁅conjugate F.U g, conjugate F.U g⁆ ≤ conjugate (F.Vi 1) g := by
    simpa only [conjugate, map_commutator] using
      (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcomm)
  have hUgE : ⁅conjugate F.U g, F.E g⁆ ≤ F.Vi 2 :=
    ((commutator_mono le_rfl (show F.E g ≤ conjugate F.U g from
      inf_le_right.trans (map_mono (show F.W ≤ F.U from inf_le_left)))).trans hconj).trans
        (conjugate_le_of_normalizes hpoint g hgG)
  have hpre : F.I₂ L ≤ commutatorPreimage (F.I₂ L) (F.E g) (F.Vi 2) := by
    nth_rw 1 [← hgen]
    exact sup_le (le_commutatorPreimage hUI hUE) (le_commutatorPreimage hUgI hUgE)
  apply le_antisymm
  · rw [commutator_comm]
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le (F.I₂ L) (F.E g) (F.Vi 2) hIG)
  · have hV2E : F.Vi 2 ≤ F.E g :=
      (F.le_seed 2).trans (F.seed_le_E_of_normalizes g hgV)
    have hc := F.binary_point_commutator (by omega) hcomm hindex
    have hV2g : conjugate (F.Vi 2) g = F.Vi 2 := (conjugate_eq_iff _ _).mpr hgG
    have hcg : ⁅conjugate F.U g, F.Vi 2⁆ = conjugate (F.Vi 1) g := by
      calc
        ⁅conjugate F.U g, F.Vi 2⁆ = ⁅conjugate F.U g, conjugate (F.Vi 2) g⁆ := by rw [hV2g]
        _ = conjugate ⁅F.U, F.Vi 2⁆ g := (map_commutator _ _ _).symm
        _ = conjugate (F.Vi 1) g := by rw [hc]
    rw [← F.binary_plane_point_span hn L hL g hgP hgH]
    apply sup_le
    · rw [← hc, commutator_comm]
      exact commutator_mono hV2E hUI
    · rw [← hcg, commutator_comm]
      exact commutator_mono hV2E hUgI

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
