module

public import CFSG.Quasithin.Chapter12.Section08.RankTwo
public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Irreducibility deductions in Section 12.8

For the actual flag, the point lies in Z(U). Irreducibility of the natural
L₁-module V/V₁ then gives V ∩ Z(U) = V₁ whenever U is nonabelian.
The same irreducibility shows V = ⟨V₂^{L₁}⟩ by comparing the orders four
and two. Taking H-conjugate spans proves U = ⟨V₂^H⟩.

Irreducibility is stated as the invariant-subgroup criterion for the
literal section V/V₁. It is an explicit earlier natural-module input,
not a conclusion of the almost-extraspecial analysis. No self-centralizing
assumption on U is used. The two-core, Frattini, form and chief-series
assertions of 12.8.4–8 remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.8(3,6), printed pp.851–852.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08
variable {G : Type*} [Group G]

/-- The embedded intrinsic center is the relative ambient centralizer. -/
public theorem centerIn_eq_inf_centralizer (A : Subgroup G) :
    centerIn A = A ⊓ centralizer (A : Set G) := by
  apply le_antisymm
  · exact le_inf (map_subtype_le _) (centerIn_le_centralizer A)
  · intro a ha
    refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (ha.2 b b.property)

namespace InvariantFlag
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

public theorem H_normalizes_ZU (F : InvariantFlag T V n) :
    F.H ≤ normalizer (F.ZU : Set G) :=
  (le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_characteristic_image F.U (center F.U))

/-- The point is central in the actual conjugate span. -/
public theorem point_le_ZU (F : InvariantFlag T V n) [IsMulCommutative V]
    (hn : 1 ≤ n) : F.Vi 1 ≤ F.ZU := by
  rw [ZU, centerIn_eq_inf_centralizer]
  refine le_inf ((F.le_seed 1).trans (le_conjugateSpanBy V F.H)) ?_
  apply le_centralizer_iff.mp
  exact F.U_le_H.trans (normalizer_le_centralizer_of_card_two _ (by
    simpa using F.card 1 hn))

/-- Source 12.8.8(3), using the earlier natural-module irreducibility criterion. -/
public theorem seed_inf_center_eq_point (F : InvariantFlag T V n)
    [IsMulCommutative V] (L : Subgroup G) (hn : 1 ≤ n)
    (hLV : L ≤ normalizer (V : Set G))
    (hirr : ∀ A : Subgroup G, F.Vi 1 ≤ A → A ≤ V →
      F.Li L 1 ≤ normalizer (A : Set G) → A = F.Vi 1 ∨ A = V)
    (hnonab : ¬ IsMulCommutative F.U) : V ⊓ F.ZU = F.Vi 1 := by
  have hL1H : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hinv : F.Li L 1 ≤ normalizer (V ⊓ F.ZU : Set G) :=
    (le_inf ((F.Li_le L 1).trans (inf_le_left.trans hLV))
      (hL1H.trans F.H_normalizes_ZU)).trans inf_normalizer_le_normalizer_inf
  rcases hirr (V ⊓ F.ZU) (le_inf (F.le_seed 1) (F.point_le_ZU hn)) inf_le_left hinv with h | h
  · exact h
  · exfalso
    apply hnonab
    apply le_centralizer_iff_isMulCommutative.mp
    have hVZ : V ≤ F.ZU := h.symm.le.trans inf_le_right
    exact (conjugateSpanBy_le hVZ F.H_normalizes_ZU).trans (centerIn_le_centralizer F.U)

/-- A plane strictly contains the point, so its L₁-span is all of V. -/
public theorem seed_eq_plane_span [Finite G] (F : InvariantFlag T V n)
    (L : Subgroup G) (hn : 2 ≤ n) (hLV : L ≤ normalizer (V : Set G))
    (hirr : ∀ A : Subgroup G, F.Vi 1 ≤ A → A ≤ V →
      F.Li L 1 ≤ normalizer (A : Set G) → A = F.Vi 1 ∨ A = V) :
    conjugateSpanBy (F.Vi 2) (F.Li L 1) = V := by
  have hC : conjugateSpanBy (F.Vi 2) (F.Li L 1) ≤ V :=
    conjugateSpanBy_le (F.le_seed 2) ((F.Li_le L 1).trans (inf_le_left.trans hLV))
  rcases hirr _ ((F.monotone (by omega : 1 ≤ 2)).trans (le_conjugateSpanBy _ _))
    hC (le_normalizer_conjugateSpanBy _ _) with h | h
  · have hle : F.Vi 2 ≤ F.Vi 1 := h ▸ le_conjugateSpanBy (F.Vi 2) (F.Li L 1)
    have hc := card_le_of_le hle
    rw [F.card 2 hn, F.card 1 (by omega)] at hc
    norm_num at hc
  · exact h

/-- Source 12.8.8(6). The conjugate-span calculation needs no nonabelian premise. -/
public theorem U_eq_plane_span [Finite G] (F : InvariantFlag T V n)
    (L : Subgroup G) (hn : 2 ≤ n) (hLV : L ≤ normalizer (V : Set G))
    (hirr : ∀ A : Subgroup G, F.Vi 1 ≤ A → A ≤ V →
      F.Li L 1 ≤ normalizer (A : Set G) → A = F.Vi 1 ∨ A = V) :
    F.U = conjugateSpanBy (F.Vi 2) F.H := by
  apply le_antisymm
  · apply conjugateSpanBy_le
    · exact (F.seed_eq_plane_span L hn hLV hirr).symm.le.trans
        (conjugateSpanBy_mono le_rfl ((F.Li_le L 1).trans inf_le_right))
    · exact le_normalizer_conjugateSpanBy _ _
  · exact conjugateSpanBy_mono (F.le_seed 2) le_rfl

end InvariantFlag
end CFSG.Quasithin.Chapter12.Section08
