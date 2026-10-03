module

public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.GroupAction.InvertedOddFrattiniFiltration

/-!
# The odd-action contradiction in Parrott's core fusion case

The centralizer C_G(z) has order 10240, hence contains no subgroup of order
three. If a two-subgroup S contains z and an inverted three-subgroup acts
on a characteristic index-two filtration of S, with its inverter trivial
on the middle layer modulo S′, the Frattini filtration theorem makes that
three-subgroup centralize S. This is impossible because it then fixes z.

This isolates the last step of the J−E fusion argument. The center and
omega calculations that construct the filtration and the inverted
three-subgroup are separate prerequisites.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.676, from “By Suzuki's lemma” to the contradiction Q ≤ C_G(z).
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The inverted three-subgroup at the end of the core fusion argument
cannot act on the stated filtration of a two-subgroup containing z. -/
public theorem parrott_no_inverted_three_filtration
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z)
    (S Q : Subgroup G) (hzS : z ∈ S) (hS : IsPGroup 2 S)
    (V : Subgroup S) [V.Characteristic] (hindex : V.index = 2)
    (hQ : Q ≤ normalizer (S : Set G)) (hQcard : Nat.card Q = 3)
    (w : normalizer (S : Set G))
    (hinverts : ∀ q ∈ Q, (w : G) * q * (w : G)⁻¹ = q⁻¹)
    (hdisplacement : ∀ v ∈ V,
      v⁻¹ * S.normalizerMonoidHom w v ∈ _root_.commutator S) : False := by
  have hodd : Odd (Nat.card Q) := hQcard ▸ (by decide : Odd 3)
  have hcentral := le_centralizer_of_inverted_odd_index_two_filtration
    S Q hS V hindex hQ hodd w hinverts hdisplacement
  have hQH : Q ≤ centralizer ({z} : Set G) := by
    intro q hq
    exact mem_centralizer_singleton_iff.mpr (hcentral hq z hzS).symm
  have hdiv := card_dvd_of_le hQH
  rw [hQcard, (h.card_and_solvable z).1] at hdiv
  norm_num at hdiv

end Stellmacher.Recognition
