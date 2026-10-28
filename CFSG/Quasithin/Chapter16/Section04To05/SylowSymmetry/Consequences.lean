module
public import CFSG.Quasithin.Chapter16.Section04To05.Fusion

/-!
# Consequences of the Sylow upgrade

Once `R` is Sylow in `K′`, the transport containment from 16.4.2(4)
identifies it with the conjugate of `T_C`. Thus `|R|=|T_C|`. The earlier
isomorphism `R ≃ C_TC(R)` forces `C_TC(R)=T_C`; tight embedding then puts
`T_C` in `H′`. These are clauses (1) and (3) of 16.4.11 with the substantive
Sylow upgrade retained explicitly. Reverse Δ₀ membership is separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 16.4.2 and 16.4.10–11, printed pp.1183 and 1192–1194.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Even order in the overgroup makes a relative Sylow nontrivial. -/
theorem SylowIn.ne_bot_of_even {R H : Subgroup G}
    (h : SylowIn R H) (he : Even (Nat.card H)) : R ≠ ⊥ := by
  obtain ⟨P, rfl⟩ := h
  have hd := P.dvd_card_of_dvd_card (even_iff_two_dvd.mp he)
  intro hh
  have hc : Nat.card P = 1 := by
    rw [← card_map_of_injective H.subtype_injective, hh, card_bot]
  rw [hc] at hd
  norm_num at hd

namespace SylowSymmetry

/-- Clauses (1) and (3) of 16.4.11, after the Sylow upgrade 16.4.10.
The isomorphism with the smaller centralizer is exactly 16.4.2(1), and
transport containment is exactly 16.4.2(4). -/
theorem centralizing_and_transport {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) :
    (commutingSylow T L ⊓ centralizer (R : Set G) = commutingSylow T L) ∧
    Nonempty (commutingSylow T L ≃* R) ∧
    commutingSylow T L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ∧
    R = (commutingSylow T L).conjBy g := by
  have heq := h.eq_conjugate_commutingSylow hR htransport
  have hc : Nat.card R = Nat.card (commutingSylow T L) := by
    rw [heq]
    exact card_map_of_injective (MulAut.conj g).injective
  have hS : commutingSylow T L ⊓ centralizer (R : Set G) = commutingSylow T L :=
    eq_of_le_of_card_ge inf_le_left (by rw [← hc]; exact (Nat.card_congr e.toEquiv).le)
  have hcent : commutingSylow T L ≤ centralizer (R : Set G) :=
    hS ▸ inf_le_right
  have hn : R ≠ ⊥ := h.sylow.ne_bot_of_even h.mem_delta.2.2
  refine ⟨hS, ?_, ?_, heq⟩
  · exact ⟨(MulEquiv.subgroupCongr hS).symm.trans e.symm⟩
  · exact hcent.trans ((centralizer_le_normalizer _).trans
      (h.normalizer_le hn le_rfl))

end SylowSymmetry
end CFSG.Quasithin.Chapter16.Intersections
