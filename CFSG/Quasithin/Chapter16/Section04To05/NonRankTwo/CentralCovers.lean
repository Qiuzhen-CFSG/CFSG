module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.CentralCovers.Basic

/-!
# The common contradiction for two-central sporadic projections

The local covering data force u into Z(T). Tight embedding then puts the chosen
conjugator g in N_G(T); the earlier conjugacy R = T_C^g and faithfulness on L
show that g moves z. Its induced action on Ω₁(Z(T)) has odd order because the
Sylow subgroup acts trivially. The quotient calculation need give only the
upper bound four: the distinct central involutions z and u give equality.

A characteristic Rudvalis subgroup of order two contradicts this moving odd
action. In the other cases the square predicate is constant on all three
nonidentity elements, contradicting the unique square in {u,uz}. This avoids
the printed proof's unsupported identification of the square with u.

These are conditional group-theoretic deductions. The covering restrictions,
quotient action and intrinsic covering data must still be supplied before
asserting exclusion of two-central projections in arbitrary marked Δ₀ setups.
No numbered source theorem is claimed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 16.5.11, printed p.1199.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.CentralCovers

open Subgroup

variable {G : Type*} [Group G]

/-- The distinguished square cannot coexist with an odd moving action on the
actual central four-group. In particular it need not generate <u>. -/
theorem uniqueSquareCoset_obstruction [Finite G]
    (E Q : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (g : G) (hgE : g ∈ normalizer (E : Set G))
    (hgQ : g ∈ normalizer (Q : Set G))
    (hodd : Odd (orderOf (E.normalizerMonoidHom ⟨g, hgE⟩)))
    (z u : E) (hmove : MulAut.conj g (z : G) ≠ z)
    (hz : z ≠ 1) (hu : u ≠ 1) (huz : u * z ≠ 1)
    (hsq : UniqueSquareCoset Q (u : G) (z : G)) : False := by
  have hi := Theory.GroupAction.square_root_iff_of_odd_four_action E Q hE g hgE hgQ
    hodd z hmove u (u * z) hu huz
  obtain ⟨w, ⟨hw, hs⟩, huniq⟩ := hsq
  have hune : (u : G) ≠ (u : G) * z := by
    intro he
    have hz1 : (z : G) = 1 := mul_left_cancel (a := (u : G)) (by simpa using he.symm)
    exact hz (Subtype.ext hz1)
  rcases hw with rfl | rfl
  · exact hune (huniq ((u : G) * z) ⟨Or.inr rfl, hi.mp hs⟩).symm
  · exact hune (huniq (u : G) ⟨Or.inl rfl, hi.mpr hs⟩)

variable [Finite G] {T : Sylow 2 G} {z g u : G} {L R : Subgroup G}

/-- A nonidentity central element of R triggers 16.5.2(1). The conjugacy
R = T_C^g and faithfulness then force the induced action to move z. -/
theorem normalizes_sylow_and_moves
    (h : IntersectionSetup T z L g R)
    (hu : u ∈ R) (hu2 : orderOf u = 2)
    (huC : u ∈ centralizer (T : Set G))
    (hfaithful : Disjoint R (centralizer (L : Set G)))
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) :
    g ∈ normalizer (T : Set G) ∧ MulAut.conj g z ≠ z := by
  have hu1 : u ≠ 1 := by intro he; simp [he] at hu2
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hne : R ⊓ centralizer (T : Set G) ≠ ⊥ := by
    intro he
    have humem : u ∈ R ⊓ centralizer (T : Set G) := ⟨hu, huC⟩
    rw [he, mem_bot] at humem
    exact hu1 humem
  refine ⟨h.conjugator_normalizes_sylow hne htransport, ?_⟩
  have hzK : z ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  have hzTC : z ∈ commutingSylow T L := ⟨h.mem_sylow, hzK⟩
  have hgR : MulAut.conj g z ∈ R := by
    rw [h.eq_conjugate_commutingSylow hR htransport]
    exact mem_map_of_mem _ hzTC
  intro he
  rw [he] at hgR
  exact hz1 (Subgroup.disjoint_def.mp hfaithful hgR hzK)

/-- The quotient calculation need supply only an upper bound: the two
specified distinct involutions already generate a four-group in Ω₁(Z(T)). -/
theorem omegaCenter_eq_plane_of_card_le
    (h : IntersectionSetup T z L g R)
    (hu : u ∈ R) (hu2 : orderOf u = 2)
    (huC : u ∈ centralizer (T : Set G))
    (hfaithful : Disjoint R (centralizer (L : Set G)))
    (hbound : Nat.card (sylowOmegaCenter T) ≤ 4) :
    sylowOmegaCenter T = zpowers z ⊔ zpowers u ∧
      Nat.card (sylowOmegaCenter T) = 4 := by
  have hzK : z ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  have hzC : z ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes ht)
  have hzE : z ∈ sylowOmegaCenter T := mem_sylowOmegaCenter T h.mem_sylow
    (by simpa only [h.involution] using pow_orderOf_eq_one z) hzC
  have huE : u ∈ sylowOmegaCenter T := mem_sylowOmegaCenter T (h.le_sylow hu)
    (by simpa only [hu2] using pow_orderOf_eq_one u) huC
  have hzu : z ≠ u := by
    intro he
    have hu1 := Subgroup.disjoint_def.mp hfaithful hu (he ▸ hzK)
    simp [hu1] at hu2
  have hcomm : Commute z u :=
    (show Commute u z from mem_centralizer_iff.mp hzC u (h.le_sylow hu)).symm
  have hklein := isKleinFour_closure_pair_of_orderOf z u h.involution hu2 hzu hcomm
  have hclosure : closure ({z, u} : Set G) = zpowers z ⊔ zpowers u := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have hplane : zpowers z ⊔ zpowers u ≤ sylowOmegaCenter T :=
    sup_le (zpowers_le.mpr hzE) (zpowers_le.mpr huE)
  have hcard : Nat.card (zpowers z ⊔ zpowers u : Subgroup G) = 4 :=
    hclosure ▸ hklein.card_four
  have heq := eq_of_le_of_card_ge hplane (by rw [hcard]; exact hbound)
  exact ⟨heq.symm, heq ▸ hcard⟩

/-- Final contradiction from the local covering calculations. The hypotheses
about the central four-group and the covering data remain obligations of the
source assembly; this theorem does not assert the central-projection exclusion. -/
theorem central_cover_obstruction
    (h : IntersectionSetup T z L g R)
    (X : Subgroup G) (hu : u ∈ R) (hu2 : orderOf u = 2)
    (huC : u ∈ centralizer (T : Set G))
    (hfaithful : Disjoint R (centralizer (L : Set G)))
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hgX : g ∈ normalizer (X : Set G))
    (hfour : Nat.card (sylowOmegaCenter T) = 4)
    (hcover : UniqueSquareCoset ((pCore 2 X).map X.subtype) u z ∨
      (Nat.card (rudvalisY X) = 2 ∧
        (rudvalisY X).map X.subtype ≤ sylowOmegaCenter T)) : False := by
  obtain ⟨hgT, hmove⟩ := normalizes_sylow_and_moves h hu hu2 huC hfaithful hR htransport
  have hzK : z ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  have hzC : z ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes ht)
  have hzE : z ∈ sylowOmegaCenter T := mem_sylowOmegaCenter T h.mem_sylow
    (by simpa only [h.involution] using pow_orderOf_eq_one z) hzC
  have huE : u ∈ sylowOmegaCenter T := mem_sylowOmegaCenter T (h.le_sylow hu)
    (by simpa only [hu2] using pow_orderOf_eq_one u) huC
  have hgE := normalizer_sylow_le_normalizer_omegaCenter T hgT
  have hodd := Theory.GroupAction.normalizer_action_order_odd T (sylowOmegaCenter T)
    (normalizer_sylow_le_normalizer_omegaCenter T) (sylow_centralizes_omegaCenter T) ⟨g, hgT⟩
  rcases hcover with hsq | ⟨hY, hYE⟩
  · apply uniqueSquareCoset_obstruction (sylowOmegaCenter T) _ hfour g hgE
      (normalizer_le_normalizer_twoCore X hgX) hodd
      ⟨z, hzE⟩ ⟨u, huE⟩ hmove
    · intro he
      have he' : z = 1 := congrArg Subtype.val he
      simpa [he'] using h.involution
    · intro he
      have he' : u = 1 := congrArg Subtype.val he
      simp [he'] at hu2
    · intro he
      have he' : u * z = 1 := congrArg Subtype.val he
      have huK : u ∈ centralizer (L : Set G) := by
        rw [eq_inv_of_mul_eq_one_left he']
        exact inv_mem hzK
      have hu1 := Subgroup.disjoint_def.mp hfaithful hu huK
      simp [hu1] at hu2
    · exact hsq
  · exact Theory.GroupAction.no_characteristic_two_in_four_of_odd_action
      (sylowOmegaCenter T) X hfour (rudvalisY X) hY hYE g hgE hgX hodd ⟨z, hzE⟩ hmove

/-- Assembly of the common argument from local covering data and the
quotient-action calculation. Neither centrality of u, normalization of X by T,
order four of Ω₁(Z(T)), nor oddness of g is an input. -/
theorem central_cover_obstruction_of_local_data
    (h : IntersectionSetup T z L g R)
    (hu : u ∈ R) (hu2 : orderOf u = 2)
    (hfaithful : Disjoint R (centralizer (L : Set G)))
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hgX : g ∈ normalizer (involutionResidual L u : Set G))
    (hbound : Nat.card (sylowOmegaCenter T) ≤ 4)
    (hcoset : ∀ t ∈ T, MulAut.conj t u = u ∨ MulAut.conj t u = u * z)
    (hdata : LocalCoverData (involutionResidual L u) u z) : False := by
  have hzK : z ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  have hzC : z ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes ht)
  have hTX := normalizes_involutionResidual (T : Subgroup G) L u z
    h.sylow_normalizes hzK hcoset
  have huC := centralizes_of_localCoverData (T : Subgroup G) (involutionResidual L u)
    u z hTX (by simpa only [pow_two, h.involution] using pow_orderOf_eq_one z) hzC hcoset hdata
  obtain ⟨hE, hfour⟩ := omegaCenter_eq_plane_of_card_le h hu hu2 huC hfaithful hbound
  apply central_cover_obstruction h (involutionResidual L u) hu hu2 huC hfaithful
    hR htransport hgX hfour
  rcases hdata with hsquare | ⟨hY, hspan⟩
  · exact Or.inl hsquare
  · refine Or.inr ⟨hY, ?_⟩
    rw [hE, ← hspan]
    exact le_sup_right

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.CentralCovers
