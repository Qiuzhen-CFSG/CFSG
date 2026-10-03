module

public import Stellmacher.Recognition.Parrott.SylowSeedData

/-!
# Frames before the two cases in Parrott's Sylow construction

The marked elements z,t,v extend to compatible elementary bases of the actual
subgroups E and F. This follows by extending the order-eight omega center first
to E ∩ F (order sixteen), then to E (order thirty-two); the original involution
supplied with F completes its basis.

The two subsequent interfaces retain the actual subgroups while separating the
choice of an outer generator and its Jordan chain from the core generators
through (10). Neither interface asserts that those choices have been made.

Source: Parrott (1972), pp.674 and 678–679, equations (1)–(10).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

private theorem closure_three (r s t : G) :
    closure ({r, s, t} : Set G) = (zpowers r ⊔ zpowers s) ⊔ zpowers t := by
  rw [show ({r, s, t} : Set G) = ({r} ∪ {s}) ∪ {t} by
      ext
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto,
    Subgroup.closure_union, Subgroup.closure_union]
  simp only [← zpowers_eq_closure]

private theorem closure_append (s : Set G) (g : G) :
    closure (s ∪ {g}) = closure s ⊔ zpowers g := by
  rw [Subgroup.closure_union, ← zpowers_eq_closure]

private theorem extend_binary [Finite G] (A B : Subgroup G)
    [IsElementaryAbelian 2 B] (hAB : A ≤ B) (hA : 0 < Nat.card A)
    (hcard : Nat.card B = 2 * Nat.card A) :
    ∃ u : G, u ∈ B ∧ u ∉ A ∧ A ⊔ zpowers u = B := by
  have hne : A ≠ B := by
    intro heq
    have hc : Nat.card A = Nat.card B := by rw [heq]
    omega
  obtain ⟨u, huB, huA⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hAB hne)
  refine ⟨u, huB, huA, eq_of_le_of_card_ge (sup_le hAB (zpowers_le.mpr huB)) ?_⟩
  have huN : u ∈ normalizer (A : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    intro a ha
    exact setLike_mul_comm (s := B) (hAB ha) huB
  rw [card_sup_zpowers_of_normalizing_involution A u
    (elemPow_eq_one_of_isElementaryAbelian u huB) huA huN, hcard]

/-- Complete the prescribed z,t,v to bases of E ∩ F, E, and F simultaneously.
This does not impose an action on the new basis vectors. -/
public theorem ParrottNormalizerFusionData.exists_elementary_bases [Finite G]
    (n : ParrottNormalizerFusionData e) (h : ParrottCentralizerHypotheses z) :
    ∃ u w : G,
      closure ({z, n.t, n.v, u} : Set G) = E ⊓ e.F ∧
      closure ({z, n.t, n.v, u, w} : Set G) = E ∧
      closure ({z, n.t, n.v, u, (e.a : G)} : Set G) = e.F := by
  let Z := ((zpowers z ⊔ zpowers n.t) ⊔ zpowers n.v : Subgroup G)
  have hZE : Z ≤ E ⊓ e.F := by
    dsimp only [Z]
    rw [← n.omega_center_eq]
    exact n.omega_center_le_inf
  have hZcard : Nat.card Z = 8 := by
    dsimp only [Z]
    rw [← n.omega_center_eq]
    exact n.ambient_omega_center_card
  obtain ⟨_, _, _, _, _, hElem, hcard, _⟩ := parrott_centralizer_structure z h
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (commutator (pCore 2 H)) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map ((H).subtype.comp (pCore 2 H).subtype)
  let : IsElementaryAbelian 2 e.F := e.elementary
  let : IsElementaryAbelian 2 (E ⊓ e.F : Subgroup G) :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
        (setLike_mul_comm (s := e.F) a.property.2 b.property.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a =>
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) a.property.2) }
  obtain ⟨u, _, _, hZu⟩ := extend_binary Z (E ⊓ e.F) hZE
    (by rw [hZcard]; decide) (by rw [e.inf_card, hZcard])
  have hEcard : Nat.card E = 32 := by
    rw [card_map_of_injective (K := commutator (pCore 2 H))
      (f := (H).subtype.comp (pCore 2 H).subtype)
      ((H).subtype_injective.comp (pCore 2 H).subtype_injective)]
    exact hcard
  obtain ⟨w, _, _, hUw⟩ := extend_binary (E ⊓ e.F) E inf_le_left
    (by rw [e.inf_card]; decide) (by rw [hEcard, e.inf_card])
  have hU : closure ({z, n.t, n.v, u} : Set G) = E ⊓ e.F := by
    rw [show ({z, n.t, n.v, u} : Set G) = {z, n.t, n.v} ∪ {u} by
      ext
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto, closure_append, closure_three]
    exact hZu
  refine ⟨u, w, hU, ?_, ?_⟩
  · rw [show ({z, n.t, n.v, u, w} : Set G) = {z, n.t, n.v, u} ∪ {w} by
      ext
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto, closure_append, hU, hUw]
  · rw [show ({z, n.t, n.v, u, (e.a : G)} : Set G) =
      {z, n.t, n.v, u} ∪ {(e.a : G)} by
      ext
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto,
      closure_append, hU, e.inf_eq, sup_comm]
    exact e.fixed_join.symm

/-- A basis with the outer action (1), before choosing the core generators.
The supplied t,v,F,T are unchanged. -/
public structure ParrottSylowActionData (n : ParrottNormalizerFusionData e) where
  u : G
  w : G
  x : G
  inf_basis : closure ({z, n.t, n.v, u} : Set G) = E ⊓ e.F
  derived_basis : closure ({z, n.t, n.v, u, w} : Set G) = E
  sylow_eq : (e.sylow : Subgroup G) = zpowers x ⊔ J
  eq01_x : x ^ 4 = 1
  eq01_xt : Tits.parrottCommutator x n.t = 1
  eq01_xv : Tits.parrottCommutator x n.v = n.t
  eq01_xu : Tits.parrottCommutator x u = n.v
  eq01_xw : Tits.parrottCommutator x w = u

/-- Core generators through (10), before the two alternatives (11)–(15).
Elementary and centrality relations are consequences of the actual subgroup
memberships and are supplied by the assembly theorem. -/
public structure ParrottSylowInitialData (n : ParrottNormalizerFusionData e)
    extends ParrottSylowActionData n where
  a : G
  b : G
  c : G
  d : G
  elementary_basis : closure ({z, n.t, n.v, u, a} : Set G) = e.F
  core_generators : closure ({a, b, c, d} : Set G) = J
  comm_bt : Commute b n.t
  d_sq : d ^ 2 = 1
  eq02_bw : Tits.parrottCommutator b w = 1
  eq02_aw : Tits.parrottCommutator a w = z
  eq02_bu : Tits.parrottCommutator b u = z
  eq03_db : Tits.parrottCommutator d b = n.v
  eq03_dt : Tits.parrottCommutator d n.t = z
  eq03_b : b ^ 2 = n.v
  eq05_ab : Tits.parrottCommutator a b = n.t
  eq07_dw : Tits.parrottCommutator d w = 1
  eq08_du : Tits.parrottCommutator d u = 1
  eq09_cu : Tits.parrottCommutator c u = 1
  eq09_cw : Tits.parrottCommutator c w = 1
  eq10_ct : Tits.parrottCommutator c n.t = 1
  eq10_cv : Tits.parrottCommutator c n.v = z
  ax_alternative : Tits.parrottCommutator a x = 1 ∨ Tits.parrottCommutator a x = n.t

namespace ParrottSylowInitialData

variable {n : ParrottNormalizerFusionData e}

/-- The five equations left after the initial frame; the Boolean records the
printed Case 2. This is a contract for the remaining choices, not an existence
assumption in the intended final theorem. -/
public structure CoreRelations (f : ParrottSylowInitialData n) (caseTwo : Bool) : Prop where
  eq11_ad : Tits.parrottCommutator f.a f.d = if caseTwo then f.u * n.v else f.u
  eq12_ac : Tits.parrottCommutator f.a f.c = if caseTwo then n.v else n.v * n.t
  eq13 : f.c ^ 2 = if caseTwo then f.w else f.w * f.u
  eq14_cd : Tits.parrottCommutator f.c f.d = if caseTwo then f.w else f.w * f.u
  eq15_bc : Tits.parrottCommutator f.b f.c = if caseTwo then f.u * n.t else f.u * n.v

end ParrottSylowInitialData

end Stellmacher.Recognition
