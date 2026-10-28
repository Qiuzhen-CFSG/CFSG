module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Incidence

/-!
# Uniqueness of the source line and the collinearity degree

Two lines through W sharing another source point have Sylow groups whose
intersection is larger than D. Since D has index three in either Sylow
group, those Sylow groups coincide. Their unique largest abelian subgroup
then identifies the two lines. Thus the four lines through W contribute
disjoint sets of nine other points, and its collinearity degree is 36.

This proves the incidence and counting assertions without assuming the
separate identification of collinearity with commutation.
Source: Aschbacher, *Sporadic Groups* (1994), 45.10(4)–(5), pp.247–248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

/-- A line through W and a second point of V is V itself. -/
theorem line_eq_base_of_second_point {U L : Subgroup G}
    (hU : U ∈ c.pointsOn c.V) (hne : U ≠ c.W)
    (hL : L ∈ c.linesThrough c.W) (hUL : U ≤ L) : L = c.V := by
  obtain ⟨k, hk, rfl⟩ := c.linesThrough_base ▸ hL
  let Q' := c.Q.conjBy k
  let I := c.Q ⊓ Q'
  have hDk : c.D.conjBy k = c.D := mem_normalizer_iff_map_conj_eq.mp
    (CubicLine.normalizer_normalizes_oddKernel c.W hk)
  have hDI : c.D ≤ I := by
    refine le_inf le_sup_right ?_
    have hh := map_mono (f := (MulAut.conj k).toMonoidHom)
      (show c.D ≤ c.Q from le_sup_right)
    change c.D.conjBy k ≤ Q' at hh
    rwa [hDk] at hh
  have hUI : U ≤ I := le_inf (hU.2.trans le_sup_left)
    (hUL.trans (map_mono (show c.V ≤ c.Q from le_sup_left)))
  have hi : c.D.relIndex c.Q = 3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) c.D c.Q bot_le le_sup_right
    simp only [relIndex_bot_left, c.odd_card, c.sylow_card] at hh
    omega
  have hm := relIndex_mul_relIndex c.D I c.Q hDI inf_le_left
  rw [hi] at hm
  have hn : c.D.relIndex I ≠ 1 := by
    intro he
    have hUD := hUI.trans (relIndex_eq_one.mp he)
    exact hne ((c.kernelLines_le_odd_iff (c.pointsOn_base ▸ hU)).mp hUD)
  have hIQ : I.relIndex c.Q = 1 := by
    have hd : c.D.relIndex I ∣ 3 := ⟨I.relIndex c.Q, hm.symm⟩
    have he := ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hn
    rw [he] at hm
    omega
  have hQQ' : c.Q ≤ Q' := (relIndex_eq_one.mp hIQ).trans inf_le_right
  have heQ : c.Q = Q' := eq_of_le_of_card_ge hQQ' (by
    change Nat.card (c.Q.map (MulAut.conj k).toMonoidHom) ≤ Nat.card c.Q
    rw [card_map_of_injective (MulAut.conj k).injective])
  let : IsElementaryAbelian 3 c.V := c.kernel_elementary
  have hVk : c.V.conjBy k ≤ c.Q := by
    rw [heQ]
    exact map_mono (show c.V ≤ c.Q from le_sup_left)
  have hcomm : IsMulCommutative (c.V.conjBy k) := by
    change IsMulCommutative (c.V.map (MulAut.conj k).toMonoidHom)
    infer_instance
  exact (c.maximum (c.V.conjBy k) hcomm hVk).2 (by
    change 81 ≤ Nat.card (c.V.map (MulAut.conj k).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj k).injective, c.kernel_card])

/-- Distinct source points lie on at most one source line. -/
theorem line_unique {U U' L L' : Subgroup G}
    (hU : U ∈ c.points) (hU' : U' ∈ c.points)
    (hL : L ∈ c.lines) (hL' : L' ∈ c.lines) (hne : U' ≠ U)
    (hUL : U ≤ L) (hUL' : U ≤ L') (hU'L : U' ≤ L) (hU'L' : U' ≤ L') : L' = L := by
  obtain ⟨g, rfl, rfl⟩ := c.incident_pair_conjugate hU hL hUL
  have hb : U'.conjBy g⁻¹ ≤ c.V := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hU'L
    change U'.conjBy g⁻¹ ≤ (c.V.conjBy g).conjBy g⁻¹ at hh
    simpa only [conjBy_inv] using hh
  have hb' : c.W ≤ L'.conjBy g⁻¹ := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hUL'
    change (c.W.conjBy g).conjBy g⁻¹ ≤ L'.conjBy g⁻¹ at hh
    simpa only [conjBy_inv] using hh
  have hne' : U'.conjBy g⁻¹ ≠ c.W := by
    intro he
    apply hne
    have hh := congrArg (fun R : Subgroup G => R.conjBy g) he
    simpa only [conjBy_inv'] using hh
  have he := c.line_eq_base_of_second_point
    ⟨c.point_conjugate_mem hU' g⁻¹, hb⟩ hne'
    ⟨c.line_conjugate_mem hL' g⁻¹, hb'⟩
    (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hU'L')
  have hh := congrArg (fun R : Subgroup G => R.conjBy g) he
  simpa only [conjBy_inv'] using hh

/-- The neighboring source points, with adjacency defined by incidence. -/
def neighbors (U : Subgroup G) : Set (Subgroup G) :=
  {U' | U' ∈ c.points ∧ U' ≠ U ∧ ∃ L ∈ c.lines, U ≤ L ∧ U' ≤ L}

def otherPoints (U L : Subgroup G) : Set (Subgroup G) := c.pointsOn L \ {U}

theorem otherPoints_card {U L : Subgroup G}
    (hU : U ∈ c.points) (hL : L ∈ c.lines) (hUL : U ≤ L) :
    Nat.card (c.otherPoints U L) = 9 := by
  have hm : U ∈ c.pointsOn L := ⟨hU, hUL⟩
  change (c.pointsOn L \ {U}).ncard = 9
  rw [Set.ncard_sdiff_singleton_of_mem hm]
  change Nat.card (c.pointsOn L) - 1 = 9
  rw [c.pointsOn_card hL]

noncomputable def neighborsEquiv (U : Subgroup G) (hU : U ∈ c.points) :
    (Σ L : c.linesThrough U, c.otherPoints U L.val) ≃ c.neighbors U := by
  let f : (Σ L : c.linesThrough U, c.otherPoints U L.val) → c.neighbors U := fun a =>
    ⟨a.2.val, a.2.property.1.1, a.2.property.2,
      a.1.val, a.1.property.1, a.1.property.2, a.2.property.1.2⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨L, x⟩ ⟨L', x'⟩ he
    have hx : x.val = x'.val := congrArg Subtype.val he
    have hLL : L' = L := Subtype.ext (c.line_unique hU x.property.1.1
      L.property.1 L'.property.1 x.property.2 L.property.2 L'.property.2
      x.property.1.2 (hx ▸ x'.property.1.2))
    subst L'
    have hxx : x = x' := Subtype.ext hx
    subst x'
    rfl
  · rintro ⟨x, hx, hne, L, hL, hUL, hxL⟩
    exact ⟨⟨⟨L, hL, hUL⟩, ⟨x, ⟨hx, hxL⟩, hne⟩⟩, rfl⟩

/-- Asc94 45.10(5), transported to every source point. -/
theorem neighbors_card {U : Subgroup G} (hU : U ∈ c.points) :
    Nat.card (c.neighbors U) = 36 := by
  classical
  let : Fintype (c.linesThrough U) := Fintype.ofFinite _
  rw [← Nat.card_congr (c.neighborsEquiv U hU), Nat.card_sigma]
  have hc (L : c.linesThrough U) : Nat.card (c.otherPoints U L.val) = 9 :=
    c.otherPoints_card hU L.property.1 L.property.2
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, c.linesThrough_card hU]

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
