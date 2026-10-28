module

public import Theory.GroupAction.CubicTree.CentralIntervals
public import Mathlib.Data.Fintype.Card

/-!
# Conjugating central intervals by a finite reflection

Conjugation transports an edge stabilizer and its center using only the two
endpoint images. If an automorphism reverses the finite fixed interval of an
element on a cubic tree track, its conjugate has exactly the same fixed interval.
At either endpoint, the original element fixes one neighbor and moves the other
two. This property survives conjugation; convexity in the tree then excludes
all further fixed track vertices. The longest central interval is reflected
inside the unchanged fixed interval.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.7), p.398.
-/

@[expose] public section

open SimpleGraph Subgroup
open SimpleGraph.PathTransitivePolygon
namespace Theory.GroupAction.CubicTree
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

private theorem moves_neighbor_of_fixes_neighbor
    (hact : GraphAction Γ G) {x a b y : V}
    (hcubic : Nat.card (Γ.neighborSet x) = 3) {z : G}
    (hzx : z • x = x) (hza : z • a = a) (hzb : z • b ≠ b)
    (hxa : Γ.Adj x a) (hxb : Γ.Adj x b) (hxy : Γ.Adj x y) (hya : y ≠ a) :
    z • y ≠ y := by
  classical
  let : Finite (Γ.neighborSet x) := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype (Γ.neighborSet x) := Fintype.ofFinite _
  have hba : b ≠ a := by rintro rfl; exact hzb hza
  intro hzy
  have hby : b ≠ y := by rintro rfl; exact hzb hzy
  let A : Γ.neighborSet x := ⟨a, hxa⟩
  let B : Γ.neighborSet x := ⟨b, hxb⟩
  let Y : Γ.neighborSet x := ⟨y, hxy⟩
  let C : Γ.neighborSet x := ⟨z • b, by
    change Γ.Adj x (z • b)
    simpa only [hzx] using hact.map_adj z hxb⟩
  have hBA : B ≠ A := fun he => hba (congrArg Subtype.val he)
  have hYA : Y ≠ A := fun he => hya (congrArg Subtype.val he)
  have hBY : B ≠ Y := fun he => hby (congrArg Subtype.val he)
  have hCA : C ≠ A := by
    intro he
    exact hba ((MulAction.toPerm z).injective ((congrArg Subtype.val he).trans hza.symm))
  have hCY : C ≠ Y := by
    intro he
    exact hby ((MulAction.toPerm z).injective ((congrArg Subtype.val he).trans hzy.symm))
  have hCB : C ≠ B := fun he => hzb (congrArg Subtype.val he)
  have hle := Finset.card_le_univ ({C, B, Y, A} : Finset (Γ.neighborSet x))
  have hfour : ({C, B, Y, A} : Finset (Γ.neighborSet x)).card = 4 := by
    simp [hCA, hCY, hCB, hBA, hBY, hYA]
  rw [hfour, ← Nat.card_eq_fintype_card, hcubic] at hle
  omega

namespace Track

theorem edgeStabilizer_local_reflection (t : Track Γ G) (g : G) (i j : ℤ)
    (hg0 : g • t.vertex i = t.vertex (j + 1))
    (hg1 : g • t.vertex (i + 1) = t.vertex j) :
    (t.edgeStabilizer i).map (MulAut.conj g).toMonoidHom = t.edgeStabilizer j := by
  unfold edgeStabilizer
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hg0, hg1, inf_comm]

theorem centralEdge_local_reflection_iff (t : Track Γ G) (g : G) (i j : ℤ)
    (hg0 : g • t.vertex i = t.vertex (j + 1))
    (hg1 : g • t.vertex (i + 1) = t.vertex j) (z : G) :
    t.CentralEdge ((MulAut.conj g) z) j ↔ t.CentralEdge z i := by
  rw [CentralEdge, ← t.edgeStabilizer_local_reflection g i j hg0 hg1]
  constructor
  · rintro ⟨⟨z', hz', he⟩, hc⟩
    have hz'z : z' = z := (MulAut.conj g).injective he
    subst z'
    refine ⟨hz', ?_⟩
    intro x hx
    exact (Commute.conj_iff g).1 (hc ((MulAut.conj g) x) ⟨x, hx, rfl⟩)
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro x ⟨x', hx', rfl⟩
    exact (hc x' hx').conj g

theorem fixed_local_conjugation_iff (t : Track Γ G) (g z : G) (i : ℤ) (v : V)
    (hg : g • t.vertex i = v) :
    (MulAut.conj g) z • v = v ↔ z • t.vertex i = t.vertex i := by
  rw [← hg]
  change (g * z * g⁻¹) • (g • t.vertex i) = g • t.vertex i ↔ _
  simp only [mul_smul, inv_smul_smul]
  exact (MulAction.toPerm g).injective.eq_iff

theorem CentralInterval.fixed_iff_local_reflection
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (hcubic : ∀ v, Nat.card (Γ.neighborSet v) = 3)
    {t : Track Γ G} {z : G} (d : t.CentralInterval z) (g : G)
    (hg : ∀ i, d.fixedLeft ≤ i → i ≤ d.fixedRight →
      g • t.vertex i = t.vertex (d.fixedLeft + d.fixedRight - i)) (i : ℤ) :
    (MulAut.conj g) z • t.vertex i = t.vertex i ↔
      d.fixedLeft ≤ i ∧ i ≤ d.fixedRight := by
  have hlt : d.fixedLeft < d.fixedRight := by
    have := d.centralLeft_mem
    have := d.centralRight_mem
    have := d.central_lt
    omega
  have hf : ∀ j, d.fixedLeft ≤ j → j ≤ d.fixedRight →
      (MulAut.conj g) z • t.vertex j = t.vertex j := by
    intro j hj hj'
    apply (t.fixed_local_conjugation_iff g z
      (d.fixedLeft + d.fixedRight - j) (t.vertex j) ?_).2
    · exact (d.fixed_iff _).2 ⟨by omega, by omega⟩
    · convert hg (d.fixedLeft + d.fixedRight - j) (by omega) (by omega) using 1
      congr 1
      omega
  have hgL : g • t.vertex d.fixedLeft = t.vertex d.fixedRight := by
    simpa only [add_sub_cancel_left] using hg d.fixedLeft le_rfl hlt.le
  have hgR : g • t.vertex d.fixedRight = t.vertex d.fixedLeft := by
    simpa only [add_sub_cancel_right] using hg d.fixedRight hlt.le le_rfl
  have hnL : (MulAut.conj g) z • t.vertex (d.fixedLeft - 1) ≠
      t.vertex (d.fixedLeft - 1) := by
    apply moves_neighbor_of_fixes_neighbor hact (hcubic (t.vertex d.fixedLeft))
      (hf d.fixedLeft le_rfl hlt.le) (hf (d.fixedLeft + 1) (by omega) (by omega))
      (b := g • t.vertex (d.fixedRight + 1))
    · intro he
      have hh := (t.fixed_local_conjugation_iff g z (d.fixedRight + 1) _ rfl).1 he
      have := (d.fixed_iff _).1 hh
      omega
    · exact t.adjacent d.fixedLeft
    · simpa only [hgR] using hact.map_adj g (t.adjacent d.fixedRight)
    · simpa only [sub_add_cancel] using (t.adjacent (d.fixedLeft - 1)).symm
    · intro he
      have := t.injective he
      omega
  have hnR : (MulAut.conj g) z • t.vertex (d.fixedRight + 1) ≠
      t.vertex (d.fixedRight + 1) := by
    apply moves_neighbor_of_fixes_neighbor hact (hcubic (t.vertex d.fixedRight))
      (hf d.fixedRight hlt.le le_rfl) (hf (d.fixedRight - 1) (by omega) (by omega))
      (b := g • t.vertex (d.fixedLeft - 1))
    · intro he
      have hh := (t.fixed_local_conjugation_iff g z (d.fixedLeft - 1) _ rfl).1 he
      have := (d.fixed_iff _).1 hh
      omega
    · simpa only [sub_add_cancel] using (t.adjacent (d.fixedRight - 1)).symm
    · have hh := hact.map_adj g (t.adjacent (d.fixedLeft - 1)).symm
      simpa only [sub_add_cancel, hgL] using hh
    · exact t.adjacent d.fixedRight
    · intro he
      have := t.injective he
      omega
  constructor
  · intro hi
    constructor
    · by_contra hn
      exact hnL (t.toLine.fixed_between hΓ hact hi (hf d.fixedLeft le_rfl hlt.le)
        (by omega) (by omega))
    · by_contra hn
      exact hnR (t.toLine.fixed_between hΓ hact (hf d.fixedRight hlt.le le_rfl) hi
        (by omega) (by omega))
  · exact fun hi => hf i hi.1 hi.2

/-- A reflection defined on the finite fixed interval transports its complete
central interval; global preservation of the track is unnecessary. -/
def CentralInterval.localReflection
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (hcubic : ∀ v, Nat.card (Γ.neighborSet v) = 3)
    {t : Track Γ G} {z : G} (d : t.CentralInterval z) (g : G)
    (hg : ∀ i, d.fixedLeft ≤ i → i ≤ d.fixedRight →
      g • t.vertex i = t.vertex (d.fixedLeft + d.fixedRight - i)) :
    t.CentralInterval ((MulAut.conj g) z) where
  fixedLeft := d.fixedLeft
  fixedRight := d.fixedRight
  centralLeft := d.fixedLeft + d.fixedRight - d.centralRight
  centralRight := d.fixedLeft + d.fixedRight - d.centralLeft
  fixed_iff := d.fixed_iff_local_reflection hΓ hact hcubic g hg
  central_lt := by have := d.central_lt; omega
  central i hi hir := by
    have hL := d.centralLeft_mem
    have hR := d.centralRight_mem
    apply (t.centralEdge_local_reflection_iff g
      (d.fixedLeft + d.fixedRight - i - 1) i ?_ ?_ z).2
    · exact d.central _ (by omega) (by omega)
    · convert hg (d.fixedLeft + d.fixedRight - i - 1) (by omega) (by omega) using 1
      congr 1
      omega
    · convert hg (d.fixedLeft + d.fixedRight - i - 1 + 1) (by omega) (by omega) using 1
      congr 1
      omega
  maximal a b hab hcentral := by
    have ha : d.fixedLeft ≤ a :=
      ((d.fixed_iff_local_reflection hΓ hact hcubic g hg a).1
        (hcentral a le_rfl hab).fixes_left).1
    have hb : b ≤ d.fixedRight := by
      have hh := (hcentral (b - 1) (by omega) (by omega)).fixes_right
      rw [sub_add_cancel] at hh
      exact ((d.fixed_iff_local_reflection hΓ hact hcubic g hg b).1 hh).2
    have hh := d.maximal (d.fixedLeft + d.fixedRight - b)
      (d.fixedLeft + d.fixedRight - a) (by omega) (fun i hi hir => by
        apply (t.centralEdge_local_reflection_iff g i
          (d.fixedLeft + d.fixedRight - i - 1) ?_ ?_ z).1
        · exact hcentral _ (by omega) (by omega)
        · convert hg i (by omega) (by omega) using 1
          congr 1
          omega
        · convert hg (i + 1) (by omega) (by omega) using 1
          congr 1
          omega)
    omega

theorem CentralInvolution.localReflection
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (hcubic : ∀ v, Nat.card (Γ.neighborSet v) = 3)
    {t : Track Γ G} {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z) (g : G)
    (hg : ∀ i, d.fixedLeft ≤ i → i ≤ d.fixedRight →
      g • t.vertex i = t.vertex (d.fixedLeft + d.fixedRight - i)) :
    t.CentralInvolution ((MulAut.conj g) z) := by
  let d' := d.localReflection hΓ hact hcubic g hg
  exact ⟨(orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z).trans hz.1,
    d'.centralLeft, d'.central d'.centralLeft le_rfl d'.central_lt⟩

end Track
end Theory.GroupAction.CubicTree
