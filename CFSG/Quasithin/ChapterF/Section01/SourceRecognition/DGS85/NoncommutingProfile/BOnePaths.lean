module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneNeighbors
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanUniqueness

/-!
# Odd path stabilizers in the noncommuting b=1 branch

Conjugation moves an arbitrary turn to a marked endpoint. The local
SL₂ calculation then places every two-subgroup fixing that turn in the
middle core. Along a path, four consecutive interior cores have trivial
intersection: the two crossed pairs are the full centers of adjacent
actors, whose intersection is killed by faithfulness.

Consequently every path of length at least five has odd pointwise
stabilizer. If both actor centers are trivial, three interior cores already
suffice, and the bound is four. The pointwise stabilizer is the actual
`pathFixer` used by the apartment-uniqueness consumer. Only finite vertex
stabilizers are used; neither a finite completion nor a tree is assumed.

Source: DGS, *Groups and Graphs* (1985), the proof of 10.5(c,d), p.156.
The marked Chapter 7 actions remain earlier inputs. The exact extremal
regular-path parameters r and s are separate obligations.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
include h c₀ c₁ hn₀ hn₁

/-- Two-subgroups fixing an arbitrary turn lie in the actual middle vertex core. -/
theorem two_group_fixes_turn {u v z : Vertex (family P)}
    (hu : (graph (family P)).Adj v u) (hz : (graph (family P)).Adj v z) (hne : u ≠ z)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hAv : A ≤ stabilizer (family P) v)
    (hAu : A ≤ stabilizer (family P) u) (hAz : A ≤ stabilizer (family P) z) :
    A ≤ Q (family P) v := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hb (i : Bool) {u z : Vertex (family P)}
      (hu : (graph (family P)).Adj (base (family P) i) u)
      (hz : (graph (family P)).Adj (base (family P) i) z) (hne : u ≠ z)
      (A : Subgroup G) (hA : IsPGroup 2 A)
      (hAv : A ≤ stabilizer (family P) (base (family P) i))
      (hAu : A ≤ stabilizer (family P) u) (hAz : A ≤ stabilizer (family P) z) :
      A ≤ Q (family P) (base (family P) i) := by
    cases i
    · exact base_two_group_fixes_turn h false c₀ hn₀ hc₁ hu hz hne A hA hAv hAu hAz
    · exact base_two_group_fixes_turn h true c₁ hn₁ hc₀ hu hz hne A hA hAv hAu hAz
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  have hbase : g⁻¹ • v = base (family P) v.type := by exact inv_smul_eq_iff.mpr hg.symm
  have hu' : (graph (family P)).Adj (base (family P) v.type) (g⁻¹ • u) := by
    have hh : (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • u) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hu
    rwa [hbase] at hh
  have hz' : (graph (family P)).Adj (base (family P) v.type) (g⁻¹ • z) := by
    have hh : (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • z) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hz
    rwa [hbase] at hh
  have hm {x : Vertex (family P)} (hx : A ≤ stabilizer (family P) x) :
      A.map (MulAut.conj g⁻¹).toMonoidHom ≤ stabilizer (family P) (g⁻¹ • x) := by
    rw [stabilizer_translate]
    exact map_mono hx
  apply (map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).mp
  rw [←Q_translate,hbase]
  exact hb v.type hu' hz' (fun he => hne ((MulAction.toPerm g⁻¹).injective he))
    _ (hA.map _) (hbase ▸ hm hAv) (hm hAu) (hm hAz)

private theorem base_crossed_cores_disjoint (i : Bool) {u z : Vertex (family P)}
    (hu : (graph (family P)).Adj (base (family P) i) u)
    (hz : (graph (family P)).Adj (base (family P) (!i)) z)
    (hune : u ≠ base (family P) (!i)) (hzne : base (family P) i ≠ z) :
    (Q (family P) u ⊓ Q (family P) (base (family P) (!i))) ⊓
      (Q (family P) (base (family P) i) ⊓ Q (family P) z) = ⊥ := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hd := paired_actor_centers_disjoint h c₀ c₁ hn₀ hn₁
  cases i
  · simp only [Bool.not_false] at *
    rw [base_two_neighbor_core_intersection h false c₀ hn₀ hc₀ hc₁ hu c₀.adjacent hune,
      base_two_neighbor_core_intersection h true c₁ hn₁ hc₁ hc₀ c₁.adjacent hz hzne]
    exact hd.eq_bot
  · simp only [Bool.not_true] at *
    rw [base_two_neighbor_core_intersection h true c₁ hn₁ hc₁ hc₀ hu c₁.adjacent hune,
      base_two_neighbor_core_intersection h false c₀ hn₀ hc₀ hc₁ c₀.adjacent hz hzne]
    exact hd.symm.eq_bot

/-- The four interior cores of a nonbacktracking path have trivial intersection. -/
theorem crossed_cores_disjoint {a b c d : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (hbc : (graph (family P)).Adj b c)
    (hcd : (graph (family P)).Adj c d) (hac : a ≠ c) (hbd : b ≠ d) :
    (Q (family P) a ⊓ Q (family P) c) ⊓ (Q (family P) b ⊓ Q (family P) d) = ⊥ := by
  obtain ⟨g,hb,hc⟩ := incident_common_translate (family P) hbc.2
  have ht : c.type = !b.type := by
    have hne := hbc.1
    cases hi : b.type <;> cases hj : c.type <;> simp_all
  have hb' : g⁻¹ • b = base (family P) b.type := by exact inv_smul_eq_iff.mpr hb.symm
  have hc' : g⁻¹ • c = base (family P) (!b.type) := by
    have hh : g⁻¹ • c = base (family P) c.type := inv_smul_eq_iff.mpr hc.symm
    simpa only [ht] using hh
  have ha' : (graph (family P)).Adj (base (family P) b.type) (g⁻¹ • a) := by
    have hh : (graph (family P)).Adj (g⁻¹ • b) (g⁻¹ • a) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hab.symm
    rwa [hb'] at hh
  have hd' : (graph (family P)).Adj (base (family P) (!b.type)) (g⁻¹ • d) := by
    have hh : (graph (family P)).Adj (g⁻¹ • c) (g⁻¹ • d) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hcd
    rwa [hc'] at hh
  have han : g⁻¹ • a ≠ base (family P) (!b.type) := by
    rw [←hc']
    exact fun he => hac ((MulAction.toPerm g⁻¹).injective he)
  have hdn : base (family P) b.type ≠ g⁻¹ • d := by
    rw [←hb']
    exact fun he => hbd ((MulAction.toPerm g⁻¹).injective he)
  apply (map_eq_bot_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) _ (MulAut.conj g⁻¹).injective).mp
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    ←Q_translate,←Q_translate,←Q_translate,←Q_translate,hb',hc']
  exact base_crossed_cores_disjoint h c₀ c₁ hn₀ hn₁ b.type ha' hd' han hdn

/-- In the center-free branch, two cores separated by a turn are disjoint. -/
theorem turn_cores_disjoint_of_centers_bot
    (hC₀ : centerIn c₀.actor = ⊥) (hC₁ : centerIn c₁.actor = ⊥)
    {u v z : Vertex (family P)} (hu : (graph (family P)).Adj v u)
    (hz : (graph (family P)).Adj v z) (hne : u ≠ z) :
    Q (family P) u ⊓ Q (family P) z = ⊥ := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hb (i : Bool) {u z : Vertex (family P)}
      (hu : (graph (family P)).Adj (base (family P) i) u)
      (hz : (graph (family P)).Adj (base (family P) i) z) (hne : u ≠ z) :
      Q (family P) u ⊓ Q (family P) z = ⊥ := by
    cases i
    · exact (base_two_neighbor_core_intersection h false c₀ hn₀ hc₀ hc₁ hu hz hne).trans hC₀
    · exact (base_two_neighbor_core_intersection h true c₁ hn₁ hc₁ hc₀ hu hz hne).trans hC₁
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  have hbase : g⁻¹ • v = base (family P) v.type := by exact inv_smul_eq_iff.mpr hg.symm
  have hu' : (graph (family P)).Adj (base (family P) v.type) (g⁻¹ • u) := by
    have hh : (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • u) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hu
    rwa [hbase] at hh
  have hz' : (graph (family P)).Adj (base (family P) v.type) (g⁻¹ • z) := by
    have hh : (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • z) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hz
    rwa [hbase] at hh
  apply (map_eq_bot_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) _ (MulAut.conj g⁻¹).injective).mp
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,←Q_translate,←Q_translate]
  exact hb v.type hu' hz' (fun he => hne ((MulAction.toPerm g⁻¹).injective he))

/-- Every two-subgroup of a path stabilizer lies in each interior vertex core. -/
theorem path_two_group_le_interior_core {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hAP : A ≤ pathFixer (X := G) p)
    (j : ℕ) (hj : 0 < j) (hjl : j < p.length) :
    A ≤ Q (family P) (p.getVert j) := by
  have hprev := p.adj_getVert_succ (show j-1 < p.length by omega)
  have hjprev : j-1+1 = j := by omega
  rw [hjprev] at hprev
  have hnext := p.adj_getVert_succ hjl
  have hne : p.getVert (j-1) ≠ p.getVert (j+1) := by
    intro he
    have := hp.getVert_injOn (by omega : j-1 ≤ p.length) (by omega : j+1 ≤ p.length) he
    omega
  exact two_group_fixes_turn h c₀ c₁ hn₀ hn₁ hprev.symm hnext hne A hA
    (fun x hx => hAP hx j (by omega))
    (fun x hx => hAP hx (j-1) (by omega))
    (fun x hx => hAP hx (j+1) (by omega))

omit h c₀ c₁ hn₀ hn₁ in
private theorem odd_card_of_two_subgroups_bot (H : Subgroup G) [Finite H]
    (hH : ∀ A : Subgroup G, IsPGroup 2 A → A ≤ H → A = ⊥) : Odd (Nat.card H) := by
  let T : Sylow 2 H := Classical.choice inferInstance
  have hT : (T : Subgroup H) = ⊥ :=
    (map_eq_bot_iff_of_injective _ H.subtype_injective).mp
      (hH _ (T.isPGroup'.map H.subtype) (map_subtype_le _))
  apply Nat.not_even_iff_odd.mp
  intro he
  have hd := T.dvd_card_of_dvd_card (even_iff_two_dvd.mp he)
  have hc : Nat.card T = 1 := card_eq_one.mpr hT
  rw [hc] at hd
  exact (by decide : ¬2 ∣ 1) hd

/-- Every path of length at least five has odd pointwise stabilizer. -/
theorem pathFixer_odd_of_five_le {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath) (hlen : 5 ≤ p.length) :
    Odd (Nat.card (pathFixer (X := G) p)) := by
  let := finite_endpoints h
  have hle : pathFixer (X := G) p ≤ stabilizer (family P) a := by
    intro x hx
    change x • a = a
    simpa only [SimpleGraph.Walk.getVert_zero] using hx 0 (Nat.zero_le _)
  let : Finite (pathFixer (X := G) p) := Finite.of_injective (inclusion hle) (inclusion_injective _)
  apply odd_card_of_two_subgroups_bot
  intro A hA hAP
  have hQ (j : ℕ) (hj : 0 < j) (hjl : j < p.length) :=
    path_two_group_le_interior_core h c₀ c₁ hn₀ hn₁ p hp A hA hAP j hj hjl
  have hne (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) (hne : i ≠ j) :
      p.getVert i ≠ p.getVert j := fun he => hne (hp.getVert_injOn hi hj he)
  apply eq_bot_iff.mpr
  have hC := crossed_cores_disjoint h c₀ c₁ hn₀ hn₁
    (p.adj_getVert_succ (by omega : 1 < p.length))
    (p.adj_getVert_succ (by omega : 2 < p.length))
    (p.adj_getVert_succ (by omega : 3 < p.length))
    (hne 1 3 (by omega) (by omega) (by decide))
    (hne 2 4 (by omega) (by omega) (by decide))
  exact (le_inf (le_inf (hQ 1 (by omega) (by omega)) (hQ 3 (by omega) (by omega)))
    (le_inf (hQ 2 (by omega) (by omega)) (hQ 4 (by omega) (by omega)))).trans hC.le

/-- In the center-free branch every path of length at least four has odd stabilizer. -/
theorem pathFixer_odd_of_four_le_of_centers_bot
    (hC₀ : centerIn c₀.actor = ⊥) (hC₁ : centerIn c₁.actor = ⊥)
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : p.IsPath) (hlen : 4 ≤ p.length) :
    Odd (Nat.card (pathFixer (X := G) p)) := by
  let := finite_endpoints h
  have hle : pathFixer (X := G) p ≤ stabilizer (family P) a := by
    intro x hx
    change x • a = a
    simpa only [SimpleGraph.Walk.getVert_zero] using hx 0 (Nat.zero_le _)
  let : Finite (pathFixer (X := G) p) := Finite.of_injective (inclusion hle) (inclusion_injective _)
  apply odd_card_of_two_subgroups_bot
  intro A hA hAP
  have hQ (j : ℕ) (hj : 0 < j) (hjl : j < p.length) :=
    path_two_group_le_interior_core h c₀ c₁ hn₀ hn₁ p hp A hA hAP j hj hjl
  have hC := turn_cores_disjoint_of_centers_bot h c₀ c₁ hn₀ hn₁ hC₀ hC₁
    (p.adj_getVert_succ (by omega : 1 < p.length)).symm
    (p.adj_getVert_succ (by omega : 2 < p.length))
    (by intro he; have := hp.getVert_injOn (by omega : 1 ≤ p.length) (by omega : 3 ≤ p.length) he; omega)
  exact eq_bot_iff.mpr ((le_inf (hQ 1 (by omega) (by omega)) (hQ 3 (by omega) (by omega))).trans hC.le)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
