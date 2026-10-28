module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOnePaths

/-!
# The normal Sylows of short paths in the noncommuting b=1 case

Every two-subgroup fixing a turn lies in its middle vertex core. Conversely,
the intersection of all interior vertex cores fixes the entire path, since
those cores fix their neighbors. Thus this literal intersection is both the
two-core and the unique Sylow two-subgroup of the full path stabilizer.

The adjacent-core index and arbitrary-turn intersection formulas compute
these Sylow orders at lengths two, three and four as q²c, qc and c, where
c is the order of the full local actor center. This makes the previous odd
path-stabilizer thresholds sharp: length four when c=1, length five when
c=q. The graph need not be a tree and the completion need not be finite.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
the proof of (10.5)(c,d), printed p.156. The marked Chapter 7 actions remain
earlier inputs. DGS regularity means transitivity on both endpoint neighbor
complements (pp.73--74); identifying its extremal r,s requires that additional
transitivity argument, and is not asserted by the oddness equivalences here.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The literal intersection of the cores at the interior vertices. -/
def pathInteriorCore {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) : Subgroup G :=
  ⨅ j ∈ Finset.Ioo 0 p.length, Q (family P) (p.getVert j)

private theorem interior_le {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    {j : ℕ} (hj : 0 < j) (hjl : j < p.length) :
    pathInteriorCore p ≤ Q (family P) (p.getVert j) :=
  iInf_le_of_le j (iInf_le _ (Finset.mem_Ioo.mpr ⟨hj,hjl⟩))

private theorem core_normalized (F : Bool → Subgroup G) (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) := by
  simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
    using (pCore 2 (stabilizer F v)).le_normalizer_map (stabilizer F v).subtype

/-- Fixing the path normalizes the intersection of its interior cores. -/
theorem pathFixer_normalizes_interiorCore {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) :
    pathFixer (X := G) p ≤ normalizer (pathInteriorCore p : Set G) := by
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  simp only [pathInteriorCore, mem_iInf]
  constructor
  · intro hx j hj
    have hn := core_normalized (family P) (p.getVert j) (hg j (by have := (Finset.mem_Ioo.mp hj).2; omega))
    exact (mem_normalizer_iff.mp hn x).mp (hx j hj)
  · intro hx j hj
    have hn := core_normalized (family P) (p.getVert j) (hg j (by have := (Finset.mem_Ioo.mp hj).2; omega))
    exact (mem_normalizer_iff.mp hn x).mpr (hx j hj)

/-- The interior-core intersection fixes both endpoints as well as the interior. -/
theorem pathInteriorCore_le_fixer (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hlen : 2 ≤ p.length) :
    pathInteriorCore p ≤ pathFixer (X := G) p := by
  intro g hg j hj
  by_cases hzero : j = 0
  · subst j
    have ha := (p.adj_getVert_succ (by omega : 0 < p.length)).symm
    exact ((source_Z_Q_U h _).2.trans ((ballKernel_one_le_edge _ ha).trans inf_le_right))
      (interior_le p (by omega) (by omega) hg)
  by_cases hend : j = p.length
  · subst j
    have ha := p.adj_getVert_succ (by omega : p.length - 1 < p.length)
    have he : p.length - 1 + 1 = p.length := by omega
    rw [he] at ha
    exact ((source_Z_Q_U h _).2.trans ((ballKernel_one_le_edge _ ha).trans inf_le_right))
      (interior_le p (by omega) (by omega) hg)
  · exact Q_le_stabilizer _ _ (interior_le p (by omega) (by omega) hg)

/-- At length two the intersection is the middle core. -/
theorem pathInteriorCore_two {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hlen : p.length = 2) :
    pathInteriorCore p = Q (family P) (p.getVert 1) := by
  ext x
  simp [pathInteriorCore, hlen, show Finset.Ioo 0 2 = {1} from rfl]

/-- At length three it is the intersection of the two middle cores. -/
theorem pathInteriorCore_three {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hlen : p.length = 3) :
    pathInteriorCore p = Q (family P) (p.getVert 1) ⊓ Q (family P) (p.getVert 2) := by
  ext x
  simp [pathInteriorCore, hlen, show Finset.Ioo 0 3 = {1,2} from rfl,
    or_imp, forall_and]

/-- At length four it is the intersection of the three middle cores. -/
theorem pathInteriorCore_four {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hlen : p.length = 4) :
    pathInteriorCore p = (Q (family P) (p.getVert 1) ⊓ Q (family P) (p.getVert 3)) ⊓
      Q (family P) (p.getVert 2) := by
  ext x
  simp [pathInteriorCore, hlen, show Finset.Ioo 0 4 = {1,2,3} from rfl,
    or_imp, forall_and, and_left_comm, and_comm]

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
include h c₀ c₁ hn₀ hn₁

/-- The intersection is the actual embedded two-core of the full path stabilizer. -/
theorem pathFixer_core_eq_interior {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    (pathFixer (X := G) p).pCoreIn 2 = pathInteriorCore p := by
  apply le_antisymm
  · apply le_iInf
    intro j
    apply le_iInf
    intro hj
    exact path_two_group_le_interior_core h c₀ c₁ hn₀ hn₁ p hp _
      (isPGroup_pCoreIn _ _) (map_subtype_le _) j
      (Finset.mem_Ioo.mp hj).1 (Finset.mem_Ioo.mp hj).2
  · exact le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 (stabilizer (family P) (p.getVert 1))).to_le
        (interior_le p (by omega) (by omega)))
      (pathInteriorCore_le_fixer h p hlen) (pathFixer_normalizes_interiorCore p)

/-- Every Sylow of the full stabilizer is this same literal intersection. -/
theorem pathFixer_sylow_eq_interior {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (T : Sylow 2 (pathFixer (X := G) p)) :
    (T : Subgroup (pathFixer (X := G) p)).map (pathFixer (X := G) p).subtype =
      pathInteriorCore p := by
  have hT : (T : Subgroup (pathFixer (X := G) p)).map (pathFixer (X := G) p).subtype ≤
      pathInteriorCore p := by
    apply le_iInf
    intro j
    apply le_iInf
    intro hj
    exact path_two_group_le_interior_core h c₀ c₁ hn₀ hn₁ p hp _
      (T.isPGroup'.map _) (map_subtype_le _) j
      (Finset.mem_Ioo.mp hj).1 (Finset.mem_Ioo.mp hj).2
  apply le_antisymm hT
  rw [←pathFixer_core_eq_interior h c₀ c₁ hn₀ hn₁ p hp hlen]
  exact pCoreIn_le_sylow _ T


local instance pathCoreFieldAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k :=
  ZMod.algebra k 2

omit hn₀ hn₁ in
/-- The same field and central factor compute every vertex core. -/
theorem vertex_core_card_of_actions
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (v : Vertex (family P)) :
    Nat.card (Q (family P) v) = Nat.card k₀ ^ 2 * Nat.card (centerIn c₀.actor) := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  rw [←hg,Q_translate,card_map_of_injective (MulAut.conj g).injective]
  cases v.type
  · exact core_card_of_natural c₀ h hc₀ E₀
  · rw [core_card_of_natural c₁ h hc₁ E₁,←paired_field_orders_eq h c₀ c₁ E₀,
      ←paired_actor_center_orders_eq h c₀ c₁ E₀ E₁]

omit hn₀ hn₁ in
private theorem base_edge_core_card
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) :
    Nat.card (Q (family P) (base (family P) false) ⊓
      Q (family P) (base (family P) true) : Subgroup G) =
      Nat.card k₀ * Nat.card (centerIn c₀.actor) := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hi := neighbor_center_index c₁ h
  rw [←hc₀,←paired_field_orders_eq h c₀ c₁ E₀] at hi
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Q (family P) (base (family P) false) ⊓ Q (family P) (base (family P) true))
    (Q (family P) (base (family P) false)) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hi,
    core_card_of_natural c₀ h hc₀ E₀] at hcount
  apply Nat.mul_right_cancel (Nat.card_pos : 0 < Nat.card k₀)
  calc
    _ = Nat.card k₀ ^ 2 * Nat.card (centerIn c₀.actor) := hcount
    _ = _ := by ring

omit hn₀ hn₁ in
/-- The intersection of the actual cores on every edge has order q times the center. -/
theorem edge_core_intersection_card
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) {u v : Vertex (family P)}
    (huv : (graph (family P)).Adj u v) :
    Nat.card (Q (family P) u ⊓ Q (family P) v : Subgroup G) =
      Nat.card k₀ * Nat.card (centerIn c₀.actor) := by
  obtain ⟨g,hu,hv⟩ := incident_common_translate (family P) huv.2
  have ht : v.type = !u.type := by
    have hne := huv.1
    cases hi : u.type <;> cases hj : v.type <;> simp_all
  rw [←hu,←hv,Q_translate,Q_translate,
    ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    card_map_of_injective (MulAut.conj g).injective,ht]
  cases u.type
  · exact base_edge_core_card h c₀ c₁ E₀
  · simpa only [Bool.not_true,inf_comm] using base_edge_core_card h c₀ c₁ E₀

/-- Cores on the ends of any turn intersect inside the middle core, with exactly
one full central factor. The field and center markings remain the original ones. -/
theorem turn_core_intersection_size
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {u v z : Vertex (family P)} (hu : (graph (family P)).Adj v u)
    (hz : (graph (family P)).Adj v z) (hne : u ≠ z) :
    Q (family P) u ⊓ Q (family P) z ≤ Q (family P) v ∧
      Nat.card (Q (family P) u ⊓ Q (family P) z : Subgroup G) =
        Nat.card (centerIn c₀.actor) := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hb (i : Bool) {u z : Vertex (family P)}
      (hu : (graph (family P)).Adj (base (family P) i) u)
      (hz : (graph (family P)).Adj (base (family P) i) z) (hne : u ≠ z) :
      Q (family P) u ⊓ Q (family P) z ≤ Q (family P) (base (family P) i) ∧
        Nat.card (Q (family P) u ⊓ Q (family P) z : Subgroup G) =
          Nat.card (centerIn c₀.actor) := by
    cases i
    · rw [base_two_neighbor_core_intersection h false c₀ hn₀ hc₀ hc₁ hu hz hne]
      exact ⟨(actor_center_le_cores c₀ h hc₀).trans inf_le_left,rfl⟩
    · rw [base_two_neighbor_core_intersection h true c₁ hn₁ hc₁ hc₀ hu hz hne]
      exact ⟨(actor_center_le_cores c₁ h hc₁).trans inf_le_left,
        (paired_actor_center_orders_eq h c₀ c₁ E₀ E₁).symm⟩
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  have hbase : g⁻¹ • v = base (family P) v.type := inv_smul_eq_iff.mpr hg.symm
  have hu' : (graph (family P)).Adj (base (family P) v.type) (g⁻¹ • u) := by
    have hh : (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • u) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hu
    rwa [hbase] at hh
  have hz' : (graph (family P)).Adj (base (family P) v.type) (g⁻¹ • z) := by
    have hh : (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • z) :=
      (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hz
    rwa [hbase] at hh
  obtain ⟨hle,hcard⟩ := hb v.type hu' hz' (fun he => hne ((MulAction.toPerm g⁻¹).injective he))
  constructor
  · apply (map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective).mp
    rwa [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      ←Q_translate,←Q_translate,←Q_translate,hbase]
  · rw [Q_translate,Q_translate,←Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective] at hcard
    exact hcard

/-- Exact orders of the normal Sylow two-subgroups of paths of lengths two,
three and four. These are literal full path stabilizers, not local kernels. -/
theorem short_path_sylow_orders
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (T : Sylow 2 (pathFixer (X := G) p)) :
    (p.length = 2 → Nat.card T = Nat.card k₀ ^ 2 * Nat.card (centerIn c₀.actor)) ∧
    (p.length = 3 → Nat.card T = Nat.card k₀ * Nat.card (centerIn c₀.actor)) ∧
    (p.length = 4 → Nat.card T = Nat.card (centerIn c₀.actor)) := by
  have hcard (hlen : 2 ≤ p.length) : Nat.card T = Nat.card (pathInteriorCore p) := by
    rw [←pathFixer_sylow_eq_interior h c₀ c₁ hn₀ hn₁ p hp hlen T,
      card_map_of_injective (pathFixer (X := G) p).subtype_injective]
  refine ⟨?_,?_,?_⟩
  · intro hl
    rw [hcard (by omega),pathInteriorCore_two p hl]
    exact vertex_core_card_of_actions h c₀ c₁ E₀ E₁ _
  · intro hl
    rw [hcard (by omega),pathInteriorCore_three p hl]
    exact edge_core_intersection_card h c₀ c₁ E₀
      (p.adj_getVert_succ (by omega : 1 < p.length))
  · intro hl
    have ht := turn_core_intersection_size h c₀ c₁ hn₀ hn₁ E₀ E₁
      (p.adj_getVert_succ (by omega : 1 < p.length)).symm
      (p.adj_getVert_succ (by omega : 2 < p.length))
      (by
        intro he
        have hh := hp.getVert_injOn (by omega : 1 ≤ p.length)
          (by omega : 3 ≤ p.length) he
        omega)
    rw [hcard (by omega),pathInteriorCore_four p hl,inf_eq_left.mpr ht.1]
    exact ht.2


omit h c₀ c₁ hn₀ hn₁ in
private theorem field_card_even : Even (Nat.card k₀) := by
  let := Fintype.ofFinite k₀
  rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
  exact (CharP.cast_eq_zero_iff k₀ 2 _).mp (FiniteField.cast_card_eq_zero k₀)

/-- The preceding length-three stabilizers are even, in both center branches. -/
theorem pathFixer_even_of_length_three
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : p.IsPath) (hlen : p.length = 3) :
    Even (Nat.card (pathFixer (X := G) p)) := by
  let := finite_endpoints h
  have hle : pathFixer (X := G) p ≤ stabilizer (family P) a := by
    intro x hx
    change x • a = a
    simpa only [SimpleGraph.Walk.getVert_zero] using hx 0 (Nat.zero_le _)
  let : Finite (pathFixer (X := G) p) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  let T : Sylow 2 (pathFixer (X := G) p) := Classical.choice inferInstance
  have hc := (short_path_sylow_orders h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp T).2.1 hlen
  apply even_iff_two_dvd.mpr
  have he : 2 ∣ Nat.card T := by
    rw [hc]
    exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp (field_card_even (k₀ := k₀))) _
  exact he.trans (T : Subgroup (pathFixer (X := G) p)).card_subgroup_dvd_card

/-- A nontrivial full center gives even stabilizers at length four. -/
theorem pathFixer_even_of_length_four_of_center_card
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hcenter : Nat.card (centerIn c₀.actor) = Nat.card k₀)
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : p.IsPath) (hlen : p.length = 4) :
    Even (Nat.card (pathFixer (X := G) p)) := by
  let := finite_endpoints h
  have hle : pathFixer (X := G) p ≤ stabilizer (family P) a := by
    intro x hx
    change x • a = a
    simpa only [SimpleGraph.Walk.getVert_zero] using hx 0 (Nat.zero_le _)
  let : Finite (pathFixer (X := G) p) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  let T : Sylow 2 (pathFixer (X := G) p) := Classical.choice inferInstance
  have hc := (short_path_sylow_orders h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp T).2.2 hlen
  rw [hcenter] at hc
  apply even_iff_two_dvd.mpr
  have he : 2 ∣ Nat.card T := hc.symm ▸ even_iff_two_dvd.mp (field_card_even (k₀ := k₀))
  exact he.trans (T : Subgroup (pathFixer (X := G) p)).card_subgroup_dvd_card

/-- The oddness thresholds are sharp: four in the center-free case, five in
the other case. This does not identify oddness with DGS path regularity. -/
theorem pathFixer_odd_thresholds
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    (centerIn c₀.actor = ⊥ ∧ centerIn c₁.actor = ⊥ ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        p.IsPath → 3 ≤ p.length →
          (Odd (Nat.card (pathFixer (X := G) p)) ↔ 4 ≤ p.length)) ∨
    (Nat.card (centerIn c₀.actor) = Nat.card k₀ ∧
      Nat.card (centerIn c₁.actor) = Nat.card k₁ ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        p.IsPath → 3 ≤ p.length →
          (Odd (Nat.card (pathFixer (X := G) p)) ↔ 5 ≤ p.length)) := by
  rcases paired_center_order_dichotomy h c₀ c₁ E₀ E₁ hn₀ hn₁ with ⟨hc₀,hc₁⟩ | ⟨hc₀,hc₁⟩
  · left
    refine ⟨hc₀,hc₁,fun {_ _} p hp hlen => ⟨?_,?_⟩⟩
    · intro ho
      by_contra hlt
      have hl : p.length = 3 := by omega
      exact (Nat.not_even_iff_odd.mpr ho)
        (pathFixer_even_of_length_three h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp hl)
    · exact pathFixer_odd_of_four_le_of_centers_bot h c₀ c₁ hn₀ hn₁ hc₀ hc₁ p hp
  · right
    refine ⟨hc₀,hc₁,fun {_ _} p hp hlen => ⟨?_,?_⟩⟩
    · intro ho
      by_contra hlt
      have hl : p.length = 3 ∨ p.length = 4 := by omega
      rcases hl with hl | hl
      · exact (Nat.not_even_iff_odd.mpr ho)
          (pathFixer_even_of_length_three h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp hl)
      · exact (Nat.not_even_iff_odd.mpr ho)
          (pathFixer_even_of_length_four_of_center_card h c₀ c₁ hn₀ hn₁ E₀ E₁ hc₀ p hp hl)
    · exact pathFixer_odd_of_five_le h c₀ c₁ hn₀ hn₁ p hp

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
