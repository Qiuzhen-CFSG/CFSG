module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneValence

/-!
# Short-path roots act transitively on the endpoint complements

Fixing an additional endpoint cuts the literal interior-core intersection
down to the intersection for the extended path. Orbit--stabilizer and the
q-fold drop in the checked root orders q²c, qc, c, 1 give transitivity on
all q exits. A new exit exists by bipartiteness, so the argument works on
the source graph without assuming it is a tree. It proves regularity at
lengths two and three, and at length four when the actor center has order q.

Source: DGS, *Groups and Graphs* (1985), (10.5)(c,d), p.156, and the
literal two-endpoint definition of regularity on pp.73--74.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

variable {G V : Type*} [Group G] [MulAction G V]

private theorem orbit_covers_of_card (A : Subgroup G) [Finite A] (X : Set V) [Finite X]
    (z : V) (hz : z ∈ X) (hstable : ∀ g ∈ A, ∀ x ∈ X, g • x ∈ X)
    (hcard : Nat.card A = Nat.card X * Nat.card (MulAction.stabilizer A z)) :
    ∀ x ∈ X, ∃ g ∈ A, g • z = x := by
  have ho : MulAction.orbit A z ⊆ X := by
    rintro _ ⟨g,rfl⟩
    exact hstable g g.property z hz
  let f : MulAction.orbit A z → X := fun x => ⟨x,ho x.property⟩
  have hf : Function.Injective f := fun x y he => Subtype.ext (congrArg (fun z : X => (z : V)) he)
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A z)
  rw [Nat.card_prod,hcard] at hc
  have he : Nat.card (MulAction.orbit A z) = Nat.card X :=
    Nat.mul_right_cancel (Nat.card_pos : 0 < Nat.card (MulAction.stabilizer A z)) hc
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,he⟩).2
  intro x hx
  obtain ⟨y,hy⟩ := hs ⟨x,hx⟩
  obtain ⟨g,hg⟩ := y.property
  exact ⟨g,g.property,hg.trans (congrArg Subtype.val hy)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
local instance bOneRootActionsAlgebra1 {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

private theorem interior_core_two {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hlen : 2 ≤ p.length) : IsPGroup 2 (pathInteriorCore p) := by
  have hh : pathInteriorCore p ≤ Q (family P) (p.getVert 1) :=
    iInf_le_of_le 1 (iInf_le _ (Finset.mem_Ioo.mpr ⟨by omega,by omega⟩))
  exact (isPGroup_pCoreIn 2 (stabilizer (family P) (p.getVert 1))).to_le hh

include h c₀ c₁ hn₀ hn₁ in
private theorem two_group_le_interior {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hfix : A ≤ pathFixer (X := G) p) :
    A ≤ pathInteriorCore p := by
  apply le_iInf
  intro j
  apply le_iInf
  intro hj
  exact path_two_group_le_interior_core h c₀ c₁ hn₀ hn₁ p hp A hA hfix j
    (Finset.mem_Ioo.mp hj).1 (Finset.mem_Ioo.mp hj).2

include h c₀ c₁ hn₀ hn₁ in
/-- Fixing one additional endpoint cuts the old path root down to the new one. -/
theorem interior_core_exit_stabilizer {a b z : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (hz : (graph (family P)).Adj b z) (hznew : z ∉ p.support) :
    MulAction.stabilizer (pathInteriorCore p) z =
      (pathInteriorCore (p.concat hz)).subgroupOf (pathInteriorCore p) := by
  have he : pathInteriorCore p ⊓ stabilizer (family P) z = pathInteriorCore (p.concat hz) := by
    apply le_antisymm
    · apply two_group_le_interior h c₀ c₁ hn₀ hn₁ (p.concat hz) (hp.concat hznew hz)
        _ ((interior_core_two p hlen).to_le inf_le_left)
      intro x hx j hj
      by_cases hjp : j ≤ p.length
      · simpa only [concat_eq_append,getVert_append',if_pos hjp] using
          pathInteriorCore_le_fixer h p hlen hx.1 j hjp
      · have hje : j = p.length + 1 := by simp only [length_concat] at hj; omega
        subst j
        have hget : (p.concat hz).getVert (p.length+1) = z := by
          simpa only [length_concat] using (p.concat hz).getVert_length
        rw [hget]
        exact hx.2
    · refine le_inf ?_ ?_
      · apply le_iInf
        intro j
        apply le_iInf
        intro hj
        have hj' := Finset.mem_Ioo.mp hj
        have hh : pathInteriorCore (p.concat hz) ≤ Q (family P) ((p.concat hz).getVert j) :=
          iInf_le_of_le j (iInf_le _ (Finset.mem_Ioo.mpr ⟨hj'.1,by simp only [length_concat]; omega⟩))
        simpa only [concat_eq_append,getVert_append',if_pos (Nat.le_of_lt hj'.2)] using hh
      · intro x hx
        have hh := pathInteriorCore_le_fixer h (p.concat hz) (by simp only [length_concat]; omega)
          hx (p.concat hz).length le_rfl
        change x • z = z
        simpa only [getVert_length] using hh
  ext x
  change (x : G) • z = z ↔ (x : G) ∈ pathInteriorCore (p.concat hz)
  rw [←he]
  exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩

/-- The full path fixer preserves its actual forward-neighbor complement. -/
theorem pathFixer_preserves_exits {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) :
    ∀ g ∈ pathFixer (X := G) p, ∀ z ∈ pathExits p, g • z ∈ pathExits p := by
  intro g hg z hz
  have hb : g • b = b := by simpa only [getVert_length] using hg p.length le_rfl
  have hp : g • p.penultimate = p.penultimate := hg (p.length-1) (Nat.sub_le _ _)
  refine ⟨?_,?_⟩
  · have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hz.1
    change (graph (family P)).Adj (g • b) (g • z) at hh
    rwa [hb] at hh
  · intro he
    exact hz.2 ((MulAction.toPerm g).injective (he.trans hp.symm))

include h c₀ c₁ hn₀ hn₁ in
/-- A q-fold root-order drop gives transitivity on the actual endpoint complement.
Only extension of the selected path is required, not an implicit tree hypothesis. -/
theorem pathInteriorCore_transitive_exits_of_order_drop
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : p.IsPath) (hlen : 2 ≤ p.length)
    {z : Vertex (family P)} (hz : z ∈ pathExits p) (hznew : z ∉ p.support)
    (hcard : Nat.card (pathInteriorCore p) =
      Nat.card k₀ * Nat.card (pathInteriorCore (p.concat hz.1))) :
    ∀ x ∈ pathExits p, ∃ g ∈ pathInteriorCore p, g • z = x := by
  let := finite_endpoints h
  have hA := pathInteriorCore_le_fixer h p hlen
  have hle : pathInteriorCore p ≤ stabilizer (family P) a := by
    intro g hg
    change g • a = a
    simpa only [getVert_zero] using hA hg 0 (Nat.zero_le _)
  let : Finite (pathInteriorCore p) := Finite.of_injective (inclusion hle) (inclusion_injective _)
  let : Finite ((graph (family P)).neighborSet b) := (graph_locally_finite h b).2
  change (graph (family P)).Adj b z ∧ z ≠ p.penultimate at hz
  let : Finite (pathExits p) := Finite.of_injective
    (fun x : pathExits p => (⟨x,x.property.1⟩ : (graph (family P)).neighborSet b))
    (fun x y he => Subtype.ext (congrArg (fun x : (graph (family P)).neighborSet b => x.val) he))
  have hnewle : pathInteriorCore (p.concat hz.1) ≤ pathInteriorCore p := by
    apply le_iInf
    intro j
    apply le_iInf
    intro hj
    have hh := Finset.mem_Ioo.mp hj
    have hmem : j ∈ Finset.Ioo 0 (p.concat hz.1).length :=
      Finset.mem_Ioo.mpr ⟨hh.1,by simp only [length_concat]; omega⟩
    have hi : pathInteriorCore (p.concat hz.1) ≤ Q (family P) ((p.concat hz.1).getVert j) :=
      iInf_le_of_le j (iInf_le _ hmem)
    simpa only [concat_eq_append,getVert_append',if_pos (Nat.le_of_lt hh.2)] using hi
  apply orbit_covers_of_card (pathInteriorCore p) (pathExits p) z hz
    (fun g hg => pathFixer_preserves_exits p g (hA hg))
  rw [pathExits_card h c₀ c₁ hn₀ hn₁ E₀ p (by intro hn; have := hn.length_eq_zero; omega),
    interior_core_exit_stabilizer h c₀ c₁ hn₀ hn₁ p hp hlen hz.1 hznew,
    Nat.card_congr (subgroupOfEquivOfLe hnewle).toEquiv]
  exact hcard

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
local instance bOneRootActionsAlgebra2 {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include h c₀ c₁ hn₀ hn₁

private theorem interior_core_orders
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) :
    (p.length = 2 → Nat.card (pathInteriorCore p) = Nat.card k₀ ^ 2 * Nat.card (centerIn c₀.actor)) ∧
    (p.length = 3 → Nat.card (pathInteriorCore p) = Nat.card k₀ * Nat.card (centerIn c₀.actor)) ∧
    (p.length = 4 → Nat.card (pathInteriorCore p) = Nat.card (centerIn c₀.actor)) := by
  let T : Sylow 2 (pathFixer (X := G) p) := Classical.choice inferInstance
  have he := pathFixer_sylow_eq_interior h c₀ c₁ hn₀ hn₁ p hp hlen T
  have hc : Nat.card (pathInteriorCore p) = Nat.card T := by
    rw [←he,card_map_of_injective (pathFixer (X := G) p).subtype_injective]
  rw [hc]
  exact short_path_sylow_orders h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp T

/-- Four consecutive interior cores annihilate the root of any path of length at least five. -/
theorem pathInteriorCore_eq_bot_of_five_le
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (hlen : 5 ≤ p.length) : pathInteriorCore p = ⊥ := by
  have hQ (j : ℕ) (hj : 0 < j) (hjl : j < p.length) :
      pathInteriorCore p ≤ Q (family P) (p.getVert j) :=
    iInf_le_of_le j (iInf_le _ (Finset.mem_Ioo.mpr ⟨hj,hjl⟩))
  have hne (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) (hne : i ≠ j) :
      p.getVert i ≠ p.getVert j := fun he => hne (hp.getVert_injOn hi hj he)
  have hc := crossed_cores_disjoint h c₀ c₁ hn₀ hn₁
    (p.adj_getVert_succ (by omega : 1 < p.length))
    (p.adj_getVert_succ (by omega : 2 < p.length))
    (p.adj_getVert_succ (by omega : 3 < p.length))
    (hne 1 3 (by omega) (by omega) (by decide))
    (hne 2 4 (by omega) (by omega) (by decide))
  exact eq_bot_iff.mpr ((le_inf
    (le_inf (hQ 1 (by omega) (by omega)) (hQ 3 (by omega) (by omega)))
    (le_inf (hQ 2 (by omega) (by omega)) (hQ 4 (by omega) (by omega)))).trans hc.le)

/-- The short-path root acts transitively on exits whenever one exit extends the path.
The last step of the order drop occurs precisely in the nontrivial-center branch. -/
theorem short_path_root_transitive_exits
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (hlen : p.length = 2 ∨ p.length = 3 ∨
      (p.length = 4 ∧ Nat.card (centerIn c₀.actor) = Nat.card k₀))
    {z : Vertex (family P)} (hz : z ∈ pathExits p) (hznew : z ∉ p.support) :
    ∀ x ∈ pathExits p, ∃ g ∈ pathInteriorCore p, g • z = x := by
  change (graph (family P)).Adj b z ∧ z ≠ p.penultimate at hz
  have htwo : 2 ≤ p.length := by rcases hlen with h | h | ⟨h,_⟩ <;> omega
  apply pathInteriorCore_transitive_exits_of_order_drop h c₀ c₁ hn₀ hn₁ E₀ p hp htwo hz hznew
  have ho := interior_core_orders h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp htwo
  have ho' := interior_core_orders h c₀ c₁ hn₀ hn₁ E₀ E₁ (p.concat hz.1)
    (hp.concat hznew hz.1) (by simp only [length_concat]; omega)
  rcases hlen with hl | hl | ⟨hl,hc⟩
  · rw [ho.1 hl,ho'.2.1 (by simp only [length_concat,hl])]
    ring
  · rw [ho.2.1 hl,ho'.2.2 (by simp only [length_concat,hl])]
  · rw [ho.2.2 hl,hc,pathInteriorCore_eq_bot_of_five_le h c₀ c₁ hn₀ hn₁
      (p.concat hz.1) (hp.concat hznew hz.1) (by simp [hl]),
      card_eq_one.mpr rfl,mul_one]

/-- Transitivity on the neighbor complement at the terminal vertex. -/
def PathExitTransitive {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) : Prop :=
  ∀ z ∈ pathExits p, ∀ x ∈ pathExits p, ∃ g ∈ pathFixer (X := G) p, g • z = x

/-- DGS regularity requires both actual endpoint complements, not merely oddness of a stabilizer. -/
def PathRegular {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) : Prop :=
  PathExitTransitive p ∧ PathExitTransitive p.reverse

/-- Short source paths are regular by the literal two-core action at both ends. -/
theorem short_path_regular
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (hlen : p.length = 2 ∨ p.length = 3 ∨
      (p.length = 4 ∧ Nat.card (centerIn c₀.actor) = Nat.card k₀)) : PathRegular p := by
  have hf {u v : Vertex (family P)} (t : (graph (family P)).Walk u v) (ht : t.IsPath)
      (hl : t.length = 2 ∨ t.length = 3 ∨
        (t.length = 4 ∧ Nat.card (centerIn c₀.actor) = Nat.card k₀)) : PathExitTransitive t := by
    obtain ⟨y,hy,hynew⟩ := short_path_has_new_exit h c₀ c₁ hn₀ hn₁ E₀ t
      (by rcases hl with h | h | ⟨h,_⟩ <;> omega)
      (by rcases hl with h | h | ⟨h,_⟩ <;> omega)
    have hmove := short_path_root_transitive_exits h c₀ c₁ hn₀ hn₁ E₀ E₁ t ht hl hy hynew
    have hfix := pathInteriorCore_le_fixer h t (by rcases hl with h | h | ⟨h,_⟩ <;> omega)
    intro z hz x hx
    obtain ⟨g,hg,hgz⟩ := hmove z hz
    obtain ⟨a,ha,hax⟩ := hmove x hx
    refine ⟨a*g⁻¹,(pathFixer t).mul_mem (hfix ha) ((pathFixer t).inv_mem (hfix hg)),?_⟩
    rw [mul_smul,←hgz,inv_smul_smul,hax]
  exact ⟨hf p hp hlen,hf p.reverse hp.reverse (by simpa only [length_reverse] using hlen)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
