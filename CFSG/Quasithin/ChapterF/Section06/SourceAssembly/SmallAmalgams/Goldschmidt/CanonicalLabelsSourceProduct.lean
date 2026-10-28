module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceIntervals
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Data.Set.Card

/-!
# The canonical neighbor product from the original source

Goldschmidt (6.8) first excludes central involutions at adjacent vertices:
their product would have a one-edge central block, whereas (6.7) gives two.
The three neighboring labels commute, and equivariance makes their product
central at the middle vertex. The exclusion forces that product to be one.

The source application constructs the actual centered labels and their
neighbor relation. Radius-one exclusion and cyclicity of the edge center
remain separate arguments before `CanonicalLabelSetup` can be assembled.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.8),
printed p.399.
-/

public section
open Subgroup SimpleGraph Theory.GroupTheory
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem eq_one_of_centralizes_adjacent (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) {z : G}
    (hza : z • a = a) (hzb : z • b = b)
    (hca : ∀ g ∈ RankTwo.stabilizer F a, Commute z g)
    (hcb : ∀ g ∈ RankTwo.stabilizer F b, Commute z g) : z = 1 := by
  let C := centralizer ({z} : Set G)
  have ht : C = ⊤ := top_unique (by
    rw [← h.adjacent_stabilizers_generate hab]
    exact sup_le (fun g hg _ hu => by
      obtain rfl := Set.mem_singleton_iff.mp hu
      exact (hca g hg).eq) (fun g hg _ hu => by
      obtain rfl := Set.mem_singleton_iff.mp hu
      exact (hcb g hg).eq))
  exact h.eq_one_of_centralizes_of_fixed_edge
    (fun g => (show g ∈ C from ht ▸ mem_top g) z (Set.mem_singleton z)) hab hza hzb

/-- The two-edge central block excludes involutions central at adjacent
track vertices. This also aligns the central blocks in the cyclic edge-center
argument. -/
theorem no_adjacent_central_involutions_on_track
    (h : LargeTreeSource F s) (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (hwidth : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.centralRight-d.centralLeft=2)
    (a : ℤ) {z w : G}
    (hz : orderOf z = 2) (hw : orderOf w = 2)
    (hzfix : z ∈ t.edgeStabilizer a) (hwfix : w ∈ t.edgeStabilizer a)
    (hzc : ∀ g ∈ RankTwo.stabilizer F (t.vertex a), Commute z g)
    (hwc : ∀ g ∈ RankTwo.stabilizer F (t.vertex (a+1)), Commute w g) : False := by
  let ht := h.action.toCubicTreeAction
  have hzw : Commute z w := hzc w hwfix.1
  have hne : z*w ≠ 1 := by
    intro he
    have hw2 : w*w=1 := by simpa only [pow_two, hw] using pow_orderOf_eq_one w
    have heq : z=w := mul_right_cancel (he.trans hw2.symm)
    have hz1 := eq_one_of_centralizes_adjacent ht (t.adjacent a) hzfix.1 hzfix.2
      hzc (heq ▸ hwc)
    rw [hz1,orderOf_one] at hz
    omega
  have hpow : (z*w)^2=1 := by
    rw [hzw.mul_pow]
    have hzpow : z^2=1 := hz ▸ pow_orderOf_eq_one z
    have hwpow : w^2=1 := hw ▸ pow_orderOf_eq_one w
    rw [hzpow,hwpow,one_mul]
  have hedge : t.CentralEdge (z*w) a := ⟨
    (t.edgeStabilizer a).mul_mem hzfix hwfix,
    fun g hg => (hzc g hg.1).mul_left (hwc g hg.2)⟩
  have hu : t.CentralInvolution (z*w) := ⟨orderOf_eq_prime hpow hne, a, hedge⟩
  obtain ⟨d⟩ := ht.exists_centralInterval_of_not_mem_fixer t (z*w) hu (hfinite _ hu)
  have ha := (ht.centralEdge_iff_in_centralInterval h.five_le h.regular t hu d a).1 hedge
  have hd := hwidth _ hu d
  have hc := ht.centralizes_vertex_of_two_centralEdges (by have := h.five_le; omega)
    h.regular t (d.centralLeft+1)
    (by simpa only [add_sub_cancel_right] using d.central d.centralLeft le_rfl d.central_lt)
    (d.central (d.centralLeft+1) (by omega) (by omega))
  have hcase : d.centralLeft+1=a ∨ d.centralLeft+1=a+1 := by omega
  rcases hcase with he | he
  · rw [he] at hc
    have hwca : ∀ g ∈ RankTwo.stabilizer F (t.vertex a), Commute w g := by
      intro g hg
      have hh := (hzc g hg).inv_left.mul_left (hc g hg)
      simpa only [inv_mul_cancel_left] using hh
    have hw1 := eq_one_of_centralizes_adjacent ht (t.adjacent a) hwfix.1 hwfix.2 hwca hwc
    rw [hw1,orderOf_one] at hw
    omega
  · rw [he] at hc
    have hzcb : ∀ g ∈ RankTwo.stabilizer F (t.vertex (a+1)), Commute z g := by
      intro g hg
      have hh := (hc g hg).mul_left (hwc g hg).inv_left
      simpa only [mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh
    have hz1 := eq_one_of_centralizes_adjacent ht (t.adjacent a) hzfix.1 hzfix.2 hzc hzcb
    rw [hz1,orderOf_one] at hz
    omega

private theorem conjugate_central_vertex
    {a b : RankTwo.Vertex F} {z g : G} (hg : g • a = b)
    (hc : ∀ x ∈ RankTwo.stabilizer F b, Commute z x) :
    ∀ x ∈ RankTwo.stabilizer F a, Commute ((MulAut.conj g⁻¹) z) x := by
  intro x hx
  have hfix : g*x*g⁻¹ ∈ RankTwo.stabilizer F b := by
    change (g*x*g⁻¹) • b = b
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hx, hg]
  have hh := (hc _ hfix).conj g⁻¹
  simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
    mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh

private theorem conjugate_fixed_vertex
    {a b : RankTwo.Vertex F} {z g : G} (hg : g • a = b) (hz : z • b = b) :
    (MulAut.conj g⁻¹) z • a = a := by
  change (g⁻¹*z*(g⁻¹)⁻¹) • a = a
  rw [inv_inv, mul_smul, mul_smul, hg, hz, ← hg, inv_smul_smul]

private theorem no_adjacent_central_involutions_of_track
    (h : LargeTreeSource F s) (t : Track (RankTwo.graph F) G)
    (h0 : t.vertex 0 = RankTwo.base F false) (h1 : t.vertex 1 = RankTwo.base F true)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (hwidth : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.centralRight-d.centralLeft=2)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) {z w : G}
    (hz : orderOf z=2) (hw : orderOf w=2)
    (hzfix : z ∈ RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b)
    (hwfix : w ∈ RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b)
    (hzc : ∀ g ∈ RankTwo.stabilizer F a, Commute z g)
    (hwc : ∀ g ∈ RankTwo.stabilizer F b, Commute w g) : False := by
  have hbase {z w : G} (hz : orderOf z=2) (hw : orderOf w=2)
      (hzfix : z ∈ RankTwo.stabilizer F (RankTwo.base F false) ⊓
        RankTwo.stabilizer F (RankTwo.base F true))
      (hwfix : w ∈ RankTwo.stabilizer F (RankTwo.base F false) ⊓
        RankTwo.stabilizer F (RankTwo.base F true))
      (hzc : ∀ g ∈ RankTwo.stabilizer F (RankTwo.base F false), Commute z g)
      (hwc : ∀ g ∈ RankTwo.stabilizer F (RankTwo.base F true), Commute w g) : False := by
    apply no_adjacent_central_involutions_on_track h t hfinite hwidth 0 hz hw
    · change z ∈ RankTwo.stabilizer F (t.vertex 0) ⊓ RankTwo.stabilizer F (t.vertex 1)
      simpa only [h0,h1] using hzfix
    · change w ∈ RankTwo.stabilizer F (t.vertex 0) ⊓ RankTwo.stabilizer F (t.vertex 1)
      simpa only [h0,h1] using hwfix
    · simpa only [h0] using hzc
    · simpa only [zero_add,h1] using hwc
  obtain ⟨g, ha, hb⟩ := RankTwo.incident_common_translate F hab.2
  let z' := (MulAut.conj g⁻¹) z
  let w' := (MulAut.conj g⁻¹) w
  have hz' : orderOf z'=2 := (orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective z).trans hz
  have hw' : orderOf w'=2 := (orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective w).trans hw
  have hza := conjugate_fixed_vertex ha hzfix.1
  have hzb := conjugate_fixed_vertex hb hzfix.2
  have hwa := conjugate_fixed_vertex ha hwfix.1
  have hwb := conjugate_fixed_vertex hb hwfix.2
  have hcz := conjugate_central_vertex ha hzc
  have hcw := conjugate_central_vertex hb hwc
  have hneq := hab.1
  cases hta : a.type <;> cases htb : b.type
  · exact hneq (hta.trans htb.symm)
  · exact hbase hz' hw' ⟨hta ▸ hza,htb ▸ hzb⟩ ⟨hta ▸ hwa,htb ▸ hwb⟩
      (hta ▸ hcz) (htb ▸ hcw)
  · exact hbase hw' hz' ⟨htb ▸ hwb,hta ▸ hwa⟩ ⟨htb ▸ hzb,hta ▸ hza⟩
      (htb ▸ hcw) (hta ▸ hcz)
  · exact hneq (hta.trans htb.symm)

private theorem source_neighbor_product
    (h : LargeTreeSource F s) (t : Track (RankTwo.graph F) G)
    (h0 : t.vertex 0 = RankTwo.base F false) (h1 : t.vertex 1 = RankTwo.base F true)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (hwidth : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.centralRight-d.centralLeft=2)
    (side : Bool) (f : RankTwo.Vertex F → G)
    (ho : ∀ w, w.type = side → orderOf (f w) = 2)
    (hc : ∀ w, w.type = side → f w ∈ RankTwo.stabilizer F w ∧
      ∀ g ∈ RankTwo.stabilizer F w, Commute (f w) g)
    (hconj : ∀ (g : G) w, w.type = side → f (g • w) = g * f w * g⁻¹)
    (hfix : ∀ w, w.type = side → ∀ x, (RankTwo.graph F).dist w x ≤ 2 → f w • x = x)
    (v u₁ u₂ u₃ : RankTwo.Vertex F)
    (ha : (RankTwo.graph F).Adj v u₁) (hb : (RankTwo.graph F).Adj v u₂)
    (hd : (RankTwo.graph F).Adj v u₃)
    (hab : u₁ ≠ u₂) (had : u₁ ≠ u₃) (hbd : u₂ ≠ u₃)
    (htype : u₁.type = side) : f u₁ * f u₂ * f u₃ = 1 := by
  classical
  let ht := h.action.toCubicTreeAction
  have hside (u : RankTwo.Vertex F) (hu : (RankTwo.graph F).Adj v u) : u.type = side := by
    have hne := hu.1
    have hne' := ha.1
    cases hv : v.type <;> cases hu : u.type <;> cases hu' : u₁.type <;> simp_all
  have hdist (u w : RankTwo.Vertex F) (hu : (RankTwo.graph F).Adj v u)
      (hw : (RankTwo.graph F).Adj v w) : (RankTwo.graph F).dist u w ≤ 2 := by
    calc
      (RankTwo.graph F).dist u w ≤
          (RankTwo.graph F).dist u v + (RankTwo.graph F).dist v w :=
        ht.tree.connected.dist_triangle
      _ = 2 := by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm, SimpleGraph.dist_eq_one_iff_adj.mpr hw]
  have hcomm (u w : RankTwo.Vertex F) (hu : (RankTwo.graph F).Adj v u)
      (hw : (RankTwo.graph F).Adj v w) : Commute (f u) (f w) :=
    (hc u (hside u hu)).2 _ (hfix w (hside w hw) u (hdist w u hw hu))
  have hc12 := hcomm u₁ u₂ ha hb
  have hc13 := hcomm u₁ u₃ ha hd
  have hc23 := hcomm u₂ u₃ hb hd
  have hpow : (f u₁ * f u₂ * f u₃)^2=1 := by
    rw [(hc13.mul_left hc23).mul_pow, hc12.mul_pow,
      show (f u₁)^2=1 from ho u₁ htype ▸ pow_orderOf_eq_one _,
      show (f u₂)^2=1 from ho u₂ (hside u₂ hb) ▸ pow_orderOf_eq_one _,
      show (f u₃)^2=1 from ho u₃ (hside u₃ hd) ▸ pow_orderOf_eq_one _]
    simp only [one_mul]
  have hf : Finite ((RankTwo.graph F).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [ht.card_neighbor v]; decide)
  have hneigh : (RankTwo.graph F).neighborSet v = ({u₁,u₂,u₃} : Set _) := by
    apply (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · intro x hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hd
    · have hn : ((RankTwo.graph F).neighborSet v).ncard=3 := by
        rw [← Nat.card_coe_set_eq]
        exact ht.card_neighbor v
      simp [hn, hab, had, hbd]
  let l := [u₁,u₂,u₃]
  have hmem (x : RankTwo.Vertex F) : x ∈ l ↔ (RankTwo.graph F).Adj v x := by
    change x ∈ l ↔ x ∈ (RankTwo.graph F).neighborSet v
    rw [hneigh]
    simp [l]
  have hn : l.Nodup := by simp [l,hab,had,hbd]
  have hcentral : ∀ g ∈ RankTwo.stabilizer F v, Commute (f u₁ * f u₂ * f u₃) g := by
    intro g hg
    have hp : l.Perm (l.map (g • ·)) := by
      apply (List.perm_ext_iff_of_nodup hn (hn.map (MulAction.toPerm g).injective)).mpr
      intro x
      rw [hmem, List.mem_map]
      constructor
      · intro hx
        refine ⟨g⁻¹ • x, (hmem _).mpr ?_, smul_inv_smul g x⟩
        have hh := trackGraphAction.map_adj g⁻¹ hx
        have hg' : g⁻¹ • v = v := by
          calc
            g⁻¹ • v = g⁻¹ • (g • v) := congrArg (g⁻¹ • ·) hg.symm
            _ = v := inv_smul_smul g v
        simpa only [hg'] using hh
      · rintro ⟨y,hy,rfl⟩
        change (RankTwo.graph F).Adj v (g • y)
        have hh := trackGraphAction.map_adj g ((hmem y).mp hy)
        simpa only [show g • v = v from hg] using hh
    have hprod := (hp.map f).prod_eq' (by simp [l, hc12, hc13, hc23])
    have he : f u₁ * f u₂ * f u₃ = g * (f u₁ * f u₂ * f u₃) * g⁻¹ := by
      simpa [l,hconj g u₁ htype,hconj g u₂ (hside u₂ hb),
        hconj g u₃ (hside u₃ hd), mul_assoc] using hprod
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  by_contra hne
  have hprodorder : orderOf (f u₁ * f u₂ * f u₃)=2 := orderOf_eq_prime hpow hne
  have hfv (u : RankTwo.Vertex F) (hu : (RankTwo.graph F).Adj v u) :
      f u ∈ RankTwo.stabilizer F v := hfix u (hside u hu) v (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm]; omega)
  have hfu (u : RankTwo.Vertex F) (hu : (RankTwo.graph F).Adj v u) :
      f u ∈ RankTwo.stabilizer F u₁ := hfix u (hside u hu) u₁ (hdist u u₁ hu ha)
  exact no_adjacent_central_involutions_of_track h t h0 h1 hfinite hwidth ha
    hprodorder (ho u₁ htype)
    ⟨(RankTwo.stabilizer F v).mul_mem
      ((RankTwo.stabilizer F v).mul_mem (hfv u₁ ha) (hfv u₂ hb)) (hfv u₃ hd),
      (RankTwo.stabilizer F u₁).mul_mem
        ((RankTwo.stabilizer F u₁).mul_mem (hfu u₁ ha) (hfu u₂ hb)) (hfu u₃ hd)⟩
    ⟨hfv u₁ ha,(hc u₁ htype).1⟩ hcentral (hc u₁ htype).2

/-- Goldschmidt (6.8)'s neighbor relation follows from the original large
source, equivariance, and the radius-two fixed balls. -/
theorem LargeTreeSource.neighbor_product
    (h : LargeTreeSource F s) {a : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s a) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := G) p) (ha : a.type = false)
    (side : Bool) (f : RankTwo.Vertex F → G)
    (ho : ∀ w, w.type = side → orderOf (f w) = 2)
    (hc : ∀ w, w.type = side → f w ∈ RankTwo.stabilizer F w ∧
      ∀ g ∈ RankTwo.stabilizer F w, Commute (f w) g)
    (hconj : ∀ (g : G) w, w.type = side → f (g • w) = g * f w * g⁻¹)
    (hfix : ∀ w, w.type = side → ∀ x, (RankTwo.graph F).dist w x ≤ 2 → f w • x = x)
    (v u₁ u₂ u₃ : RankTwo.Vertex F)
    (h₁ : (RankTwo.graph F).Adj v u₁) (h₂ : (RankTwo.graph F).Adj v u₂)
    (h₃ : (RankTwo.graph F).Adj v u₃)
    (h₁₂ : u₁ ≠ u₂) (h₁₃ : u₁ ≠ u₃) (h₂₃ : u₂ ≠ u₃)
    (htype : u₁.type = side) : f u₁ * f u₂ * f u₃ = 1 := by
  let ht := h.action.toCubicTreeAction
  obtain ⟨t,h0,h1,href⟩ := ht.exists_preferred_track
  have hf : ∀ z : G, t.CentralInvolution z → z ∉ t.fixer :=
    ht.centralInvolution_not_mem_trackFixer h.not_cubic h.not_alternating t h0 h1
      h.five_le h.odd h.regular p hp hn ha
  have hw : ∀ z, t.CentralInvolution z → ∀ d : t.CentralInterval z,
      d.centralRight-d.centralLeft=2 := fun z hz d =>
    ht.centralInterval_length_eq_two h.five_le h.regular p hp hn h.not_cubic
      h.not_alternating t hf href hz d
  exact source_neighbor_product h t h0 h1 hf hw side f ho hc hconj hfix
    v u₁ u₂ u₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ htype

/-- Construct the actual centered labels with the neighbor relation proved.
Only radius one and cyclicity of the edge center remain before these data
form `CanonicalLabelSetup`; the product field is no longer a source input. -/
theorem LargeTreeSource.exists_centered_source_labels
    (h : LargeTreeSource F s) {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s v) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := G) p) (hv : v.type = false) :
    ∃ (t : Track (RankTwo.graph F) G) (z : G) (d : t.CentralInterval z)
      (c : ℤ) (r : ℕ) (f : RankTwo.Vertex F → G),
      d.centralLeft = c - 1 ∧ d.centralRight = c + 1 ∧
      d.fixedLeft = c - (r + 1) ∧ d.fixedRight = c + (r + 1) ∧
      (r = 1 ∨ r = 2 ∨ Odd r ∧ 3 ≤ r) ∧ f (t.vertex c) = z ∧
      (∀ w, w.type = (t.vertex c).type → orderOf (f w) = 2) ∧
      (∀ w, w.type = (t.vertex c).type → f w ∈ RankTwo.stabilizer F w ∧
        ∀ g ∈ RankTwo.stabilizer F w, Commute (f w) g) ∧
      (∀ (g : G) w, w.type = (t.vertex c).type → f (g • w) = g * f w * g⁻¹) ∧
      (∀ w, w.type = (t.vertex c).type → ∀ x,
        (RankTwo.graph F).dist w x ≤ r + 1 →
        (RankTwo.graph F).dist w x ≤ s → f w • x = x) ∧
      (∀ w, w.type = (t.vertex c).type → r + 2 ≤ s → ∀ x,
        (RankTwo.graph F).dist w x = r + 2 → f w • x ≠ x) ∧
      (∀ (a u₁ u₂ u₃ : RankTwo.Vertex F),
        (RankTwo.graph F).Adj a u₁ → (RankTwo.graph F).Adj a u₂ →
        (RankTwo.graph F).Adj a u₃ → u₁ ≠ u₂ → u₁ ≠ u₃ → u₂ ≠ u₃ →
        u₁.type = (t.vertex c).type → f u₁ * f u₂ * f u₃ = 1) := by
  let ht := h.action.toCubicTreeAction
  obtain ⟨t,h0,h1,href⟩ := ht.exists_preferred_track
  have hf : ∀ z : G, t.CentralInvolution z → z ∉ t.fixer :=
    ht.centralInvolution_not_mem_trackFixer h.not_cubic h.not_alternating t h0 h1
      h.five_le h.odd h.regular p hp hn hv
  obtain ⟨z,hz⟩ := h.exists_centralInvolution t h0 h1
  obtain ⟨d,c,r,f,hL,hR,hFL,hFR,hr,hz',ho,hc,hconj,hball,hsphere⟩ :=
    ht.exists_centered_interval_labels h.five_le h.regular p hp hn
      h.not_cubic h.not_alternating t hf href hz
  refine ⟨t,z,d,c,r,f,hL,hR,hFL,hFR,hr,hz',ho,hc,hconj,hball,hsphere,?_⟩
  apply h.neighbor_product p hp hn hv (t.vertex c).type f ho hc hconj
  intro w hw x hx
  have hr' : 1 ≤ r := by rcases hr with hr | hr | hr <;> omega
  exact hball w hw x (by omega) (hx.trans (by have := h.five_le; omega))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
