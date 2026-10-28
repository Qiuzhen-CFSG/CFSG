module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCommutator
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralVertexAction
public import Theory.GroupAction.CubicTree.CentralReflection

/-!
# Excluding radius two for an odd fixed interval

An edge-central involution with a one-edge central block and two-vertex
margins gives a nontrivial commutator central at the midpoint between two
marked edges. Four-arc transitivity transports this calculation across a turn.
Applying it in the two orientations puts one commutator in the centers of
adjacent vertex stabilizers. These stabilizers generate the faithful group,
giving a contradiction.

Conjugates retain their marked edge transporters: two transporters agreeing
on the central edge induce the same conjugate. This is the precise meaning of
the source's corresponding conjugates and requires no uniqueness assumption
about the center of an edge stabilizer.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5),
printed p.398, the radius-two exclusion and assertion (*).
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem edge_conjugates_eq (t : Track (RankTwo.graph F) G)
    {z : G} {a : ℤ} (hz : t.CentralEdge z a) {g k : G}
    (h₀ : g • t.vertex a = k • t.vertex a)
    (h₁ : g • t.vertex (a+1) = k • t.vertex (a+1)) :
    (MulAut.conj g) z = (MulAut.conj k) z := by
  have hc := hz.2 (k⁻¹*g) ⟨by
    change (k⁻¹*g) • t.vertex a=t.vertex a
    simp only [mul_smul, h₀, inv_smul_smul], by
    change (k⁻¹*g) • t.vertex (a+1)=t.vertex (a+1)
    simp only [mul_smul, h₁, inv_smul_smul]⟩
  have he : (k⁻¹*g)*z*(k⁻¹*g)⁻¹ = z := by
    rw [← hc.eq, mul_inv_cancel_right]
  change g*z*g⁻¹ = k*z*k⁻¹
  calc
    g*z*g⁻¹ = k*((k⁻¹*g)*z*(k⁻¹*g)⁻¹)*k⁻¹ := by group
    _ = k*z*k⁻¹ := by rw [he]

private theorem central_vertex_conjugate {u g : G} {v : RankTwo.Vertex F}
    (hc : ∀ x ∈ RankTwo.stabilizer F v, Commute u x) :
    ∀ x ∈ RankTwo.stabilizer F (g • v), Commute ((MulAut.conj g) u) x := by
  intro x hx
  have hf : g⁻¹*x*g ∈ RankTwo.stabilizer F v := by
    change (g⁻¹*x*g) • v = v
    have hx' : x • (g • v)=g • v := hx
    simp only [mul_smul, hx', inv_smul_smul]
  have hh := (hc _ hf).conj g
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one,
    MulAut.conj_apply] using hh

private theorem centralInvolution_reverse (t : Track (RankTwo.graph F) G)
    {z : G} (hz : t.CentralInvolution z) : t.reverse.CentralInvolution z := by
  refine ⟨hz.1, ?_⟩
  obtain ⟨i, hi⟩ := hz.2
  refine ⟨-i-1, (Track.centralEdge_reverse_iff t z _).2 ?_⟩
  simpa only [show -(-i-1)-1=i by omega] using hi

private theorem reflected_pair_central (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z)
    (hw : d.centralRight=d.centralLeft+1) (hl : d.leftMargin=2) (hr : d.rightMargin=2)
    (r : G) (href : ∀ i, r • t.vertex i = t.vertex (2*(d.centralLeft+2)-i)) :
    orderOf ⁅z,(MulAut.conj r) z⁆ = 2 ∧
      ⁅z,(MulAut.conj r) z⁆ • t.vertex (d.centralLeft+2) = t.vertex (d.centralLeft+2) ∧
      ∀ g ∈ RankTwo.stabilizer F (t.vertex (d.centralLeft+2)),
        Commute ⁅z,(MulAut.conj r) z⁆ g := by
  let e := d.reflection r (d.centralLeft+2) href
  have hz' := hz.reflection r (d.centralLeft+2) href
  have hlc := d.leftMargin_cast
  have hrc := d.rightMargin_cast
  have hright := h.central_commutator_of_large_residual hs hshort hC hA t hz hz' d e (by
    dsimp only [e, Track.CentralInterval.reflection]
    omega)
  have hleft := h.central_commutator_of_large_residual hs hshort hC hA t.reverse
    (centralInvolution_reverse t hz') (centralInvolution_reverse t hz) e.reverse d.reverse (by
      dsimp only [e, Track.CentralInterval.reverse, Track.CentralInterval.reflection]
      omega)
  have heleft : t.CentralEdge ⁅(MulAut.conj r) z,z⁆ (d.centralLeft+2) := by
    have hh := (Track.centralEdge_reverse_iff t _ _).1 hleft.2
    convert hh using 1
    dsimp only [e, Track.CentralInterval.reverse, Track.CentralInterval.reflection]
    omega
  have heleft' : t.CentralEdge ⁅z,(MulAut.conj r) z⁆ (d.centralLeft+2) := by
    have hh : t.CentralEdge (⁅(MulAut.conj r) z,z⁆⁻¹) (d.centralLeft+2) :=
      ⟨(t.edgeStabilizer _).inv_mem heleft.1, fun a ha => (heleft.2 a ha).inv_left⟩
    simpa only [commutatorElement_inv] using hh
  refine ⟨hright.1, heleft'.fixes_left, ?_⟩
  exact h.centralizes_vertex_of_two_centralEdges (by omega) hshort t (d.centralLeft+2)
    (by convert hright.2 using 1; omega) heleft'

/-- The finite four-arc transport in the assertion (*) of (6.5). The two
involutions are marked conjugates: agreement on the original central edge
identifies their conjugates, without any uniqueness assertion about its center. -/
private theorem commutator_at_turn (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z)
    (hw : d.centralRight=d.centralLeft+1) (hl : d.leftMargin=2) (hr : d.rightMargin=2)
    (r : G) (href : ∀ i, r • t.vertex i = t.vertex (2*(d.centralLeft+2)-i))
    (w : G) (hfix : w • t.vertex (d.centralLeft+2) = t.vertex (d.centralLeft+2))
    (hmove : w • t.vertex (d.centralLeft+1) ≠ t.vertex (d.centralLeft+1)) :
    orderOf ⁅z,(MulAut.conj w) z⁆ = 2 ∧
      ⁅z,(MulAut.conj w) z⁆ • t.vertex (d.centralLeft+2) = t.vertex (d.centralLeft+2) ∧
      ∀ g ∈ RankTwo.stabilizer F (t.vertex (d.centralLeft+2)),
        Commute ⁅z,(MulAut.conj w) z⁆ g := by
  let a := d.centralLeft
  have ha12 : (RankTwo.graph F).Adj (t.vertex (a+1)) (t.vertex (a+2)) := by
    simpa only [show a+1+1=a+2 by omega] using t.adjacent (a+1)
  have ha2w : (RankTwo.graph F).Adj (t.vertex (a+2)) (w • t.vertex (a+1)) := by
    have hf : w • t.vertex (a+2)=t.vertex (a+2) := hfix
    simpa only [hf] using (trackGraphAction.map_adj w ha12).symm
  let q : BasedWalk (RankTwo.graph F) 4 (t.vertex a) :=
    ⟨⟨t.vertex (a+1), t.adjacent a⟩, ⟨⟨t.vertex (a+2), ha12⟩,
      ⟨⟨w • t.vertex (a+1), ha2w⟩,
        ⟨⟨w • t.vertex a, (trackGraphAction.map_adj w (t.adjacent a)).symm⟩,
          PUnit.unit⟩⟩⟩⟩
  have hq : q.Nonbacktracking := by
    refine ⟨?_, hmove, ?_, trivial⟩
    · intro he
      have hh := t.injective he
      omega
    · intro he
      have hh := (MulAction.toPerm w).injective (he.trans hfix.symm)
      have hi := t.injective hh
      omega
  obtain ⟨g,hg⟩ := h.congruent_arcs s hshort (by omega : 4≤s)
    (t.arc a 4) q (t.arc_nonbacktracking _ _) hq rfl
  have hcoords : g • t.vertex a = t.vertex a ∧
      g • t.vertex (a+1) = t.vertex (a+1) ∧
      g • t.vertex (a+2) = t.vertex (a+2) ∧
      g • t.vertex (a+3) = w • t.vertex (a+1) ∧
      g • t.vertex (a+4) = w • t.vertex a := by
    change [g • t.vertex a, g • t.vertex (a+1), g • t.vertex (a+1+1),
      g • t.vertex (a+1+1+1), g • t.vertex (a+1+1+1+1)] =
      [t.vertex a,t.vertex (a+1),t.vertex (a+2),w • t.vertex (a+1),w • t.vertex a] at hg
    simpa only [show a+1+1=a+2 by omega, show a+2+1=a+3 by omega,
      show a+3+1=a+4 by omega, List.cons.injEq, and_true] using hg
  have hzedge := d.central a le_rfl (by dsimp only [a]; omega)
  have hgz : (MulAut.conj g) z=z := by
    exact (edge_conjugates_eq t hzedge (g:=g) (k:=1)
      (by simpa only [one_smul] using hcoords.1)
      (by simpa only [one_smul] using hcoords.2.1)).trans (by simp)
  have hgrz : (MulAut.conj g) ((MulAut.conj r) z)=(MulAut.conj w) z := by
    have he := edge_conjugates_eq t hzedge (g:=g*r) (k:=w)
      (by
        rw [mul_smul, href, show 2*(d.centralLeft+2)-a=a+4 by dsimp only [a]; omega]
        exact hcoords.2.2.2.2)
      (by
        rw [mul_smul, href, show 2*(d.centralLeft+2)-(a+1)=a+3 by dsimp only [a]; omega]
        exact hcoords.2.2.2.1)
    simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using he
  have hu := reflected_pair_central h hs hshort hC hA t hz d hw hl hr r href
  have he : (MulAut.conj g) ⁅z,(MulAut.conj r) z⁆ = ⁅z,(MulAut.conj w) z⁆ := by
    rw [map_commutatorElement, hgz, hgrz]
  refine ⟨?_, ?_, ?_⟩
  · rw [← he]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _).trans hu.1
  · rw [← he]
    change (g*⁅z,(MulAut.conj r) z⁆*g⁻¹) • t.vertex (a+2)=t.vertex (a+2)
    rw [← hcoords.2.2.1, mul_smul, mul_smul, inv_smul_smul, hu.2.1]
  · have hh := central_vertex_conjugate (g:=g) hu.2.2
    rw [he, hcoords.2.2.1] at hh
    exact hh

private theorem commutator_turn_inverse {z w : G} (hz : z^2=1) (hw : w^2=1) :
    ⁅w,(MulAut.conj z) w⁆ = ⁅z,(MulAut.conj w) z⁆⁻¹ := by
  have hzi : z⁻¹=z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz)
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
  simp only [commutatorElement_def, MulAut.conj_apply, mul_inv_rev, hzi, hwi]
  group

/-- The radius-two branch of the odd-fixed-interval argument is impossible.
The same nontrivial commutator centralizes the stabilizers of two adjacent
vertices, which generate the faithful acting group. -/
theorem CubicTreeAction.odd_radius_two_impossible (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G) (href : t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (hw : d.centralRight=d.centralLeft+1) (hl : d.leftMargin=2) (hr : d.rightMargin=2) :
    False := by
  let a := d.centralLeft
  let w := (MulAut.conj (t.translation^(2:ℤ))) z
  let e := d.shift 2
  let er := e.reverse
  have hzw := hz.shift 2
  have hzc := d.leftMargin_cast
  have hzrc := d.rightMargin_cast
  obtain ⟨r,hreflection⟩ := href.exists_center (a+2)
  have hwfix : w • t.vertex (a+2)=t.vertex (a+2) := by
    apply (e.fixed_iff _).2
    dsimp only [e,Track.CentralInterval.shift]
    dsimp only [a] at *
    omega
  have hwmove : w • t.vertex (a+1)≠t.vertex (a+1) := by
    intro hh
    have hm := (e.fixed_iff _).1 hh
    dsimp only [e,Track.CentralInterval.shift] at hm
    dsimp only [a] at *
    omega
  have hu := commutator_at_turn h hs hshort hC hA t hz d hw hl hr
    r hreflection w hwfix hwmove
  obtain ⟨r',hr'⟩ := href.exists_center (-(er.centralLeft+2))
  have hrrev : ∀ i, r' • t.reverse.vertex i =
      t.reverse.vertex (2*(er.centralLeft+2)-i) := by
    intro i
    change r' • t.vertex (-i)=t.vertex (-(2*(er.centralLeft+2)-i))
    rw [hr']
    congr 1
    omega
  have herwidth : er.centralRight=er.centralLeft+1 := by
    dsimp only [er,e,Track.CentralInterval.reverse,Track.CentralInterval.shift]
    omega
  have herleft : er.leftMargin=2 := by
    have hh : (er.leftMargin:ℤ)=d.fixedRight-d.centralRight := by
      rw [er.leftMargin_cast]
      dsimp only [er,e,Track.CentralInterval.reverse,Track.CentralInterval.shift]
      omega
    omega
  have herright : er.rightMargin=2 := by
    have hh : (er.rightMargin:ℤ)=d.centralLeft-d.fixedLeft := by
      rw [er.rightMargin_cast]
      dsimp only [er,e,Track.CentralInterval.reverse,Track.CentralInterval.shift]
      omega
    omega
  have hemid : -(er.centralLeft+2)=a+3 := by
    dsimp only [er,e,Track.CentralInterval.reverse,Track.CentralInterval.shift,a]
    omega
  have henext : -(er.centralLeft+1)=a+4 := by
    dsimp only [er,e,Track.CentralInterval.reverse,Track.CentralInterval.shift,a]
    omega
  have hzfix : z • t.reverse.vertex (er.centralLeft+2)=t.reverse.vertex (er.centralLeft+2) := by
    change z • t.vertex (-(er.centralLeft+2))=t.vertex (-(er.centralLeft+2))
    rw [hemid]
    apply (d.fixed_iff _).2
    dsimp only [a] at *
    omega
  have hzmove : z • t.reverse.vertex (er.centralLeft+1)≠t.reverse.vertex (er.centralLeft+1) := by
    change z • t.vertex (-(er.centralLeft+1))≠t.vertex (-(er.centralLeft+1))
    rw [henext]
    intro hh
    have hm := (d.fixed_iff _).1 hh
    dsimp only [a] at *
    omega
  have hu' := commutator_at_turn h hs hshort hC hA t.reverse
    (centralInvolution_reverse t hzw) er herwidth herleft herright r' hrrev z hzfix hzmove
  have hzinv : z^2=1 := by rw [← hz.1]; exact pow_orderOf_eq_one z
  have hwinv : w^2=1 := by rw [← hzw.1]; exact pow_orderOf_eq_one w
  have hident := commutator_turn_inverse hzinv hwinv
  rw [hident] at hu'
  change _ ∧ _ • t.vertex (-(er.centralLeft+2))=t.vertex (-(er.centralLeft+2)) ∧
    ∀ g ∈ RankTwo.stabilizer F (t.vertex (-(er.centralLeft+2))), _ at hu'
  rw [hemid] at hu'
  let u := ⁅z,(MulAut.conj w) z⁆
  have hur : u • t.vertex (a+3)=t.vertex (a+3) := by
    have hh := congrArg (u • ·) hu'.2.1
    simpa only [u,smul_inv_smul] using hh.symm
  have hcr : ∀ g ∈ RankTwo.stabilizer F (t.vertex (a+3)), Commute u g := by
    intro g hg
    simpa only [inv_inv] using (hu'.2.2 g hg).inv_left
  have hadj : (RankTwo.graph F).Adj (t.vertex (a+2)) (t.vertex (a+3)) := by
    simpa only [show a+2+1=a+3 by omega] using t.adjacent (a+2)
  let C := centralizer ({u} : Set G)
  have hle : RankTwo.stabilizer F (t.vertex (a+2)) ⊔
      RankTwo.stabilizer F (t.vertex (a+3)) ≤ C := by
    apply sup_le
    · intro g hg v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      exact (hu.2.2 g hg).eq
    · intro g hg v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      exact (hcr g hg).eq
  have htop : C=⊤ := top_unique (by rwa [h.adjacent_stabilizers_generate hadj] at hle)
  have huone : u=1 := h.eq_one_of_centralizes_of_fixed_edge (fun g => by
    have hg : g∈C := by rw [htop]; trivial
    exact hg u (Set.mem_singleton u)) hadj hu.2.1 hur
  have horder : orderOf u=2 := hu.1
  simp only [huone,orderOf_one] at horder
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
