module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.PathTransport
public import Theory.GroupAction.RankTwoCosetGeometry.Distance

/-!
# The marked six-step path is a geodesic before smallness

At point distance zero, two, or four, the central long-root labels commute.
For distances two and four this follows from nine-path transitivity and
the actual marked short words. The centered six-step endpoints have a
product of order four, so their involution labels cannot commute. The
explicit six-edge walk and bipartite parity therefore force distance six.
No completion recognition, smallness, or larger girth bound is used.
Source: the final proof of J.4.7, printed p.444, using F.4.6.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
open Subgroup Theory.GroupTheory
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon
open MarkedInverter
variable {K : Type*} [Group K] (q : Completion K)

abbrev basePoint : q.Vertex := base q.family false
abbrev baseLine : q.Vertex := base q.family true
abbrev leftActor : K := q.left leftReflection
abbrev rightActor : K := q.right rightReflection
abbrev centralRoot : K := q.left modelZ

theorem leftActor_fixes_basePoint : leftActor q • basePoint q=basePoint q := by
  change leftActor q ∈ stabilizer q.family (basePoint q)
  simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using
    (show leftActor q ∈ q.family false from ⟨leftReflection,rfl⟩)

private theorem fixes_l : rightActor q • baseLine q=baseLine q := by
  change rightActor q ∈ stabilizer q.family (baseLine q)
  simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using
    (show rightActor q ∈ q.family true from ⟨rightReflection,rfl⟩)

private theorem root_centralized (g : K) (hg : g • basePoint q=basePoint q) : g*centralRoot q*g⁻¹=centralRoot q := by
  have hm : g ∈ q.left.range := by
    have h : g ∈ stabilizer q.family (basePoint q) := hg
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base,Completion.family_false] using h
  have hc := completion_root_centralizes q hm
  change _ ∈ centralizer {q.left (amalgam.left (middleRoot 9))} at hc
  rw [←modelZ_middle] at hc
  exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hc)

private theorem label_eq_of_vertex_eq (g h : K) (he : g • basePoint q=h • basePoint q) :
    g*centralRoot q*g⁻¹=h*centralRoot q*h⁻¹ := by
  have hh : (h⁻¹*g) • basePoint q=basePoint q := by rw [mul_smul,he,inv_smul_smul]
  have hr := root_centralized q (h⁻¹*g) hh
  calc
    g*centralRoot q*g⁻¹ = h*((h⁻¹*g)*centralRoot q*(h⁻¹*g)⁻¹)*h⁻¹ := by group
    _ = h*centralRoot q*h⁻¹ := by rw [hr]

private theorem two_neighbors : HasTwoNeighbors q.graph := by
  intro v w
  obtain ⟨z,hz,hzw,_⟩ := q.thick v w w
  exact ⟨z,hz,hzw⟩

private def twoPath : BasedWalk q.graph 2 (basePoint q) :=
  ⟨⟨baseLine q,alternatingFour_adj0 q.family⟩,
    ⟨⟨rightActor q • basePoint q,alternatingFour_adj1 q.family (rightActor q) ⟨rightReflection,rfl⟩⟩,PUnit.unit⟩⟩

private theorem twoPath_nb : (twoPath q).Nonbacktracking := by
  refine ⟨?_,trivial⟩
  intro he
  have hm : rightActor q ∈ q.left.range := by
    have h : rightActor q ∈ stabilizer q.family (basePoint q) := he
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base,Completion.family_false] using h
  exact completion_right_not_left q hm

private theorem two_distance : q.graph.dist (basePoint q) (rightActor q • basePoint q)=2 :=
  q.short_nonbacktracking_geodesic (twoPath q) (twoPath_nb q) (by decide)

private theorem commute_two : Commute (centralRoot q) ((rightActor q)*centralRoot q*(rightActor q)⁻¹) := by
  have hr (i : ReeTwo.CoreRoot) : q.middle (middleRoot i)=q.right (amalgam.right (middleRoot i)) :=
    DFunLike.congr_fun q.compatible _
  have he : rightActor q*centralRoot q*(rightActor q)⁻¹=q.middle (middleRoot 8) := by
    change q.right rightReflection*q.left modelZ*(q.right rightReflection)⁻¹=_
    rw [modelZ_middle]
    change q.right rightReflection*q.middle (middleRoot 9)*(q.right rightReflection)⁻¹=_
    rw [hr,hr,←map_inv,←map_mul,←map_mul,rightReflection_nine]
  rw [he]
  have hc := completion_root_centralizes q (q.middle_le_left (show q.middle (middleRoot 8)∈q.middle.range from ⟨_,rfl⟩))
  change _ ∈ centralizer {q.left (amalgam.left (middleRoot 9))} at hc
  rw [←modelZ_middle] at hc
  exact (mem_centralizer_singleton_iff.mp hc).symm

private theorem commute_four : Commute (centralRoot q)
    ((completionFourthWord q)*centralRoot q*(completionFourthWord q)⁻¹) := by
  change Commute (q.left modelZ) (_*q.left modelZ*_)
  rw [modelZ_middle]
  change Commute (q.middle (middleRoot 9)) (_*q.middle (middleRoot 9)*_)
  rw [completion_conjugates]
  exact (mem_centralizer_singleton_iff.mp (completion_root_centralizes q
    (q.middle_le_left (show q.middle (middleRootOne^2)∈q.middle.range from ⟨_,rfl⟩)))).symm

private theorem commute_at_distance (n : ℕ) (hn : n≤9) (h : K)
    (hd : q.graph.dist (basePoint q) (h • basePoint q)=n)
    (hc : Commute (centralRoot q) (h*centralRoot q*h⁻¹)) (g : K)
    (hg : q.graph.dist (basePoint q) (g • basePoint q)=n) : Commute (centralRoot q) (g*centralRoot q*g⁻¹) := by
  have ht := ((q.nine_transitive (basePoint q)).mono (two_neighbors q) hn).sphereTransitive q.graphAction q.connected
  obtain ⟨k,hkx,hkg⟩ := ht _ _ hd hg
  have he : (k*h)*centralRoot q*(k*h)⁻¹=g*centralRoot q*g⁻¹ :=
    label_eq_of_vertex_eq q (k*h) g (by simpa only [mul_smul] using hkg)
  have hh := hc.map (MulAut.conj k).toMonoidHom
  have hk := root_centralized q k hkx
  change Commute (k*centralRoot q*k⁻¹) (k*(h*centralRoot q*h⁻¹)*k⁻¹) at hh
  rw [hk] at hh
  have he' : k*(h*centralRoot q*h⁻¹)*k⁻¹=g*centralRoot q*g⁻¹ := by
    calc
      _ = (k*h)*centralRoot q*(k*h)⁻¹ := by group
      _ = _ := he
  rwa [he'] at hh

/-- Long-root labels of source point vertices at distance at most four commute. -/
theorem short_point_labels_commute (g : K)
    (hd : q.graph.dist (basePoint q) (g • basePoint q)≤4) : Commute (centralRoot q) (g*centralRoot q*g⁻¹) := by
  have heven : Even (q.graph.dist (basePoint q) (g • basePoint q)) :=
    (even_dist_iff q.family q.generated _ _).mpr rfl
  have hcases : q.graph.dist (basePoint q) (g • basePoint q)=0 ∨
      q.graph.dist (basePoint q) (g • basePoint q)=2 ∨ q.graph.dist (basePoint q) (g • basePoint q)=4 := by
    obtain ⟨k,hk⟩ := heven
    omega
  rcases hcases with h0|h2|h4
  · have hx : basePoint q=g • basePoint q := q.connected.dist_eq_zero_iff.mp h0
    rw [root_centralized q g hx.symm]
  · exact commute_at_distance q 2 (by decide) (rightActor q) (two_distance q) (commute_two q) g h2
  · exact commute_at_distance q 4 (by decide) (completionFourthWord q)
      (four_point_distance q) (commute_four q) g h4

/-- The actual centered six-edge walk, using the same endpoint words as the commutator. -/
def centeredSixPath : BasedWalk q.graph 6 ((completionLeftWord q) • basePoint q) := by
  have h1 : q.graph.Adj ((leftActor q*rightActor q) • basePoint q) (leftActor q • baseLine q) := by
    have hh := q.graphAction.map_adj (leftActor q) (alternatingFour_adj1 q.family (rightActor q) ⟨rightReflection,rfl⟩).symm
    simpa only [mul_smul] using hh
  have h2 : q.graph.Adj (leftActor q • baseLine q) (basePoint q) := by
    have hh := q.graphAction.map_adj (leftActor q) (alternatingFour_adj0 q.family).symm
    rwa [leftActor_fixes_basePoint q] at hh
  exact ⟨⟨leftActor q • baseLine q,h1⟩,⟨⟨basePoint q,h2⟩,⟨⟨baseLine q,alternatingFour_adj0 q.family⟩,
    ⟨⟨rightActor q • basePoint q,alternatingFour_adj1 q.family (rightActor q) ⟨rightReflection,rfl⟩⟩,
      ⟨⟨(rightActor q*leftActor q) • baseLine q,alternatingFour_adj2 q.family (leftActor q) (rightActor q) ⟨leftReflection,rfl⟩⟩,
        ⟨⟨(rightActor q*leftActor q*rightActor q) • basePoint q,alternatingFour_adj3 q.family (leftActor q) (rightActor q) ⟨rightReflection,rfl⟩⟩,
          PUnit.unit⟩⟩⟩⟩⟩⟩

theorem centeredSixPath_endpoint : (centeredSixPath q).endpoint=completionFourthWord q • basePoint q := rfl

/-- The middle vertex is the original second endpoint. -/
theorem centeredSixPath_middle : (take 3 (by decide) (centeredSixPath q)).endpoint=baseLine q := rfl

/-- The literal centered six-step endpoints are at distance six before smallness. -/
theorem centered_six_distance :
    q.graph.dist (completionLeftWord q • basePoint q) (completionFourthWord q • basePoint q)=6 := by
  have hle : q.graph.dist (completionLeftWord q • basePoint q) (completionFourthWord q • basePoint q)≤6 := by
    have hh := SimpleGraph.dist_le (centeredSixPath q).toWalk
    change q.graph.dist (completionLeftWord q • basePoint q) (completionFourthWord q • basePoint q)≤6 at hh
    exact hh
  have hev : Even (q.graph.dist (completionLeftWord q • basePoint q) (completionFourthWord q • basePoint q)) :=
    (even_dist_iff q.family q.generated _ _).mpr rfl
  by_contra hne
  have hsmall : q.graph.dist (completionLeftWord q • basePoint q) (completionFourthWord q • basePoint q)≤4 := by
    obtain ⟨k,hk⟩ := hev
    omega
  let L := completionLeftWord q
  let R := completionFourthWord q
  have hd : q.graph.dist (basePoint q) ((L⁻¹*R) • basePoint q)≤4 := by
    have he := q.graphAction.dist_smul L⁻¹ (L • basePoint q) (R • basePoint q)
    simp only [←mul_smul,inv_mul_cancel,one_smul] at he
    exact he.symm ▸ hsmall
  have hc := short_point_labels_commute q (L⁻¹*R) hd
  have hm := hc.map (MulAut.conj L).toMonoidHom
  have he : L*((L⁻¹*R)*centralRoot q*(L⁻¹*R)⁻¹)*L⁻¹=R*centralRoot q*R⁻¹ := by group
  change Commute (L*centralRoot q*L⁻¹) (L*((L⁻¹*R)*centralRoot q*(L⁻¹*R)⁻¹)*L⁻¹) at hm
  rw [he] at hm
  have ho : orderOf (centralRoot q)=2 := by
    rw [centralRoot,modelZ_middle]
    exact completion_root_order q
  have hL : (L*centralRoot q*L⁻¹)^2=1 := by
    have hh := (orderOf_eq_prime_iff.mp ho).1
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj L) hh
  have hR : (R*centralRoot q*R⁻¹)^2=1 := by
    have hh := (orderOf_eq_prime_iff.mp ho).1
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj R) hh
  have hp : ((L*centralRoot q*L⁻¹)*(R*centralRoot q*R⁻¹))^2=1 := by rw [hm.mul_pow,hL,hR,one_mul]
  have hfour : orderOf ((L*centralRoot q*L⁻¹)*(R*centralRoot q*R⁻¹))=4 := by
    change orderOf ((completionLeftWord q*q.left modelZ*(completionLeftWord q)⁻¹)*
      (completionFourthWord q*q.left modelZ*(completionFourthWord q)⁻¹))=4
    rw [modelZ_middle]
    change orderOf ((completionLeftWord q*q.middle (middleRoot 9)*(completionLeftWord q)⁻¹)*
      (completionFourthWord q*q.middle (middleRoot 9)*(completionFourthWord q)⁻¹))=4
    rw [completion_conjugates,completion_leftSix_conjugates]
    exact completion_endpoints_product_order q
  have hh := orderOf_dvd_of_pow_eq_one hp
  rw [hfour] at hh
  norm_num at hh

/-- The same displayed six-edge walk has no backtracking. -/
theorem centeredSixPath_nonbacktracking : (centeredSixPath q).Nonbacktracking :=
  nonbacktracking_of_geodesic (centeredSixPath q) (centered_six_distance q)

/-- Every source point pair at distance six has the same order-four root product. -/
theorem six_point_labels_product_order (g : K)
    (hg : q.graph.dist (basePoint q) (g • basePoint q)=6) :
    orderOf (centralRoot q*(g*centralRoot q*g⁻¹))=4 := by
  let L := completionLeftWord q
  let R := completionFourthWord q
  let w := L⁻¹*R
  have hw : q.graph.dist (basePoint q) (w • basePoint q)=6 := by
    have he := q.graphAction.dist_smul L⁻¹ (L • basePoint q) (R • basePoint q)
    simp only [←mul_smul,inv_mul_cancel,one_smul] at he
    exact he.trans (centered_six_distance q)
  have hwo : orderOf (centralRoot q*(w*centralRoot q*w⁻¹))=4 := by
    have he : L*(centralRoot q*(w*centralRoot q*w⁻¹))*L⁻¹=
        (L*centralRoot q*L⁻¹)*(R*centralRoot q*R⁻¹) := by dsimp only [w]; group
    have hh := (MulAut.conj L).orderOf_eq (centralRoot q*(w*centralRoot q*w⁻¹))
    change orderOf (L*(centralRoot q*(w*centralRoot q*w⁻¹))*L⁻¹)=_ at hh
    rw [he] at hh
    apply hh.symm.trans
    change orderOf ((completionLeftWord q*q.left modelZ*(completionLeftWord q)⁻¹)*
      (completionFourthWord q*q.left modelZ*(completionFourthWord q)⁻¹))=4
    rw [modelZ_middle]
    change orderOf ((completionLeftWord q*q.middle (middleRoot 9)*(completionLeftWord q)⁻¹)*
      (completionFourthWord q*q.middle (middleRoot 9)*(completionFourthWord q)⁻¹))=4
    rw [completion_conjugates,completion_leftSix_conjugates]
    exact completion_endpoints_product_order q
  have ht := ((q.nine_transitive (basePoint q)).mono (two_neighbors q) (by decide : 6≤9)).sphereTransitive
    q.graphAction q.connected
  obtain ⟨k,hkx,hkg⟩ := ht _ _ hw hg
  have he := label_eq_of_vertex_eq q (k*w) g (by simpa only [mul_smul] using hkg)
  have hk := root_centralized q k hkx
  have hp : k*(centralRoot q*(w*centralRoot q*w⁻¹))*k⁻¹=centralRoot q*(g*centralRoot q*g⁻¹) := by
    calc
      _ = (k*centralRoot q*k⁻¹)*((k*w)*centralRoot q*(k*w)⁻¹) := by group
      _ = _ := by rw [hk,he]
  have hh := (MulAut.conj k).orderOf_eq (centralRoot q*(w*centralRoot q*w⁻¹))
  change orderOf (k*(centralRoot q*(w*centralRoot q*w⁻¹))*k⁻¹)=_ at hh
  rw [hp] at hh
  exact hh.trans hwo

/-- The order-four assertion is independent of the chosen point representatives. -/
theorem point_pair_product_order_six (g h : K)
    (hd : q.graph.dist (g • basePoint q) (h • basePoint q)=6) :
    orderOf ((g*centralRoot q*g⁻¹)*(h*centralRoot q*h⁻¹))=4 := by
  have he := q.graphAction.dist_smul g⁻¹ (g • basePoint q) (h • basePoint q)
  simp only [←mul_smul,inv_mul_cancel,one_smul] at he
  have ho := six_point_labels_product_order q (g⁻¹*h) (he.trans hd)
  have hh := (MulAut.conj g).orderOf_eq (centralRoot q*((g⁻¹*h)*centralRoot q*(g⁻¹*h)⁻¹))
  have hp : g*(centralRoot q*((g⁻¹*h)*centralRoot q*(g⁻¹*h)⁻¹))*g⁻¹=
      (g*centralRoot q*g⁻¹)*(h*centralRoot q*h⁻¹) := by group
  change orderOf (g*(centralRoot q*((g⁻¹*h)*centralRoot q*(g⁻¹*h)⁻¹))*g⁻¹)=_ at hh
  rw [hp] at hh
  exact hh.trans ho

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
