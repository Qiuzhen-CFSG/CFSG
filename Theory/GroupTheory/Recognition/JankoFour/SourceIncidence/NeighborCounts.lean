module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.RadicalActions
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.TriangleSymmetry
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LinePermutations

/-!
# The two coplanar neighbor counts

For label two, the radical stabilizer is transitive on the four other points
of the second line. The three plane point–line types ensure at least one of
those points neighbors the chosen first-line point, so all five do.
A realized three-neighbor plane configuration consequently has label one:
label zero gives four neighbors and label two gives five. The simultaneous
line orbital action and the radical's four-point action transport that
configuration to every label-one pair, giving exactly three neighbors.

This proves the last two neighbor-count fields of the unchanged Input.
It uses the literal charts and existing plane orbits, with no new finite
catalogue, marking assumption or geometric callback.

Source: Aschbacher–Segev (1991), (5.4)(3)–(4), p.600.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

private theorem line_neighbor_card_of_incident (y : Point a.P) (k : Line a.L)
    (hy : OnLine a.L y k) : {u | OnLine a.L u k ∧ Adj a.L y u}.ncard = 4 := by
  have he : {u | OnLine a.L u k ∧ Adj a.L y u} = {u | OnLine a.L u k} \ {y} := by
    ext u
    constructor
    · rintro ⟨hu,ha⟩; exact ⟨hu,fun he => ha.1 he.symm⟩
    · rintro ⟨hu,hne⟩; exact ⟨hu,fun he => hne he.symm,k,hy,hu⟩
  rw [he,Set.ncard_sdiff_singleton_of_mem (s := {u : Point a.P | OnLine a.L u k}) (a := y) hy,a.line_card]

private theorem neighbor_count_smul (g : G) (y : Point a.P) (k : Line a.L) :
    {u | OnLine a.L u (g • k) ∧ Adj a.L (g • y) u}.ncard =
      {u | OnLine a.L u k ∧ Adj a.L y u}.ncard := by
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
  symm
  apply Nat.card_congr ((MulAction.toPerm g).subtypeEquiv _)
  intro u
  change (OnLine a.L u k ∧ Adj a.L y u) ↔
    (OnLine a.L (g • u) (g • k) ∧ Adj a.L (g • y) (g • u))
  constructor
  · rintro ⟨hu,ha⟩; exact ⟨incident_smul g hu,adj_smul g ha⟩
  · rintro ⟨hu,ha⟩
    exact ⟨by simpa only [OnLine,inv_smul_smul] using incident_smul g⁻¹ hu,
      by simpa only [inv_smul_smul] using adj_smul g⁻¹ ha⟩

private theorem neighbor_exists_other (y x : Point a.P) (k : Line a.L)
    (hc : {u | OnLine a.L u k ∧ Adj a.L y u}.ncard = 3) :
    ∃ u, OnLine a.L u k ∧ Adj a.L y u ∧ u ≠ x := by
  by_contra hn
  have hs : {u | OnLine a.L u k ∧ Adj a.L y u} ⊆ {x} := by
    intro u hu
    by_contra hne
    exact hn ⟨u,hu.1,hu.2,hne⟩
  have hh := Set.ncard_le_ncard hs
  rw [hc,Set.ncard_singleton] at hh
  omega

private theorem distinct_line_of_positive_type (x : Point a.P) (l k : Line a.L)
    (i : Fin 5) (hi : 0 < i.val) (ht : LineType a.residueChart i x l k) : l ≠ k := by
  intro he
  have hzero := (a.delta_zero x l k).mpr ⟨(lineType_incident ht).1,he.symm⟩
  obtain ⟨j,hj,huniq⟩ := a.orbital_partition x l k (lineType_incident ht).1 (lineType_incident ht).2
  have hij : i = 0 := (huniq i ht).trans (huniq 0 hzero).symm
  subst i
  exact Nat.lt_irrefl 0 hi

/-- AS91 (5.4)(4): all five points of a label-two line neighbor the chosen
other point of the first line. The radical stabilizer and the three plane
pair types determine the count. -/
theorem delta_two_neighbors (x y : Point a.P) (l k : Line a.L)
    (hxl : OnLine a.L x l) (hyl : OnLine a.L y l) (hyx : y ≠ x)
    (ht : LineType a.residueChart 2 x l k) :
    ∀ u, OnLine a.L u k → Adj a.L y u := by
  have hxk := (lineType_incident ht).2
  obtain ⟨π,hlπ,hkπ⟩ := (a.delta_coplanar x l k hxl hxk).mpr ⟨2,by decide,ht⟩
  have hyπ := a.string y l π hyl hlπ
  have hyn : ¬ OnLine a.L y k := by
    intro hyk
    obtain ⟨m,hm,huniq⟩ := a.unique_line x y ⟨hyx.symm,l,hxl,hyl⟩
    exact a.distinct_line_of_positive_type x l k 2 (by decide) ht
      ((huniq l ⟨hxl,hyl⟩).trans (huniq k ⟨hxk,hyk⟩).symm)
  obtain ⟨i,hi⟩ := a.plane_pair_types π y k hyπ hkπ
  fin_cases i
  · exact (hyn hi).elim
  · exact hi
  · have hc : {u | OnLine a.L u k ∧ Adj a.L y u}.ncard = 3 := hi
    obtain ⟨v,hvk,hyv,hvx⟩ := a.neighbor_exists_other y x k hc
    intro u hu
    by_cases hux : u = x
    · subst u
      exact ⟨hyx,l,hyl,hxl⟩
    · obtain ⟨e,hey,hev⟩ := a.core_stabilizer_transitive x y l k 2 hxl hyl hyx
        (by decide) ht v u hvk hvx hu hux
      simpa only [hey,hev] using adj_smul (e : G) hyv

private theorem exists_label_one_count :
    ∃ (x y : Point a.P) (l k : Line a.L), OnLine a.L x l ∧ OnLine a.L y l ∧ y ≠ x ∧
      LineType a.residueChart 1 x l k ∧ {u | OnLine a.L u k ∧ Adj a.L y u}.ncard = 3 := by
  let y := Cosets.vertex a.P.M 1
  let π := Cosets.vertex (centralizer z) 1
  obtain ⟨k,hkπ,hcount⟩ := a.plane_pair_types_realized π y ⟨1,rfl,rfl⟩ 2
  have hc : {u | OnLine a.L u k ∧ Adj a.L y u}.ncard = 3 := hcount
  obtain ⟨x,hxk,hyx⟩ := (Set.ncard_pos (s := {u | OnLine a.L u k ∧ Adj a.L y u})).mp (show 0 < {u | OnLine a.L u k ∧ Adj a.L y u}.ncard by omega)
  obtain ⟨l,hyl,hxl⟩ := hyx.2
  have hlπ := a.plane_closed y x l π hyx.1 hyl hxl ⟨1,rfl,rfl⟩ (a.string x k π hxk hkπ)
  obtain ⟨i,hi,ht⟩ := (a.delta_coplanar x l k hxl hxk).mp ⟨π,hlπ,hkπ⟩
  have hone : i = 1 := by
    fin_cases i
    · have he := ((a.delta_zero x l k).mp ht).2
      have hh := a.line_neighbor_card_of_incident y k (he.symm ▸ hyl)
      omega
    · rfl
    · have hall := a.delta_two_neighbors x y l k hxl hyl hyx.1 ht
      have he : {u | OnLine a.L u k ∧ Adj a.L y u} = {u | OnLine a.L u k} :=
        Set.ext (fun u => ⟨And.left,fun hu => ⟨hu,hall u hu⟩⟩)
      rw [he,a.line_card] at hc
      omega
    · norm_num at hi
    · norm_num at hi
  exact ⟨x,y,l,k,hxl,hyl,hyx.1,hone ▸ ht,hc⟩

private theorem configuration_transitive
    (x y u v : Point a.P) (l k m n : Line a.L) (i : Fin 5)
    (hxl : OnLine a.L x l) (hyl : OnLine a.L y l) (hyx : y ≠ x)
    (hum : OnLine a.L u m) (hvm : OnLine a.L v m) (hvu : v ≠ u)
    (ht : LineType a.residueChart i x l k) (hs : LineType a.residueChart i u m n) :
    ∃ g : G, g • x = u ∧ g • y = v ∧ g • l = m ∧ g • k = n := by
  obtain ⟨r,hrx,hrl⟩ := hxl
  have hum' := hum
  obtain ⟨s,hsu,hsm⟩ := hum
  let g := s*r⁻¹
  have hgx : g • x = u := by rw [←hrx,Cosets.smul_vertex]; simpa only [g,inv_mul_cancel_right] using hsu
  have hgl : g • l = m := by rw [←hrl,Cosets.smul_vertex]; simpa only [g,inv_mul_cancel_right] using hsm
  have ht' : LineType a.residueChart i u m (g • k) := by
    simpa only [hgx,hgl] using lineType_smul g ht
  obtain ⟨f,hfu,hfm,hfk⟩ := a.orbital_transitive u m (g • k) n i ht' hs
  have hfgx : (f*g) • x = u := by rw [mul_smul,hgx,hfu]
  have hfgl : (f*g) • l = m := by rw [mul_smul,hgl,hfm]
  have hfgk : (f*g) • k = n := by rw [mul_smul,hfk]
  have hfgy : OnLine a.L ((f*g) • y) m := by
    have hh := incident_smul (f*g) hyl
    rw [hfgl] at hh
    exact hh
  have hfgyne : (f*g) • y ≠ u := by
    rw [←hfgx]; exact (MulAction.injective (f*g)).ne hyx
  obtain ⟨e,he⟩ := a.core_transitive_other u m hum' ((f*g) • y) v hfgy hfgyne hvm hvu
  exact ⟨(e : G)*(f*g),by rw [mul_smul,hfgx]; exact coreAt_le_stabilizer a.P u e.property,
    by rw [mul_smul,he],by rw [mul_smul,hfgl]; exact a.core_fixes_lines u e m hum',
    by rw [mul_smul,hfgk]; exact a.core_fixes_lines u e n (lineType_incident hs).2⟩

/-- AS91 (5.4)(3): exactly three points of a label-one line neighbor the
chosen other point of the first line. A realized plane configuration fixes
the label, and the original stabilizers transport its actual neighbor set. -/
theorem delta_one_neighbors (x y : Point a.P) (l k : Line a.L)
    (hxl : OnLine a.L x l) (hyl : OnLine a.L y l) (hyx : y ≠ x)
    (ht : LineType a.residueChart 1 x l k) :
    {u | OnLine a.L u k ∧ Adj a.L y u}.ncard = 3 := by
  obtain ⟨u,v,m,n,hum,hvm,hvu,hs,hc⟩ := a.exists_label_one_count
  obtain ⟨g,hgu,hgv,hgm,hgn⟩ := a.configuration_transitive u v x y m n l k 1
    hum hvm hvu hxl hyl hyx hs ht
  rw [←hgv,←hgn,a.neighbor_count_smul,hc]
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
