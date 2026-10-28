module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.WeissEven
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralIntervals
public import Theory.GroupTheory.Amalgam.LocalCover
public import Theory.GroupAction.CubicTree.TrackFixer
public import Mathlib.Data.Set.Card

/-!
# Cubic centralizers and the new-track contradiction

An element of order three in a vertex stabilizer cycles its three neighbors.
Connectedness and faithfulness then kill an element with cubic centralizers
at the two ends of a fixed edge, or at every neighbor of a fixed star.
Applied to the track constructed from commuting local movers, these criteria
are the centralizer endgame of the odd-radius argument.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), consequences
of (2.2)--(2.3), printed pp.379--380, used in (6.11), printed p.402.
-/

@[expose] public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- An actual element of order three cycles the neighbors of its fixed vertex. -/
theorem CubicTreeAction.cubic_neighbor_transitive (h : CubicTreeAction F)
    {a b c : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (hac : (RankTwo.graph F).Adj a c) {x : G}
    (hx : orderOf x=3) (hxa : x • a=a) :
    ∃ y∈zpowers x, y • a=a ∧ y • b=c := by
  let H := RankTwo.stabilizer F a
  let : Finite H := h.finite_stabilizer a
  let E := (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b).subgroupOf H
  let xH : H := ⟨x,hxa⟩
  let X := zpowers xH
  have hE : IsPGroup 2 E := (h.edgeStabilizer_isPGroup hab).comap_subtype
  have hi : E.index=3 := by
    change (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b).relIndex
      (RankTwo.stabilizer F a) = 3
    rw [inf_comm]
    exact h.edge_vertex_relIndex hab.symm
  have hX : Nat.card X=3 := by
    rw [Nat.card_zpowers]
    exact (orderOf_coe xH).symm.trans hx
  have hcomp := three_complement_of_two_group_index_three E X hE hi hX
  obtain ⟨g,hga,hgb⟩ := RankTwo.locally_transitive F hab hac
  obtain ⟨⟨y,t⟩,he,_⟩ := hcomp.existsUnique (⟨g,hga⟩ : H)
  refine ⟨y.val.val, ?_, y.val.property, ?_⟩
  · obtain ⟨k,hk⟩ := y.property
    exact ⟨k,congrArg (fun z:H => (z:G)) hk⟩
  · have he' := congrArg (fun z:H => (z:G)) he
    change y.val.val*t.val.val=g at he'
    have htb : t.val.val • b=b := t.property.2
    rw [← he',mul_smul,htb] at hgb
    exact hgb

/-- Source (2.2): cubic centralizers at every neighbor of a fixed closed star
force the original element to be trivial. -/
theorem CubicTreeAction.eq_one_of_cubic_centralizers_on_star (h : CubicTreeAction F)
    {a : RankTwo.Vertex F} {v : G} (hva : v • a=a)
    (hvn : ∀ b, (RankTwo.graph F).Adj a b → v • b=b)
    (hcube : ∀ b, (RankTwo.graph F).Adj a b → ∃ x:G,
      orderOf x=3 ∧ x • b=b ∧ Commute v x) : v=1 := by
  let C := centralizer ({v}:Set G)
  let S (w : RankTwo.Vertex F) : Prop :=
    (∃ g∈C, g • a=w) ∨
    (∃ b, (RankTwo.graph F).Adj a b ∧ ∃ g∈C, g • b=w)
  have hstep {w z : RankTwo.Vertex F} (hwz : (RankTwo.graph F).Adj w z) : S w → S z := by
    rintro (⟨g,hg,rfl⟩ | ⟨b,hab,g,hg,rfl⟩)
    · right
      refine ⟨g⁻¹ • z, ?_,g,hg,smul_inv_smul g z⟩
      simpa only [inv_smul_smul] using trackGraphAction.map_adj g⁻¹ hwz
    · have hbz : (RankTwo.graph F).Adj b (g⁻¹ • z) := by
        simpa only [inv_smul_smul] using trackGraphAction.map_adj g⁻¹ hwz
      obtain ⟨x,hx,hxb,hvx⟩ := hcube b hab
      obtain ⟨y,hy,hya,hyz⟩ := h.cubic_neighbor_transitive hab.symm hbz hx hxb
      have hyC : y∈C := (zpowers_le.mpr (show x∈C from
        mem_centralizer_singleton_iff.mpr hvx.symm.eq)) hy
      exact .inl ⟨g*y,C.mul_mem hg hyC,by rw [mul_smul,hyz,smul_inv_smul]⟩
  have hall (w : RankTwo.Vertex F) : S w := by
    obtain ⟨p⟩ := h.tree.connected a w
    have hp {b c : RankTwo.Vertex F} (q : (RankTwo.graph F).Walk b c) : S b → S c := by
      induction q with
      | nil => exact id
      | cons hadj q ih => exact fun hb => ih (hstep hadj hb)
    exact hp p (.inl ⟨1,C.one_mem,one_smul G a⟩)
  apply h.action_injective
  ext w
  change v • w=(1:G) • w
  rw [one_smul]
  have hfix {g:G} (hg:g∈C) {b : RankTwo.Vertex F} (hb:v • b=b) :
      v • (g • b)=g • b := by
    have hg' : Commute v g := (mem_centralizer_singleton_iff.mp hg).symm
    rw [← mul_smul,hg'.eq,mul_smul,hb]
  rcases hall w with ⟨g,hg,rfl⟩ | ⟨b,hab,g,hg,rfl⟩
  · exact hfix hg hva
  · exact hfix hg (hvn b hab)

/-- Source (2.3): cubic centralizers at the two endpoints of a fixed edge
force the original element to be trivial. -/
theorem CubicTreeAction.eq_one_of_cubic_centralizers_on_edge (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    {v x y : G} (hva : v • a=a) (hvb : v • b=b)
    (hx : orderOf x=3) (hxa : x • a=a) (hvx : Commute v x)
    (hy : orderOf y=3) (hyb : y • b=b) (hvy : Commute v y) : v=1 := by
  let C := centralizer ({v}:Set G)
  have hf (c : RankTwo.Vertex F) (hac : (RankTwo.graph F).Adj a c) :
      ∃ g∈C, g • a=a ∧ g • b=c := by
    obtain ⟨g,hg,hga,hgb⟩ := h.cubic_neighbor_transitive hab hac hx hxa
    exact ⟨g,(zpowers_le.mpr (show x∈C from
      mem_centralizer_singleton_iff.mpr hvx.symm.eq)) hg,hga,hgb⟩
  apply h.eq_one_of_cubic_centralizers_on_star hva
  · intro c hac
    obtain ⟨g,hg,hga,rfl⟩ := hf c hac
    have hg' : Commute v g := (mem_centralizer_singleton_iff.mp hg).symm
    rw [← mul_smul,hg'.eq,mul_smul,hvb]
  · intro c hac
    obtain ⟨g,hg,hga,rfl⟩ := hf c hac
    refine ⟨g*y*g⁻¹,?_,?_,?_⟩
    · exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).trans hy
    · simp only [mul_smul,inv_smul_smul,hyb]
    · have hg' : Commute v g := (mem_centralizer_singleton_iff.mp hg).symm
      exact (hg'.mul_right hvy).mul_right hg'.inv_right

/-- An index-at-most-two local centralizer contains an actual element of order
three; no ambient finiteness is used. -/
theorem CubicTreeAction.exists_cubic_centralizer_of_index_le_two (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) (v:G)
    (hind : (centralizer ({v}:Set G)).relIndex (RankTwo.stabilizer F a) ≤ 2) :
    ∃ x:G, orderOf x=3 ∧ x • a=a ∧ Commute v x := by
  let H := RankTwo.stabilizer F a
  let : Finite H := h.finite_stabilizer a
  let E := (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b).subgroupOf H
  let C := (centralizer ({v}:Set G)).subgroupOf H
  have hi : E.index=3 := by
    change (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b).relIndex
      (RankTwo.stabilizer F a)=3
    rw [inf_comm]
    exact h.edge_vertex_relIndex hab.symm
  have hd : 3∣Nat.card H := by
    rw [← E.card_mul_index,hi]
    exact dvd_mul_left _ _
  have hn : ¬3∣C.index := by
    intro he
    have hp : 0<C.index := Nat.pos_of_ne_zero C.index_ne_zero_of_finite
    have hh := Nat.le_of_dvd hp he
    change C.index ≤ 2 at hind
    omega
  rw [← C.card_mul_index] at hd
  have hdC : 3∣Nat.card C := (Nat.prime_three.dvd_mul.mp hd).resolve_right hn
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G:=C) 3 hdC
  refine ⟨x.val.val,?_,x.val.property,?_⟩
  · exact (orderOf_coe x.val).trans ((orderOf_coe x).trans hx)
  · exact (mem_centralizer_singleton_iff.mp x.property).symm

/-- The new-track contradiction used in (6.11): commuting movers and the
all-track semilocal cubic witness kill the element fixing their base edge. -/
theorem CubicTreeAction.eq_one_of_commuting_track_movers (h : CubicTreeAction F)
    (htracks : ∀ t : Track (RankTwo.graph F) G, t.fixer≠⊥ →
      ∃ i:Fin 2, ∃ q:G, orderOf q=3 ∧ q∈RankTwo.stabilizer F (t.vertex i) ∧
        q∈centralizer (t.fixer:Set G))
    {a b c : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (hbc : (RankTwo.graph F).Adj b c) (hac : a≠c)
    {v x y : G} (hva : v • a=a) (hvb : v • b=b) (hvc : v • c=c)
    (hvx : Commute v x) (hvy : Commute v y)
    (hxa : x • a=a) (hxb : x • b=b) (hxc : x • c≠c)
    (hyc : y • c=c) (hyb : y • b≠b)
    (hcube : ∃ q:G, orderOf q=3 ∧ q • a=a ∧ Commute v q) : v=1 := by
  let t := localMoversTrack h.tree.isAcyclic trackGraphAction hbc hxb hyc hxc hyb
  have hvQ : v∈t.fixer := by
    apply (t.mem_fixer).mpr
    intro i
    change v • alternatingVertex (y*x) b c i=alternatingVertex (y*x) b c i
    unfold alternatingVertex
    have hτ := hvy.mul_right hvx
    split <;> rw [← mul_smul,(hτ.zpow_right (i/2)).eq,mul_smul]
    · rw [hvb]
    · rw [hvc]
  by_cases hQ : t.fixer=⊥
  · exact Subgroup.mem_bot.mp (hQ ▸ hvQ)
  obtain ⟨q₀,hq₀,hq₀a,hvq₀⟩ := hcube
  obtain ⟨i,q,hq,hqfix,hqC⟩ := htracks t hQ
  have hvq : Commute v q := hqC v hvQ
  fin_cases i
  · have hqb : q • b=b := by
      change q • t.vertex 0=t.vertex 0 at hqfix
      simpa only [t,localMoversTrack_zero] using hqfix
    exact h.eq_one_of_cubic_centralizers_on_edge hab hva hvb hq₀ hq₀a hvq₀ hq hqb hvq
  · have hqc : q • c=c := by
      change q • t.vertex 1=t.vertex 1 at hqfix
      simpa only [t,localMoversTrack_one] using hqfix
    have hbxc : (RankTwo.graph F).Adj b (x • c) := by
      simpa only [hxb] using trackGraphAction.map_adj x hbc
    have haxc : a≠x • c := by
      intro he
      exact hac ((MulAction.toPerm x).injective (hxa.trans he))
    let : Finite ((RankTwo.graph F).neighborSet b) :=
      Nat.finite_of_card_ne_zero (by rw [h.card_neighbor b]; decide)
    have hcover : (RankTwo.graph F).neighborSet b=({a,c,x • c}:Set (RankTwo.Vertex F)) := by
      symm
      apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
      · intro w hw
        rcases hw with rfl | rfl | rfl
        · exact hab.symm
        · exact hbc
        · exact hbxc
      · have h3 : ({a,c,x • c}:Set (RankTwo.Vertex F)).ncard=3 :=
          Set.ncard_eq_three.mpr ⟨a,c,x • c,hac,haxc,hxc.symm,rfl⟩
        rw [h3]
        exact (h.card_neighbor b).le
    apply h.eq_one_of_cubic_centralizers_on_star hvb
    · intro w hw
      change w∈(RankTwo.graph F).neighborSet b at hw
      rw [hcover] at hw
      rcases hw with rfl | rfl | rfl
      · exact hva
      · exact hvc
      · rw [← mul_smul,hvx.eq,mul_smul,hvc]
    · intro w hw
      change w∈(RankTwo.graph F).neighborSet b at hw
      rw [hcover] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨q₀,hq₀,hq₀a,hvq₀⟩
      · exact ⟨q,hq,hqc,hvq⟩
      · refine ⟨x*q*x⁻¹,?_,?_,(hvx.mul_right hvq).mul_right hvx.inv_right⟩
        · exact (orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective q).trans hq
        · simp only [mul_smul,inv_smul_smul,hqc]

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
