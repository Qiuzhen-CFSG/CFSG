module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MaximalNormalizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackNormalizer
public import Mathlib.Data.Set.Card

/-!
# Paired neighbors in a normalizer orbit

The index-three part of a normalizer candidate gives transitivity on the
neighbors of the first base vertex. The other local normalizer moves that
vertex, but cannot be transitive: otherwise the normalized overlap would be
trivial. Consequently each intervening vertex pairs exactly two points of
the normalizer orbit. This is the local geometric input to the distance-two
tree in Goldschmidt (5.2), printed p.394.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The actual normalizer orbit used as vertices of the distance-two graph. -/
abbrev normalizerOrbit (F : Bool → Subgroup G) (Q : Subgroup G) : Set (RankTwo.Vertex F) :=
  MulAction.orbit (normalizer (Q : Set G)) (RankTwo.base F false)

private theorem mem_local_fixes (Q : Subgroup G) (i : Bool) {g : G}
    (hg : g ∈ localNormalizer F Q i) : g • RankTwo.base F i = RankTwo.base F i := by
  change g ∈ MulAction.stabilizer G (RankTwo.base F i)
  rw [RankTwo.base, stabilizer_base]
  exact hg.2

private theorem base_adj (i : Bool) :
    (RankTwo.graph F).Adj (RankTwo.base F i) (RankTwo.base F (!i)) :=
  ⟨by change i ≠ !i; cases i <;> decide, incident_base F _ _⟩

theorem normalizer_local_orbit_card (Q : Subgroup G) (i : Bool) :
    Nat.card (MulAction.orbit (localNormalizer F Q i) (RankTwo.base F (!i))) =
      (F false ⊓ F true).relIndex (localNormalizer F Q i) := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  congr 1
  ext g
  change (g:G) • RankTwo.base F (!i) = RankTwo.base F (!i) ↔ (g:G) ∈ F false ⊓ F true
  have hg : (g:G) ∈ F i := g.property.2
  have he : ((g:G) • RankTwo.base F (!i) = RankTwo.base F (!i)) ↔ (g:G) ∈ F (!i) := by
    change (g:G) ∈ MulAction.stabilizer G (RankTwo.base F (!i)) ↔ _
    rw [RankTwo.base, stabilizer_base]
  rw [he]
  cases i
  · exact ⟨fun h => ⟨hg,h⟩,fun h => h.2⟩
  · exact ⟨fun h => ⟨h,hg⟩,fun h => h.1⟩

private theorem local_orbit_subset (Q : Subgroup G) (i : Bool) :
    MulAction.orbit (localNormalizer F Q i) (RankTwo.base F (!i)) ⊆
      (RankTwo.graph F).neighborSet (RankTwo.base F i) := by
  rintro _ ⟨g,rfl⟩
  have he := trackGraphAction.map_adj (g:G) (base_adj (F:=F) i)
  rwa [mem_local_fixes Q i g.property] at he

private theorem local_orbit_eq_neighbors (h : CubicTreeAction F) (Q : Subgroup G) (i : Bool)
    (hi : (F false ⊓ F true).relIndex (localNormalizer F Q i) = 3) :
    MulAction.orbit (localNormalizer F Q i) (RankTwo.base F (!i)) =
      (RankTwo.graph F).neighborSet (RankTwo.base F i) := by
  have hn := h.card_neighbor (RankTwo.base F i)
  have hf : Finite ((RankTwo.graph F).neighborSet (RankTwo.base F i)) :=
    Nat.finite_of_card_ne_zero (by rw [hn]; decide)
  apply Set.eq_of_subset_of_ncard_le (local_orbit_subset Q i)
  · change Nat.card ((RankTwo.graph F).neighborSet (RankTwo.base F i)) ≤ _
    rw [hn]
    change 3 ≤ Nat.card (MulAction.orbit (localNormalizer F Q i) (RankTwo.base F (!i)))
    rw [normalizer_local_orbit_card,hi]

theorem NormalizerCandidate.locally_transitive (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    {x y : RankTwo.Vertex F}
    (hx : (RankTwo.graph F).Adj (RankTwo.base F false) x)
    (hy : (RankTwo.graph F).Adj (RankTwo.base F false) y) :
    ∃ g ∈ localNormalizer F Q false, g • x = y := by
  have he := local_orbit_eq_neighbors h Q false hQ.left_index
  obtain ⟨a,ha⟩ := (he.symm ▸ hx : x ∈ MulAction.orbit (localNormalizer F Q false)
    (RankTwo.base F (!false)))
  obtain ⟨b,hb⟩ := (he.symm ▸ hy : y ∈ MulAction.orbit (localNormalizer F Q false)
    (RankTwo.base F (!false)))
  change (a:G) • RankTwo.base F true = x at ha
  change (b:G) • RankTwo.base F true = y at hb
  refine ⟨(b:G)*(a:G)⁻¹, mul_mem b.property (inv_mem a.property), ?_⟩
  rw [mul_smul,←ha,inv_smul_smul]
  exact hb

private theorem orbit_neighbor_iff (h : CubicTreeAction F) {Q : Subgroup G}
    (hQ : NormalizerCandidate F Q) (z : RankTwo.Vertex F) :
    z ∈ normalizerOrbit F Q ∧ (RankTwo.graph F).Adj (RankTwo.base F true) z ↔
      z ∈ MulAction.orbit (localNormalizer F Q true) (RankTwo.base F false) := by
  constructor
  · rintro ⟨⟨g,hg⟩,hz⟩
    have hga : (g:G) • RankTwo.base F false = z := hg
    have hpre : (RankTwo.graph F).Adj (RankTwo.base F false)
        ((g:G)⁻¹ • RankTwo.base F true) := by
      have he := trackGraphAction.map_adj (g:G)⁻¹ hz.symm
      rwa [←hga,inv_smul_smul] at he
    have hab : (RankTwo.graph F).Adj (RankTwo.base F false) (RankTwo.base F true) :=
      ⟨Bool.false_ne_true,incident_base F _ _⟩
    obtain ⟨a,ha,haβ⟩ := hQ.locally_transitive h hab hpre
    have haα : a • RankTwo.base F false = RankTwo.base F false := by
      change a ∈ MulAction.stabilizer G (RankTwo.base F false)
      rw [RankTwo.base,stabilizer_base]
      exact ha.2
    have hgaβ : ((g:G)*a) • RankTwo.base F true = RankTwo.base F true := by
      rw [mul_smul,haβ,smul_inv_smul]
    have hk : (g:G)*a ∈ localNormalizer F Q true := by
      refine ⟨mul_mem g.property ha.1, ?_⟩
      change (g:G)*a ∈ MulAction.stabilizer G (RankTwo.base F true) at hgaβ
      rw [RankTwo.base,stabilizer_base] at hgaβ
      exact hgaβ
    refine ⟨⟨(g:G)*a,hk⟩,?_⟩
    change ((g:G)*a) • RankTwo.base F false = z
    rw [mul_smul,haα,hga]
  · rintro ⟨g,rfl⟩
    refine ⟨⟨⟨g,g.property.1⟩,rfl⟩,?_⟩
    have he := trackGraphAction.map_adj (g:G)
      (show (RankTwo.graph F).Adj (RankTwo.base F true) (RankTwo.base F false) from
        ⟨by change true ≠ false; decide,incident_base F _ _⟩)
    have hfix : (g:G) • RankTwo.base F true = RankTwo.base F true := by
      change (g:G) ∈ MulAction.stabilizer G (RankTwo.base F true)
      rw [RankTwo.base,stabilizer_base]
      exact g.property.2
    rwa [hfix] at he

private theorem exists_base_pair (h : CubicTreeAction F) {Q : Subgroup G}
    (hQ : NormalizerCandidate F Q) :
    ∃ b ∈ normalizerOrbit F Q, b ≠ RankTwo.base F false ∧
      (RankTwo.graph F).Adj (RankTwo.base F true) b ∧
      ∀ z ∈ normalizerOrbit F Q, (RankTwo.graph F).Adj (RankTwo.base F true) z →
        z = RankTwo.base F false ∨ z = b := by
  classical
  let K := localNormalizer F Q true
  let O := MulAction.orbit K (RankTwo.base F false)
  let : Finite K := h.finite_localNormalizer Q true
  have hcard : O.ncard ≤ 2 := by
    have hle : O.ncard ≤ 3 := by
      have hn := h.card_neighbor (RankTwo.base F true)
      have : Finite ((RankTwo.graph F).neighborSet (RankTwo.base F true)) :=
        Nat.finite_of_card_ne_zero (by rw [hn]; decide)
      have hh := Set.ncard_le_ncard (local_orbit_subset (F:=F) Q true)
        (Set.toFinite ((RankTwo.graph F).neighborSet (RankTwo.base F true)))
      change O.ncard ≤ Nat.card ((RankTwo.graph F).neighborSet (RankTwo.base F true)) at hh
      rwa [hn] at hh
    have hne : O.ncard ≠ 3 := by
      intro he
      apply hQ.nontrivial
      apply h.normalized_overlap_eq_bot_of_local_indices Q hQ.le_overlap hQ.left_index
      have hc := normalizer_local_orbit_card (F:=F) Q true
      change Nat.card O = _ at hc
      exact hc.symm.trans he
    omega
  have hm : ∃ g, g ∈ K ∧ g ∉ F false := by
    by_contra hn
    apply hQ.right_mover
    intro g hg
    by_contra hng
    exact hn ⟨g,hg,hng⟩
  obtain ⟨g,hg,hgnot⟩ := hm
  let b := g • RankTwo.base F false
  have hbO : b ∈ O := ⟨⟨g,hg⟩,rfl⟩
  have hane : RankTwo.base F false ≠ b := by
    intro he
    apply hgnot
    have hf : g ∈ MulAction.stabilizer G (RankTwo.base F false) := he.symm
    simpa only [RankTwo.base,stabilizer_base] using hf
  have haO : RankTwo.base F false ∈ O := MulAction.mem_orbit_self _
  have hpair : O = {RankTwo.base F false,b} := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
      (show O.Finite from Set.finite_range (fun a:K => a • RankTwo.base F false))
    · simpa only [Set.insert_subset_iff,Set.singleton_subset_iff] using And.intro haO hbO
    · rwa [Set.ncard_pair hane]
  have hb := (orbit_neighbor_iff h hQ b).2 hbO
  refine ⟨b,hb.1,hane.symm,hb.2,?_⟩
  intro z hz hβz
  have hzO := (orbit_neighbor_iff h hQ z).1 ⟨hz,hβz⟩
  change z ∈ O at hzO
  rw [hpair] at hzO
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hzO

private theorem orbit_smul_mem {Q : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Q : Set G)) {z : RankTwo.Vertex F}
    (hz : z ∈ normalizerOrbit F Q) : g • z ∈ normalizerOrbit F Q :=
  MulAction.mem_orbit_of_mem_orbit (⟨g,hg⟩ : normalizer (Q:Set G)) hz

theorem NormalizerCandidate.paired_neighbors (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (x : normalizerOrbit F Q) (m : RankTwo.Vertex F)
    (hxm : (RankTwo.graph F).Adj x.val m) :
    ∃! y : normalizerOrbit F Q, y.val ≠ x.val ∧ (RankTwo.graph F).Adj m y.val := by
  classical
  obtain ⟨b,hb,hbne,hβb,hpair⟩ := exists_base_pair h hQ
  obtain ⟨g,hg⟩ := x.property
  have hgα : (g:G) • RankTwo.base F false = x.val := hg
  have hαm : (RankTwo.graph F).Adj (RankTwo.base F false) ((g:G)⁻¹ • m) := by
    have hh := trackGraphAction.map_adj (g:G)⁻¹ hxm
    rwa [←hgα,inv_smul_smul] at hh
  obtain ⟨a,ha,haβ⟩ := hQ.locally_transitive h (base_adj (F:=F) false) hαm
  change a • RankTwo.base F true = (g:G)⁻¹ • m at haβ
  have haα := mem_local_fixes Q false ha
  let k := (g:G)*a
  have hk : k ∈ normalizer (Q:Set G) := mul_mem g.property ha.1
  have hkα : k • RankTwo.base F false = x.val := by rw [mul_smul,haα,hgα]
  have hkβ : k • RankTwo.base F true = m := by rw [mul_smul,haβ,smul_inv_smul]
  let y : normalizerOrbit F Q := ⟨k • b,orbit_smul_mem hk hb⟩
  have hyne : y.val ≠ x.val := by
    rw [←hkα]
    exact fun he => hbne ((MulAction.toPerm k).injective he)
  have hmy : (RankTwo.graph F).Adj m y.val := by
    rw [←hkβ]
    exact trackGraphAction.map_adj k hβb
  refine ⟨y,⟨hyne,hmy⟩,?_⟩
  intro z hz
  have hzO : k⁻¹ • z.val ∈ normalizerOrbit F Q := orbit_smul_mem (inv_mem hk) z.property
  have hβz : (RankTwo.graph F).Adj (RankTwo.base F true) (k⁻¹ • z.val) := by
    have hh := trackGraphAction.map_adj k⁻¹ hz.2
    rwa [←hkβ,inv_smul_smul] at hh
  rcases hpair _ hzO hβz with he | he
  · have hh := congrArg (k • ·) he
    rw [smul_inv_smul,hkα] at hh
    exact (hz.1 hh).elim
  · apply Subtype.ext
    have hh := congrArg (k • ·) he
    rwa [smul_inv_smul] at hh

theorem NormalizerCandidate.orbit_locally_transitive (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (v : normalizerOrbit F Q) {x y : RankTwo.Vertex F}
    (hx : (RankTwo.graph F).Adj v.val x) (hy : (RankTwo.graph F).Adj v.val y) :
    ∃ g ∈ normalizer (Q:Set G), g • v.val = v.val ∧ g • x = y := by
  obtain ⟨a,ha⟩ := v.property
  have haα : (a:G) • RankTwo.base F false = v.val := ha
  have hx' : (RankTwo.graph F).Adj (RankTwo.base F false) ((a:G)⁻¹ • x) := by
    have hh := trackGraphAction.map_adj (a:G)⁻¹ hx
    rwa [←haα,inv_smul_smul] at hh
  have hy' : (RankTwo.graph F).Adj (RankTwo.base F false) ((a:G)⁻¹ • y) := by
    have hh := trackGraphAction.map_adj (a:G)⁻¹ hy
    rwa [←haα,inv_smul_smul] at hh
  obtain ⟨b,hb,hbxy⟩ := hQ.locally_transitive h hx' hy'
  refine ⟨(a:G)*b*(a:G)⁻¹, mul_mem (mul_mem a.property hb.1) (inv_mem a.property), ?_, ?_⟩
  · rw [mul_smul,mul_smul,←haα,inv_smul_smul,mem_local_fixes Q false hb]
  · rw [mul_smul,mul_smul,hbxy,smul_inv_smul]

theorem normalizerOrbit_fixed {Q : Subgroup G} (hQ : Q ≤ F false)
    {g : G} (hg : g ∈ Q) (v : normalizerOrbit F Q) : g • v.val = v.val := by
  obtain ⟨a,ha⟩ := v.property
  change (a:G) • RankTwo.base F false = v.val at ha
  have hc : (a:G)⁻¹*g*(a:G) ∈ Q :=
    (mem_normalizer_iff''.mp a.property g).mp hg
  have hfix : ((a:G)⁻¹*g*(a:G)) • RankTwo.base F false = RankTwo.base F false := by
    change _ ∈ MulAction.stabilizer G (RankTwo.base F false)
    rw [RankTwo.base,stabilizer_base]
    exact hQ hc
  have hh := congrArg ((a:G) • ·) hfix
  simp only [mul_smul,smul_inv_smul] at hh
  rwa [ha] at hh

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
