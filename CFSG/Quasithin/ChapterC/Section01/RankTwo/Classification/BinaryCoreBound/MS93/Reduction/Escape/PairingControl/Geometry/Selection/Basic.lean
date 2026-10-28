module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure

/-!
# Path and fixed-point deductions for MS93 (4.3.2)(4)--(5)

A six-step contrary path has actual vertices at positions one, two and five;
the stored predecessor is position four. The tree's unique geodesic makes
these choices compatible with any `CentralizerChoice`, including its
position-three vertex. Minimality of the critical distance excludes containment
of Z_alpha in the product of the Z-layers at positions two and four.

The local fixed preimage B is normal in its vertex stabilizer. If Z_alpha
lies in Z_(alpha+4) B_(alpha+2), this produces the literal x and y on p.884
with xy in B_(alpha+2) outside Z_(alpha+2). The element xy is an involution.
The actual irreducible natural U, of order eight, has no nontrivial normal
subgroup inside an incident edge displacement, whose order is at most four.
For an element of B, its commutator with Q is normalized by the local
residual. These facts prove the terminal contradiction from the three local
containments in the complementary b = 6 branch.

The changed critical-path selection and the (1.7)(ii) application in the
other b = 6 branch are not proved here. Nor are the three containment
premises of `SixPath.false_of_fixed_cover` assumed to follow automatically.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.2)(4)--(5), printed pp.884--885.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

theorem fixedPreimage_normalized [Finite M] (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    stabilizer R a ≤ normalizer (B R a (geometry.Z_normal a) : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (B R a (geometry.Z_normal a)).map (MulAut.conj g).toMonoidHom = _
  have h := FirstPairing.B_act hb g⁻¹ a ha
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

/-- The three additional vertices needed in the b = 6 argument. All lie on
this counterexample's original critical path; no endpoints are identified WLOG. -/
structure SixPath (p : Counterexample geometry) where
  six : geometry.b R = 6
  first : Vertex R
  middle : Vertex R
  last : Vertex R
  first_before : Before p.a p.a' first 5
  middle_before : Before p.a p.a' middle 4
  last_before : Before p.a p.a' last 1

/-- Choose the actual shortest-path vertices in the b = 6 case. -/
noncomputable def sixPath (p : Counterexample geometry) (h : geometry.b R = 6) :
    SixPath p := by
  classical
  let f := p.exists_before (show 5 ≤ geometry.b R by omega)
  let s := p.exists_before (show 4 ≤ geometry.b R by omega)
  let t := p.exists_before (show 1 ≤ geometry.b R by omega)
  exact ⟨h, f.choose, s.choose, t.choose, f.choose_spec, s.choose_spec, t.choose_spec⟩

namespace SixPath
variable {p : Counterexample geometry} (path : SixPath p)

theorem middle_before_start : Before p.a' p.a path.middle 2 := by
  have h := before_reverse path.middle_before
  simpa only [p.distance_eq_b, path.six] using h

theorem first_before_start : Before p.a' p.a path.first 1 := by
  have h := before_reverse path.first_before
  simpa only [p.distance_eq_b, path.six] using h

theorem start_first_adjacent : Adjacent R p.a path.first :=
  path.first_before_start.endpoint_adjacent

theorem first_middle_adjacent : Adjacent R path.first path.middle :=
  path.first_before.adjacent (geometry := geometry) path.middle_before

theorem middle_choice_adjacent (choice : CentralizerChoice p) :
    Adjacent R path.middle choice.t :=
  path.middle_before.adjacent (geometry := geometry) choice.before

theorem choice_predecessor_adjacent (choice : CentralizerChoice p) :
    Adjacent R choice.t p.c :=
  choice.before.adjacent (geometry := geometry) p.before

theorem predecessor_last_adjacent : Adjacent R p.c path.last :=
  p.before.adjacent (geometry := geometry) path.last_before

theorem last_end_adjacent : Adjacent R path.last p.a' :=
  adjacent_symm R path.last_before.endpoint_adjacent

theorem start_middle_distance : (cosetGraph R).dist p.a path.middle = 2 := by
  rw [SimpleGraph.dist_comm]
  exact path.middle_before_start.1

theorem middle_predecessor_distance : (cosetGraph R).dist path.middle p.c = 2 :=
  before_distance (geometry := geometry) path.middle_before p.before (by decide)

variable [Finite M]

theorem middle_color : color R path.middle = false :=
  (path.middle_before.color (by decide)).trans p.end_color

theorem middle_Z_le_end_kernel : Z R path.middle ≤ Q R p.a' := by
  apply Z_le_Q_of_dist_lt R path.middle (geometry.exists_critical _ path.middle_color)
  rw [geometry.distance_constant _ path.middle_color, path.middle_before.1]
  change 4 < geometry.b R
  rw [path.six]
  decide

include path in
theorem predecessor_Z_le_end_kernel : Z R p.c ≤ Q R p.a' := by
  apply Z_le_Q_of_dist_lt R p.c (geometry.exists_critical _ p.before_color)
  rw [geometry.distance_constant _ p.before_color, p.before.1]
  change 2 < geometry.b R
  rw [path.six]
  decide

theorem start_Z_not_le_middle_sup_predecessor :
    ¬ Z R p.a ≤ Z R path.middle ⊔ Z R p.c :=
  fun h => p.critical.2
    (h.trans (sup_le path.middle_Z_le_end_kernel path.predecessor_Z_le_end_kernel))

omit [Finite M] in
theorem start_V_le_middle_kernel : V R p.a ≤ Q R path.middle :=
  V_le_Q_of_distance p.color_a (by rw [path.start_middle_distance, path.six]; decide)

theorem predecessor_V_le_middle_kernel : V R p.c ≤ Q R path.middle := by
  apply V_le_Q_of_distance p.before_color
  rw [SimpleGraph.dist_comm, path.middle_predecessor_distance, path.six]
  decide

omit [Finite M] in
theorem start_Z_le_middle_V : Z R p.a ≤ V R path.middle :=
  le_iSup_of_le p.a (le_iSup_of_le path.start_middle_distance.le le_rfl)

/-- The element selection at the end of printed p.884, with the source
product containment still explicit. Normality is only in the middle stabilizer. -/
theorem exists_product_in_fixed_not_Z
    (hcover : Z R p.a ≤ Z R p.c ⊔ B R path.middle (geometry.Z_normal path.middle)) :
    ∃ x ∈ Z R p.a, ∃ y ∈ Z R p.c,
      x * y ∈ B R path.middle (geometry.Z_normal path.middle) ∧
      x * y ∉ Z R path.middle := by
  obtain ⟨x, hx, hout⟩ := SetLike.not_le_iff_exists.mp
    path.start_Z_not_le_middle_sup_predecessor
  have hnorm : Z R p.c ≤
      normalizer (B R path.middle (geometry.Z_normal path.middle) : Set (FreeAmalgam R)) :=
    ((Z_le_VBall R p.c 2).trans path.predecessor_V_le_middle_kernel).trans
      ((show Q R path.middle ≤ stabilizer R path.middle from fun _ hz => hz.1).trans
        (fixedPreimage_normalized (by rw [path.six]; decide) _ path.middle_color))
  have hxprod : x ∈ B R path.middle (geometry.Z_normal path.middle) ⊔ Z R p.c := by
    rw [sup_comm]
    exact hcover hx
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hnorm] at hxprod
  obtain ⟨b, hb, c, hc, hbc⟩ := hxprod
  change b ∈ B R path.middle (geometry.Z_normal path.middle) at hb
  refine ⟨x, hx, c⁻¹, (Z R p.c).inv_mem hc, ?_, ?_⟩
  · simpa only [← hbc, mul_inv_cancel_right] using hb
  · intro h
    apply hout
    have hh := (Z R path.middle ⊔ Z R p.c).mul_mem (mem_sup_left h) (mem_sup_right hc)
    simpa only [inv_mul_cancel_right] using hh

end SixPath

variable [Finite M]

/-- Irreducibility of the actual natural eight-group excludes a nonzero
normal subgroup in an incident displacement of order at most four. -/
theorem edge_normal_subgroup_eq_bot (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ edgeDisplacement a t)
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R))) : K = ⊥ := by
  obtain ⟨o⟩ := facts.opposite a ha
  have hKU := hK.trans (Initial.edge_le_natural source a t ha hat)
  have hUG := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hKG := hKU.trans hUG
  let : (K.subgroupOf (stabilizer R a)).Normal := normal_subgroupOf_of_le_normalizer hn
  have him : (⊤ : Subgroup (stabilizer R a)).map o.projection = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr o.surjective
  rcases o.naturalU.irreducible him (K.subgroupOf (stabilizer R a))
    (fun _ hx => hKU hx) le_normalizer_of_normal with h | h
  · have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
    simpa only [map_subgroupOf_eq_of_le hKG, Subgroup.map_bot] using hh
  · have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
    have heq : K = U R a := by
      simpa only [map_subgroupOf_eq_of_le hKG, map_subgroupOf_eq_of_le hUG] using hh
    have hUedge : U R a ≤ edgeDisplacement a t := heq ▸ hK
    let := finite_stabilizer R a
    let : Finite (edgeDisplacement a t) := Finite.of_injective
      (inclusion ((Initial.edge_le_natural source a t ha hat).trans hUG))
      (inclusion_injective _)
    have hcard := Nat.card_le_card_of_injective (inclusion hUedge) (inclusion_injective _)
    have hsmall := Initial.edge_card_le_four source hb modules a t ha hat
    rw [modules.natural.card_at a ha] at hcard
    omega

theorem mem_Z_of_normalized_edge_commutator (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    {x : FreeAmalgam R} (hx : x ∈ Q R a) (hsquare : x ^ 2 = 1)
    (hbound : ⁅zpowers x, Q R a⁆ ≤ edgeDisplacement a t)
    (hn : Ltilde R a ≤ normalizer ((⁅zpowers x, Q R a⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    x ∈ Z R a := by
  have hnorm : stabilizer R a ≤ normalizer ((⁅zpowers x, Q R a⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    rw [← source.local_generation a ha]
    exact sup_le hn (normalizer_commutator_ge_right _ _)
  have hbot := edge_normal_subgroup_eq_bot source hb modules facts ha hat _ hbound hnorm
  have hc := commutator_eq_bot_iff_le_centralizer.mp hbot (mem_zpowers x)
  rw [← modules.X_eq_Z a ha]
  exact mem_omegaCenter_iff.mpr ⟨hx, hsquare, hc⟩

theorem fixed_element_commutator_normalized (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a = false) {x : FreeAmalgam R}
    (hx : x ∈ B R a (geometry.Z_normal a)) :
    Ltilde R a ≤ normalizer ((⁅zpowers x, Q R a⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hV := (geometry.V_le_Q hb a ha).trans (show Q R a ≤ stabilizer R a from fun _ hz => hz.1)
  obtain ⟨hxV, hfixed⟩ := (mem_B_iff R a _ hV x).mp hx
  have hxQ := geometry.V_le_Q hb a ha hxV
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)
  have hreduce := commutator_eq_of_centralizing_sup
    (B := Z R a ⊔ zpowers x) rfl hcentral
    ((zpowers_le.mpr hxQ).trans (Q R a).le_normalizer)
  apply le_normalizer_iff.mpr
  intro l hl y hy
  have hlx : l * x * l⁻¹ ∈ Z R a ⊔ zpowers x := by
    have hh := (Z R a ⊔ zpowers x).mul_mem (mem_sup_left (hfixed l hl))
      (mem_sup_right (mem_zpowers x))
    simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  have hX : (zpowers x).map (MulAut.conj l).toMonoidHom ≤ Z R a ⊔ zpowers x := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hlx
  have hQ : (Q R a).map (MulAut.conj l).toMonoidHom = Q R a :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized R a) (Ltilde_le_stabilizer a hl))
  have hmap : (⁅zpowers x, Q R a⁆ : Subgroup (FreeAmalgam R)).map
      (MulAut.conj l).toMonoidHom ≤ ⁅zpowers x, Q R a⁆ := by
    rw [map_commutator, hQ]
    calc
      ⁅(zpowers x).map (MulAut.conj l).toMonoidHom, Q R a⁆ ≤
          ⁅Z R a ⊔ zpowers x, Q R a⁆ := commutator_mono hX le_rfl
      _ = ⁅zpowers x, Q R a⁆ := by
        rw [commutator_comm, ← hreduce, commutator_comm]
  exact hmap (mem_map_of_mem _ hy)

/-- Source p.885: a fixed-preimage involution with such a small displacement
centralizes Q and hence lies in X = Z. -/
theorem mem_Z_of_fixed_small_commutator (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    {x : FreeAmalgam R} (hx : x ∈ B R a (geometry.Z_normal a)) (hsquare : x ^ 2 = 1)
    (hbound : ⁅zpowers x, Q R a⁆ ≤ edgeDisplacement a t) : x ∈ Z R a := by
  have hV := (geometry.V_le_Q hb a ha).trans (show Q R a ≤ stabilizer R a from fun _ hz => hz.1)
  have hxQ := geometry.V_le_Q hb a ha ((mem_B_iff R a _ hV x).mp hx).1
  exact mem_Z_of_normalized_edge_commutator source hb modules facts ha hat hxQ hsquare
    hbound (fixed_element_commutator_normalized hb ha hx)

theorem product_square_eq_one (source : LocalSource L R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    {x y : FreeAmalgam R} (hx : x ∈ Z R p.a) (hy : y ∈ Z R p.c) : (x * y) ^ 2 = 1 := by
  have hxX : x ∈ X R p.a := by rw [modules.X_eq_Z p.a p.color_a]; exact hx
  have hyX : y ∈ X R p.c := by rw [modules.X_eq_Z p.c p.before_color]; exact hy
  have hxy : Commute x y := (mem_omegaCenter_iff.mp hyX).2.2 x
    (p.trapped ((Z_le_VBall R p.a 2) hx))
  rw [hxy.mul_pow, (mem_omegaCenter_iff.mp hxX).2.1,
    (mem_omegaCenter_iff.mp hyX).2.1, one_mul]

namespace SixPath
variable {p : Counterexample geometry} (path : SixPath p)

/-- Complete the complementary b = 6 contradiction once its three actual
local subgroup containments have been established. -/
theorem false_of_fixed_cover (source : LocalSource L R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (hcover : Z R p.a ≤ Z R p.c ⊔ B R path.middle (geometry.Z_normal path.middle))
    (hstart : ⁅Z R p.a, Q R path.middle⁆ ≤ edgeDisplacement path.middle path.first)
    (hpredecessor : ⁅Z R p.c, Q R path.middle⁆ ≤ edgeDisplacement path.middle path.first) :
    False := by
  obtain ⟨x, hx, y, hy, hfixed, hout⟩ := path.exists_product_in_fixed_not_Z hcover
  have hadj := adjacent_symm R path.first_middle_adjacent
  have hbound : edgeDisplacement path.middle path.first ≤ Z R path.middle :=
    (Initial.edge_le_natural source _ _ path.middle_color hadj).trans (U_le_Z _)
  have hnorm : Q R path.middle ≤ normalizer
      (edgeDisplacement path.middle path.first : Set (FreeAmalgam R)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes path.middle path.middle_color))).trans
        (centralizer_le hbound)).trans (Subgroup.centralizer_le_normalizer _)
  have hstartPre := le_commutatorPreimage
    ((Z_le_VBall R p.a 2).trans path.start_V_le_middle_kernel) hstart
  have hpredPre := le_commutatorPreimage
    ((Z_le_VBall R p.c 2).trans path.predecessor_V_le_middle_kernel) hpredecessor
  have hxy := (commutatorPreimage (Q R path.middle) (Q R path.middle)
    (edgeDisplacement path.middle path.first)).mul_mem (hstartPre hx) (hpredPre hy)
  have hcomm := (commutator_mono (zpowers_le.mpr hxy) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnorm)
  exact hout (mem_Z_of_fixed_small_commutator source (by rw [path.six]; decide)
    modules facts path.middle_color hadj hfixed (product_square_eq_one source modules p hx hy) hcomm)

end SixPath

/-- Step (3) identifies the two sides of the final edge when the endpoint
is a moving neighbor. That membership remains an explicit premise. -/
theorem radius_eq_predecessor_edge (p : Counterexample geometry)
    (initial : InitialFacts p) (facts : ContraryLocalFacts geometry)
    (hmoving : p.a' ∈ movingNeighbors geometry p.c)
    {t : Vertex R} (ht : Before p.a p.a' t 1) :
    radiusCommutator p.a p.a' = edgeDisplacement p.c t := by
  rw [initial.radius_eq_edge t ht]
  exact facts.edge_eq p.c t p.a' p.before_color
    (p.before.adjacent (geometry := geometry) ht) ht.endpoint_adjacent hmoving

theorem radius_le_predecessor_natural (source : LocalSource L R)
    (p : Counterexample geometry) (initial : InitialFacts p)
    (facts : ContraryLocalFacts geometry)
    (hmoving : p.a' ∈ movingNeighbors geometry p.c) :
    radiusCommutator p.a p.a' ≤ U R p.c := by
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by have := initial.six_le; omega)
  rw [radius_eq_predecessor_edge p initial facts hmoving ht]
  exact Initial.edge_le_natural source p.c t p.before_color
    (p.before.adjacent (geometry := geometry) ht)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
