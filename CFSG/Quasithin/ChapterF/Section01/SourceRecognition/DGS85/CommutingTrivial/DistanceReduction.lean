module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceFiveExclusion
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The critical distance is three in characteristic two

For a hypothetical distance above five, the first radius-two escape supplies
its shifted critical pair. The centralizer supplement at alpha-prime-2
moves the final neighboring center to another neighbor while fixing the
commutator R = [V_beta,V_alpha-prime]. Their intersection traps R in the
middle central omega. The natural residual section gives the reverse order
bound, so R equals that omega.

A second radius-two escape centralizes R by the distance bound, and also
centralizes its own local central omega. Those two omegas generate the
intervening natural center. An escaping element moves the other neighbor;
edge maximality and faithfulness then force this nontrivial center to vanish.
Thus b > 3 implies b = 5. The established characteristic-two distance-five
contradiction leaves b = 3.

The actual reduced F1.11 application constructs both linear markings and
natural sections before using them. The catalogue, Chapter 8 and source 6.5
premises remain explicit for their existing producers. DistanceThreeReduction
applies the result to the whole-span theorem with both literal actions.
The field-two conclusion of 9.10 is a separate remaining obligation.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.11, printed pp.150--151; 9.7--9.8, printed pp.144--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A centralizer supplement traps a subgroup of a neighboring center in the
local omega: transport to a second neighbor and intersect. -/
theorem linear_center_bound_of_centralizer_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {w v r : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hne : v ≠ r)
    (hωw : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,K))
    (R : Subgroup G) (hRv : R ≤ Z (family P) v)
    (hsupp : graphLocalGroup (family P) w =
      (graphLocalGroup (family P) w ⊓ centralizer (R : Set G)) ⊔ Q (family P) w) :
    R ≤ Z (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  let C := graphLocalGroup Γ w ⊓ centralizer (R : Set G)
  have hn : C ≤ normalizer (Q Γ w : Set G) :=
    (inf_le_left.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ w)
  obtain ⟨g,hg,hgv⟩ := graphLocalGroup_transitive h hB hS w ⟨v,hv⟩ ⟨r,hr⟩
  change g • v = r at hgv
  have hg' : g ∈ C ⊔ Q Γ w := hsupp ▸ hg
  change g ∈ (↑(C ⊔ Q Γ w) : Set G) at hg'
  rw [coe_mul_of_left_le_normalizer_right C (Q Γ w) hn] at hg'
  obtain ⟨c,hc,q,hq,rfl⟩ := hg'
  have hqv : q • v = v := (source_Z_Q_U h w).2.trans
    ((ballKernel_one_le_edge Γ hv).trans inf_le_right) hq
  rw [mul_smul,hqv] at hgv
  have hRc : R.map (MulAut.conj c).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer (R : Set G) hc.2)
  have hRr := map_mono (f := (MulAut.conj c).toMonoidHom) hRv
  rw [hRc,←Z_translate,hgv] at hRr
  exact (le_inf hRv hRr).trans_eq
    (linear_neighbor_centers_intersection h hB hS hv hr hne hob hωw ew ev)

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- A full Sylow image in the actual natural residual section moves at least
one field line. The bound concerns the original group commutator. -/
theorem reduced_natural_residual_commutator_card_ge
    (h : HypothesisF11 L S₀) (beta : Vertex (Reduction.reducedFamily L S₀))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n)
    (D : Subgroup (Reduction.G₀ L S₀)) (hp : IsPGroup 2 D)
    (hDH : D ≤ graphLocalGroup (Reduction.reducedFamily L S₀) beta)
    (hi : (Q (Reduction.reducedFamily L S₀) beta).relIndex D = Nat.card F) :
    Nat.card F ≤ Nat.card (⁅V (Reduction.reducedFamily L S₀) beta 1,D⁆ :
      Subgroup (Reduction.G₀ L S₀)) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,σ,Tβ,hσ,hfaith,hnat,E,hE⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate (fun y => (source_Z_Q_U ht y).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  have hcomp : σ.comp q = Representation.NormalElementaryQuotient.fixedQuotientAction A (pResidual 2 H) :=
    MonoidHom.ext hσ
  obtain ⟨⟨c⟩,_,_⟩ := neighborhood_residual_section ht (Reduction.reduced_kernel_sylow h) beta hb2 H
    (core_le_graphLocalGroup ht beta) (sylowGenerated_le _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q Γ beta := hk ▸ graphLocalGroup_core ht beta
  let I := (D.subgroupOf H).map q
  have hcI : Nat.card I = Nat.card F := by
    change Nat.card ((D.subgroupOf H).map q) = Nat.card F
    rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
      hkmap,map_subgroupOf_eq_of_le hDH]
    exact hi
  obtain ⟨T,hT⟩ := (hp.comap_subtype.map q).exists_le_sylow
  have hIT : I = T := eq_of_le_of_card_ge hT (by
    rw [hcI]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).ge)
  have hquad : IsQuadratic σ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) Tβ T
    exact SL2SylowFixedRecognition.quadratic_conjugate σ hnat.2.2 g
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  rw [commutator_comm]
  exact Representation.BinaryConjugationSection.natural_section_commutator_card_ge q σ
    (hcomp.symm ▸ c) hfaith T hn hF ⟨hnat.1,hnat.2.1,hquad⟩ D hDH hIT


private theorem omega_of_same_type
    (h : LocallyRankOneTriple P B) {v w : Vertex (family P)} (ht : v.type = w.type)
    (hz : Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v)) :
    Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w) := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  rw [Z_translate,graphLocalGroup_conjugate h,
    ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hz]

private theorem center_card_of_same_type
    {Γ : Bool → Subgroup G} [∀ i, Finite (Γ i)] {v w : Vertex Γ} (ht : v.type = w.type) :
    Nat.card (Z Γ w) = Nat.card (Z Γ v) := by
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ v w).mpr ht
  have hh := card_map_of_injective (K := Z Γ v)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rwa [←Z_translate,hg] at hh

private theorem type_of_two_edges {Γ : Bool → Subgroup G} {x y z : Vertex Γ}
    (hxy : (graph Γ).Adj x y) (hyz : (graph Γ).Adj y z) : x.type = z.type := by
  have h1 := hxy.1
  have h2 := hyz.1
  cases hx : x.type <;> cases hy : y.type <;> cases hz : z.type <;> simp_all

private theorem short_span_le_core (h : LocallyRankOneTriple P B)
    (hSyl : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (v w : Vertex (family P)) (r : ℕ)
    (hd : (graph (family P)).dist v w + r < b (family P)) :
    V (family P) v r ≤ Q (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  apply Z_le_Q_of_dist_lt_b Γ (fun y => (source_Z_Q_U h y).1) hSyl
  have hz' := (mem_ball_iff Γ h.generate v z r).mp hz
  have ht := (connected Γ h.generate).dist_triangle (u := z) (v := v) (w := w)
  rw [SimpleGraph.dist_comm (u := z) (v := v)] at ht
  change (graph Γ).dist v w + r < b Γ at hd
  omega

private theorem short_spans_commute (h : LocallyRankOneTriple P B)
    (hSyl : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (v w : Vertex (family P)) (r s : ℕ)
    (hd : (graph (family P)).dist v w + r + s < b (family P)) :
    ⁅V (family P) v r,V (family P) w s⁆ = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply le_centralizer_iff.mp
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hx' := (mem_ball_iff Γ h.generate v x r).mp hx
  have hy' := (mem_ball_iff Γ h.generate w y s).mp hy
  have ht := (connected Γ h.generate).dist_triangle (u := y) (v := w) (w := x)
  have ht' := (connected Γ h.generate).dist_triangle (u := w) (v := v) (w := x)
  rw [SimpleGraph.dist_comm (u := y) (v := w)] at ht
  rw [SimpleGraph.dist_comm (u := w) (v := v)] at ht'
  exact short_centers_commute Γ (fun z => (source_Z_Q_U h z).1) hSyl y x (by
    change (graph Γ).dist v w + r + s < b Γ at hd
    omega)

private theorem opposite_omega_centers_generate
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {r w s : Vertex (family P)} (hw : (graph (family P)).Adj r w)
    (hs : (graph (family P)).Adj r s) (hne : w ≠ s)
    (hωw : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (er : (graphLocalGroup (family P) r ⧸ pCore 2 (graphLocalGroup (family P) r)) ≃* SL(2,F))
    {q : ℕ} (hcw : Nat.card (Z (family P) w) = q)
    (hcr : Nat.card (Z (family P) r) = q^2) :
    Z (family P) r = Z (family P) w ⊔ Z (family P) s := by
  let := finite_endpoints h
  let Γ := family P
  let := Z_elementary Γ (fun v => (source_Z_Q_U h v).1) r
  let : Finite (Z Γ r) := Finite.of_injective (inclusion (Z_le_stabilizer Γ r)) (inclusion_injective _)
  have hws : w.type = s.type := type_of_two_edges hw.symm hs
  have hωs := omega_of_same_type h hws hωw
  have hwZ : Z Γ w ≤ Z Γ r := hωw ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hw.symm
  have hsZ : Z Γ s ≤ Z Γ r := hωs ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hs.symm
  have hdis := linear_central_neighbor_centers_disjoint h hB hS hw hs hne
    (core_escape_of_intersection_obstruction Γ (hob w r hw.symm))
    (core_escape_of_intersection_obstruction Γ (hob s r hs.symm)) hωw er
  have hn : Z Γ s ≤ normalizer (Z Γ w : Set G) :=
    ((hsZ.trans (le_centralizer (Z Γ r))).trans (centralizer_le hwZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint (Z Γ w) (Z Γ s) hn
    (disjoint_iff.mpr hdis)
  rw [center_card_of_same_type hws,hcw,←pow_two,←hcr] at hc
  exact (eq_of_le_of_card_ge (sup_le hwZ hsZ) hc.ge).symm

private theorem center_normalizer_escape_false
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {s r k : Vertex (family P)} (hr : (graph (family P)).Adj s r)
    (hk : (graph (family P)).Adj s k) (hne : k ≠ r)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (es : (graphLocalGroup (family P) s ⧸ pCore 2 (graphLocalGroup (family P) s)) ≃* SL(2,F))
    (A : Subgroup G) (hAQ : A ≤ Q (family P) k) (he : ¬ A ≤ Q (family P) s)
    (hAC : A ≤ centralizer (Z (family P) r : Set G)) : False := by
  let := finite_endpoints h
  let Γ := family P
  obtain ⟨t,ht,htQ⟩ := SetLike.not_le_iff_exists.mp he
  have hmove := linear_core_element_moves_other_neighbor h hB hS hk hr hne es (hAQ ht) htQ
  have htS : t ∈ stabilizer Γ s :=
    (sylowGenerated_le _) (neighbor_core_le_localGroup h hB hS hk (hAQ ht))
  have hn : stabilizer Γ s ≤ normalizer (Z Γ r : Set G) := by
    rcases source_edge_maximal h hr (stabilizer Γ s ⊓ normalizer (Z Γ r : Set G))
      (le_inf inf_le_left (inf_le_right.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ r)))
      inf_le_left with heq | heq
    · exact (hmove (heq.le ⟨htS,Subgroup.centralizer_le_normalizer _ (hAC ht)⟩).2).elim
    · exact heq.ge.trans inf_le_right
  have hbot : Z Γ r = ⊥ := by
    apply CommutingNontrivial.source_normalized_edge_eq_bot h hr _
      (le_inf (((source_Z_Q_U h r).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h r).2.trans ((ballKernel_one_le_edge Γ hr.symm).trans inf_le_right)))
        (Z_le_stabilizer Γ r))
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := locally_transitive Γ hr hz
      exact ⟨g,hn hg,hgz⟩
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := locally_transitive Γ hr.symm hz
      exact ⟨g,CommutingNontrivial.stabilizer_normalizes_Z Γ r hg,hgz⟩
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base Γ r
  rw [←hg,Z_translate,map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hbot
  exact base_Z_ne_bot h _ hbot


/-- The two radius-two escapes exclude every critical distance above five
on the literal reduced graph. No upper distance bound is assumed. -/
theorem reduced_critical_distance_gt_five_false
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb5 : 5 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) : False := by
  have hb : 3 < b (Reduction.reducedFamily L S₀) := by omega
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,v,hx,hdx,hv,hdv,hwhole,hcard,hcent,hcent',hR⟩ :=
    reduced_critical_large_distance_whole_span h hc hab hd hb hcomm h8 hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hSyl := Reduction.reduced_kernel_sylow h
  have hZ := fun y => (source_Z_Q_U ht y).1
  change 5 < b Γ at hb5
  change 3 < b Γ at hb
  have hb1 : 1 < b Γ := by omega
  have hb2 : 2 < b Γ := by omega
  obtain ⟨hodd,_,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  have hb6 : 6 < b Γ := by
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    change 5 < b Γ at hb5
    omega
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  change (graph Γ).dist beta v + 2 = b Γ at hdv
  have hca : (graph Γ).dist a a' = b Γ := hc.1
  have hba' : beta.type = a'.type := by
    apply (even_dist_iff Γ ht.generate beta a').mp
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    exact ⟨k,by omega⟩
  have hdav : (graph Γ).dist a v + 1 = b Γ := by
    have h1 := (connected Γ ht.generate).dist_triangle (u := a) (v := beta) (w := v)
    have h2 := (connected Γ ht.generate).dist_triangle (u := a) (v := v) (w := a')
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab] at h1
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hv.symm,hca] at h2
    omega
  have hav : a ≠ v := by intro he; rw [he,SimpleGraph.dist_self] at hdav; omega
  obtain ⟨w,hw,hdw⟩ := exists_predecessor Γ ht.generate a v hav
  have hdaw : (graph Γ).dist a w + 2 = b Γ := by omega
  have haw : a ≠ w := by intro he; rw [he,SimpleGraph.dist_self] at hdaw; omega
  obtain ⟨r,hr,hdr⟩ := exists_predecessor Γ ht.generate a w haw
  have hdar : (graph Γ).dist a r + 3 = b Γ := by omega
  have har : a ≠ r := by intro he; rw [he,SimpleGraph.dist_self] at hdar; omega
  obtain ⟨s,hs,hds⟩ := exists_predecessor Γ ht.generate a r har
  have hdas : (graph Γ).dist a s + 4 = b Γ := by omega
  have hvr : v ≠ r := by intro he; rw [he] at hdav; omega
  have hws : w ≠ s := by intro he; rw [he] at hdaw; omega
  have hbw : beta.type = w.type := hba'.trans (type_of_two_edges hv hw)
  have hbs : beta.type = s.type := hbw.trans (type_of_two_edges hr hs)
  have hωw := omega_of_same_type ht hbw hω
  have hωs := omega_of_same_type ht hbs hω
  obtain ⟨g,hgw,hgv⟩ := same_type_edge_transport Γ hab hw hbw
  obtain ⟨_,fv,_,_,_⟩ := local_quotient_parameter_transport ht g hgv
  let ev := fv.symm.trans eα
  obtain ⟨j,hjw,hjr⟩ := same_type_edge_transport Γ hab hr.symm hbw
  obtain ⟨_,fr,_,_,_⟩ := local_quotient_parameter_transport ht j hjr
  let er := fr.symm.trans eα
  obtain ⟨j,hjs⟩ := (same_orbit_iff Γ beta s).mpr hbs
  obtain ⟨_,fs,_,_,_⟩ := local_quotient_parameter_transport ht j hjs
  let es := fs.symm.trans eβ
  obtain ⟨_,_,_,hi',_⟩ := reduced_large_distance_natural_section h h8 hob
    hc hab hd hb hcomm hn hF eα eβ
  have hpath := critical_first_path_orbit ht hB hS hc hab hd hb2 hodd eα eβ
  obtain ⟨hW,heW,hRW,t,z,hat,htz,haz,hzc,hdtw,hzcomm,
      ez,et,ew,htriv,hrev,hit,hiw,hnatt,hnatw⟩ :=
    reduced_linear_shifted_sections h h8 hob hc hab hd hb hcomm hn hF eα eβ
      hi hi' hpath hv hw hdav hdaw
  obtain ⟨ew',_,_,_,hsupp,_,_⟩ := reduced_linear_commutator_centralizer_supplement h h8 hob
    hc hab hd hb hcomm hn hF eα eβ hi hi' hpath hv hw hdav hdaw
  have hRZw : ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ w :=
    linear_center_bound_of_centralizer_supplement ht hB hS hob hw.symm hr hvr hωw ew' ev
      _ (hR.trans inf_le_left) hsupp
  let := Z_elementary Γ hZ a
  obtain ⟨ρ,T,hact,hfaith,hna,E,hE⟩ := hnat
  obtain ⟨hcarda,hcardb⟩ := linear_natural_neighbor_center_orders ht hB hS hab
    (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
    ρ hact hfaith ⟨T,hna⟩
  rw [heq] at hcarda hcardb
  have hcardw : Nat.card (Z Γ w) = Nat.card F := (center_card_of_same_type hbw).trans hcardb
  have hcardr : Nat.card (Z Γ r) = Nat.card F^2 := by
    -- Use the common edge transporter, whose alpha endpoint is r.
    obtain ⟨k,hkw,hkr⟩ := same_type_edge_transport Γ hab hr.symm hbw
    have hh' := card_map_of_injective (K := Z Γ a)
      (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
    rw [←Z_translate,hkr] at hh'
    exact hh'.trans hcarda
  let : Finite (Z Γ w) := Finite.of_injective (inclusion (Z_le_stabilizer Γ w)) (inclusion_injective _)
  let := V_elementary Γ ht.generate hZ hSyl a' (r := 1) (by simpa using hb2)
  have hlow := reduced_natural_residual_commutator_card_ge h beta hn hF eβ hres
    (V Γ a' 1) (IsElementaryAbelian.isPGroup 2 _)
    (neighbor_le_graphLocalGroup ht hSyl a' beta hb1 (by
      change (graph Γ).dist a' beta + 1 ≤ b Γ
      rw [SimpleGraph.dist_comm]
      exact hd.le)) hi'
  have hReq : ⁅V Γ beta 1,V Γ a' 1⁆ = Z Γ w :=
    eq_of_le_of_card_ge hRZw (by rw [hcardw]; exact hlow)
  have hczw : (graph Γ).dist z w = b Γ := hzc.1
  have hdzr : (graph Γ).dist z r + 1 = b Γ := by
    have h1 := (connected Γ ht.generate).dist_triangle (u := z) (v := a) (w := r)
    have h2 := (connected Γ ht.generate).dist_triangle (u := z) (v := r) (w := w)
    rw [SimpleGraph.dist_comm (u := z) (v := a),haz] at h1
    rw [hczw,SimpleGraph.dist_eq_one_iff_adj.mpr hr.symm] at h2
    omega
  have hdzs : (graph Γ).dist z s + 2 = b Γ := by
    have h1 := (connected Γ ht.generate).dist_triangle (u := z) (v := a) (w := s)
    have h2 := (connected Γ ht.generate).dist_triangle (u := z) (v := s) (w := r)
    rw [SimpleGraph.dist_comm (u := z) (v := a),haz] at h1
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hs.symm] at h2
    omega
  have hpath' := critical_first_path_orbit ht hB hS hzc htz.symm hdtw hb2 hodd ez et
  obtain ⟨hTs,heTs⟩ := linear_radius_two_escape_at_predecessor ht hB hS hzc htz.symm hdtw
    hb2 hodd et hit hiw hpath' hr hs hdzr hdzs
  have hshort : ⁅V Γ beta 1,V Γ z 2⁆ = ⊥ := by
    apply short_spans_commute ht hSyl
    have hh := (connected Γ ht.generate).dist_triangle (u := beta) (v := a) (w := z)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab.symm,haz] at hh
    change (graph Γ).dist beta z + 1 + 2 < b Γ
    omega
  have hZwT : Z Γ w ≤ centralizer (V Γ z 2 : Set (Reduction.G₀ L S₀)) := by
    rw [←hReq]
    exact ((hR.trans inf_le_right).trans (CommutingNontrivial.Z_neighbor_le_V Γ hx)).trans
      (commutator_eq_bot_iff_le_centralizer.mp hshort)
  have hZsT : Z Γ s ≤ centralizer (V Γ z 2 : Set (Reduction.G₀ L S₀)) := by
    change Z Γ s = omegaCenterIn (graphLocalGroup Γ s) at hωs
    rw [hωs]
    have hc : omegaCenterIn (graphLocalGroup Γ s) ≤
        centralizer (graphLocalGroup Γ s : Set (Reduction.G₀ L S₀)) :=
      fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
    exact hc.trans (centralizer_le hTs)
  have hZr := opposite_omega_centers_generate ht hB hS hob hr.symm hs hws hωw er hcardw hcardr
  have hZrT : Z Γ r ≤ centralizer (V Γ z 2 : Set (Reduction.G₀ L S₀)) := by
    change Z Γ r = Z Γ w ⊔ Z Γ s at hZr
    rw [hZr]
    exact sup_le hZwT hZsT
  have hzs : z ≠ s := by intro he; rw [he,SimpleGraph.dist_self] at hdzs; omega
  obtain ⟨k,hk,hdk⟩ := exists_predecessor Γ ht.generate z s hzs
  have hkr : k ≠ r := by intro he; rw [he] at hdk; omega
  have hTQk : V Γ z 2 ≤ Q Γ k := short_span_le_core ht hSyl z k 2 (by
    change (graph Γ).dist z k + 2 < b Γ
    omega)
  exact center_normalizer_escape_false ht hB hS hs.symm hk hkr es (V Γ z 2)
    hTQk heTs (le_centralizer_iff.mp hZrT)

/-- The unrestricted large-distance reduction in source 9.11. -/
theorem reduced_critical_large_distance_eq_five
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) : b (Reduction.reducedFamily L S₀) = 5 := by
  have hb1 : 1 < b (Reduction.reducedFamily L S₀) := by omega
  have hodd := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm).1
  have hle : b (Reduction.reducedFamily L S₀) ≤ 5 := by
    by_contra he
    exact reduced_critical_distance_gt_five_false h hc hab hd (by omega) hcomm h8 hob
      Mα Mβ Mα' Mαsource
  obtain ⟨k,hk⟩ := hodd
  omega

/-- Source 9.11 in characteristic two: the actual critical distance is three.
The field parameters are not assumed binary. -/
theorem reduced_critical_distance_eq_three
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) : b (Reduction.reducedFamily L S₀) = 3 := by
  have hge := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.1
  apply Nat.le_antisymm _ hge
  by_contra he
  have hb5 := reduced_critical_large_distance_eq_five h hc hab hd (by omega) hcomm h8 hob
    Mα Mβ Mα' Mαsource
  exact reduced_critical_distance_five_false h hc hab hd hb5 hcomm h8 hob Mα Mβ Mα' Mαsource

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
