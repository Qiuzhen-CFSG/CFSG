module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceFivePaths
/-!
# Reflected elements on the distance-five path

A nonidentity element of the original neighboring two-core moves every other
neighbor in the binary linear local action. Reflecting a four-edge path about
such an element places a double commutator in its middle center. For an
eight-edge path the two reflections place inverse double commutators in
disjoint middle centers, so both vanish. This uses the actual original
quotient markings and the source four-path identity, without a tree hypothesis.

The F1.11 consumer constructs and transports the markings and discharges the
four-path identity using `DistanceFivePaths`. Its distance-five and earlier
source premises remain explicit; terminal distance and field conclusions are
not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.11, printed p.151, characteristic-two paragraph.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem double_commutator_inverse {t u : G} (ht : t^2=1) (hu : u^2=1) :
    ⁅u*t*u⁻¹,t⁆ = ⁅t*u*t⁻¹,u⁆⁻¹ := by
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hu)
  simp only [commutatorElement_def,mul_inv_rev,hti,hui,mul_assoc]

/-- Every surviving neighboring-core element moves the other neighbors. -/
theorem linear_core_element_moves_other_neighbor
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w x : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hx : (graph (family P)).Adj v x) (hne : w ≠ x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    {t : G} (ht : t ∈ Q (family P) w) (htQ : t ∉ Q (family P) v) : t • x ≠ x := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hQH := neighbor_core_le_localGroup h hB hS hw
  let tH : H := ⟨t,hQH ht⟩
  obtain ⟨T,hT,hfix⟩ := linear_neighbor_core_sylow_image h hB hS hw
    (fun he => htQ (he ht)) e
  change ((Q Γ w).subgroupOf H).map q = (T : Subgroup SL(2,F)) at hT
  change ∀ l : H, q l ∈ normalizer (T : Set SL(2,F)) ↔ (l : G) • w = w at hfix
  have htT : q tH ∈ T := by
    change q tH ∈ (T : Subgroup SL(2,F))
    rw [←hT]
    exact mem_map_of_mem q (show tH ∈ (Q Γ w).subgroupOf H from ht)
  have htne : q tH ≠ 1 := by
    intro he
    have hh : tH ∈ pCore 2 H := (QuotientGroup.eq_one_iff tH).mp
      (e.injective (he.trans e.map_one.symm))
    exact htQ ((graphLocalGroup_core h v).le (mem_map_of_mem H.subtype hh))
  obtain ⟨g,hg,hgx⟩ := graphLocalGroup_transitive h hB hS v ⟨w,hw⟩ ⟨x,hx⟩
  change g • w = x at hgx
  let gH : H := ⟨g,hg⟩
  intro htx
  have hconj : q (gH⁻¹*tH*gH) ∈ normalizer (T : Set SL(2,F)) := by
    apply (hfix _).mpr
    change (g⁻¹*t*g) • w = w
    rw [mul_smul,mul_smul,hgx,htx,←hgx,inv_smul_smul]
  have hn := Matrix.SpecialLinearGroup.mem_sylow_normalizer_of_conjugate_mem T (q tH)
    (q gH)⁻¹ htT htne (by simpa only [map_mul,map_inv,inv_inv] using hconj)
  have hn' : q gH ∈ normalizer (T : Set SL(2,F)) := by
    simpa only [inv_inv] using (normalizer (T : Set SL(2,F))).inv_mem hn
  have hwfix := (hfix gH).mp hn'
  exact hne (hwfix.symm.trans hgx)

/-- Reflecting a four-path bounds the two endpoint-center commutator. -/
theorem reflected_center_commutator_le
    {Γ : Bool → Subgroup G} {beta a d₀ d₁ d₂ : Vertex Γ}
    (h4 : ∀ v₀ v₁ v₂ v₃ v₄ : Vertex Γ,
      (graph Γ).Adj v₀ v₁ → (graph Γ).Adj v₁ v₂ → (graph Γ).Adj v₂ v₃ →
      (graph Γ).Adj v₃ v₄ → v₂ ≠ v₀ → v₃ ≠ v₁ → v₄ ≠ v₂ →
      beta.type = v₀.type → ⁅V Γ v₀ 1,V Γ v₄ 1⁆ = Z Γ v₂)
    (ha : (graph Γ).Adj d₀ a) (h01 : (graph Γ).Adj d₀ d₁)
    (h12 : (graph Γ).Adj d₁ d₂) (hne : d₂ ≠ d₀) (htype : beta.type = d₀.type)
    (u : G) (hfix : u • d₂ = d₂) (hmove : u • d₁ ≠ d₁) :
    ⁅Z Γ (u • a),Z Γ a⁆ ≤ Z Γ d₂ := by
  have hact : ∀ (g : G) {v w : Vertex Γ}, (graph Γ).Adj v w →
      (graph Γ).Adj (g • v) (g • w) :=
    fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso Γ g).toHom.map_adj he
  have h23 : (graph Γ).Adj d₂ (u • d₁) := by simpa only [hfix] using hact u h12.symm
  have h34 := hact u h01.symm
  have h24 : u • d₀ ≠ d₂ := by
    rw [←hfix]
    exact fun he => hne ((MulAction.toPerm u).injective he).symm
  have h := h4 d₀ d₁ d₂ (u • d₁) (u • d₀) h01 h12 h23 h34 hne hmove h24 htype
  rw [commutator_comm]
  exact (commutator_mono (CommutingNontrivial.Z_neighbor_le_V Γ ha)
    (CommutingNontrivial.Z_neighbor_le_V Γ (hact u ha))).trans_eq h

private theorem four_edges_dist_le {Γ : Bool → Subgroup G} {v₀ v₁ v₂ v₃ v₄ : Vertex Γ}
    (h01 : (graph Γ).Adj v₀ v₁) (h12 : (graph Γ).Adj v₁ v₂)
    (h23 : (graph Γ).Adj v₂ v₃) (h34 : (graph Γ).Adj v₃ v₄) :
    (graph Γ).dist v₀ v₄ ≤ 4 := by
  simpa using (graph Γ).dist_le (Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h34 Walk.nil))))

/-- The two reflected commutators are inverse elements of disjoint path centers. -/
theorem eight_path_reflected_elements_commute
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (hb5 : b (family P) = 5)
    {d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ : Vertex (family P)}
    (h01 : (graph (family P)).Adj d₀ d₁) (h12 : (graph (family P)).Adj d₁ d₂)
    (h23 : (graph (family P)).Adj d₂ d₃) (h34 : (graph (family P)).Adj d₃ d₄)
    (h45 : (graph (family P)).Adj d₄ d₅) (h56 : (graph (family P)).Adj d₅ d₆)
    (h67 : (graph (family P)).Adj d₆ d₇) (h78 : (graph (family P)).Adj d₇ d₈)
    (h31 : d₃ ≠ d₁) (h42 : d₄ ≠ d₂) (h53 : d₅ ≠ d₃)
    (h64 : d₆ ≠ d₄) (h75 : d₇ ≠ d₅)
    (h4 : ∀ v₀ v₁ v₂ v₃ v₄ : Vertex (family P),
      (graph (family P)).Adj v₀ v₁ → (graph (family P)).Adj v₁ v₂ →
      (graph (family P)).Adj v₂ v₃ → (graph (family P)).Adj v₃ v₄ →
      v₂ ≠ v₀ → v₃ ≠ v₁ → v₄ ≠ v₂ → d₁.type = v₀.type →
      ⁅V (family P) v₀ 1,V (family P) v₄ 1⁆ = Z (family P) v₂)
    (hω3 : Z (family P) d₃ = omegaCenterIn (graphLocalGroup (family P) d₃))
    (htype7 : d₁.type = d₇.type)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (e3 : (graphLocalGroup (family P) d₃ ⧸ pCore 2 (graphLocalGroup (family P) d₃)) ≃* SL(2,F))
    (e4 : (graphLocalGroup (family P) d₄ ⧸ pCore 2 (graphLocalGroup (family P) d₄)) ≃* SL(2,K))
    (e5 : (graphLocalGroup (family P) d₅ ⧸ pCore 2 (graphLocalGroup (family P) d₅)) ≃* SL(2,F))
    {t u : G} (ht : t ∈ Z (family P) d₀) (htQ : t ∉ Q (family P) d₅)
    (hu : u ∈ Z (family P) d₈) (huQ : u ∉ Q (family P) d₃) :
    Commute (u*t*u⁻¹) t := by
  let := finite_endpoints h
  let Γ := family P
  have hZ := fun v => (source_Z_Q_U h v).1
  have hSyl := source_kernel_sylow h hB hS
  have ht4 : t ∈ Q Γ d₄ := Z_le_Q_of_dist_lt_b Γ hZ hSyl d₀ d₄
    (by rw [hb5]; exact (four_edges_dist_le h01 h12 h23 h34).trans_lt (by decide)) ht
  have hu4 : u ∈ Q Γ d₄ := Z_le_Q_of_dist_lt_b Γ hZ hSyl d₈ d₄
    (by rw [hb5]; exact (four_edges_dist_le h78.symm h67.symm h56.symm h45.symm).trans_lt (by decide)) hu
  have hu3 : u • d₃ = d₃ := (source_Z_Q_U h d₄).2.trans
    ((ballKernel_one_le_edge Γ h34.symm).trans inf_le_right) hu4
  have ht5 : t • d₅ = d₅ := (source_Z_Q_U h d₄).2.trans
    ((ballKernel_one_le_edge Γ h45).trans inf_le_right) ht4
  have humove := linear_core_element_moves_other_neighbor h hB hS h34 h23.symm h42 e3 hu4 huQ
  have htmove := linear_core_element_moves_other_neighbor h hB hS h45.symm h56 h64.symm e5 ht4 htQ
  have hR := reflected_center_commutator_le h4 h01.symm h12 h23 h31 rfl u hu3 humove
  have hR' := reflected_center_commutator_le h4 h78 h67.symm h56.symm h75.symm htype7 t ht5 htmove
  have ht' : u*t*u⁻¹ ∈ Z Γ (u • d₀) := by
    rw [Z_translate]
    exact mem_map_of_mem (MulAut.conj u).toMonoidHom ht
  have hu' : t*u*t⁻¹ ∈ Z Γ (t • d₈) := by
    rw [Z_translate]
    exact mem_map_of_mem (MulAut.conj t).toMonoidHom hu
  have hz : ⁅u*t*u⁻¹,t⁆ ∈ Z Γ d₃ := hR (commutator_mem_commutator ht' ht)
  have hz' : ⁅t*u*t⁻¹,u⁆ ∈ Z Γ d₅ := hR' (commutator_mem_commutator hu' hu)
  have ht2 := ((mem_omegaCenterIn_iff _ _).mp (hZ d₀ ht)).2.2
  have hu2 := ((mem_omegaCenterIn_iff _ _).mp (hZ d₈ hu)).2.2
  have hi := linear_central_neighbor_centers_disjoint h hB hS h34.symm h45 h53.symm
    (core_escape_of_intersection_obstruction Γ (hob d₃ d₄ h34))
    (core_escape_of_intersection_obstruction Γ (hob d₅ d₄ h45.symm)) hω3 e4
  apply commutatorElement_eq_one_iff_commute.mp
  apply (show Z Γ d₃ ⊓ Z Γ d₅ ≤ ⊥ from hi.le)
  exact ⟨hz,double_commutator_inverse ht2 hu2 ▸ (Z Γ d₅).inv_mem hz'⟩

private theorem bool_same {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
  cases i <;> cases j <;> cases k <;> simp_all

private theorem same_type_of_two_edges {Γ : Bool → Subgroup G} {v w z : Vertex Γ}
    (hv : (graph Γ).Adj v w) (hz : (graph Γ).Adj w z) : v.type = z.type := by
  exact bool_same hv.1 hz.1.symm

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The reflected-element step of 9.11 on the literal reduced graph. -/
theorem reduced_critical_distance_five_reflected_elements
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb5 : b (Reduction.reducedFamily L S₀) = 5)
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
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    ∀ d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ : Vertex Γ,
      (graph Γ).Adj d₀ d₁ → (graph Γ).Adj d₁ d₂ →
      (graph Γ).Adj d₂ d₃ → (graph Γ).Adj d₃ d₄ →
      (graph Γ).Adj d₄ d₅ → (graph Γ).Adj d₅ d₆ →
      (graph Γ).Adj d₆ d₇ → (graph Γ).Adj d₇ d₈ →
      d₃ ≠ d₁ → d₄ ≠ d₂ → d₅ ≠ d₃ → d₆ ≠ d₄ → d₇ ≠ d₅ →
      beta.type = d₁.type →
      ∀ t ∈ Z Γ d₀, t ∉ Q Γ d₅ →
      ∀ u ∈ Z Γ d₈, u ∉ Q Γ d₃ → Commute (u*t*u⁻¹) t := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,v,hx,hdx,hv,hdv,hwhole,hcard,hcent,hcent',hR,h4⟩ :=
    reduced_critical_distance_five_path_commutator h hc hab hd hb5 hcomm h8 hob Mα Mβ Mα' Mαsource
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
  have hb1 : 1 < b Γ := by change b Γ = 5 at hb5; omega
  obtain ⟨_,_,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  dsimp only
  intro d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ h01 h12 h23 h34 h45 h56 h67 h78
    h31 h42 h53 h64 h75 htype t htZ htQ u huZ huQ
  have ht3 : beta.type = d₃.type := htype.trans (same_type_of_two_edges h12 h23)
  have ht5 : beta.type = d₅.type := ht3.trans (same_type_of_two_edges h34 h45)
  have ht7 : d₁.type = d₇.type := htype.symm.trans (ht5.trans (same_type_of_two_edges h56 h67))
  have ha4 : a.type = d₄.type := bool_same hab.1 (ht3.symm ▸ h34.1.symm)
  obtain ⟨g3,hg3⟩ := (same_orbit_iff Γ beta d₃).mpr ht3
  obtain ⟨g4,hg4⟩ := (same_orbit_iff Γ a d₄).mpr ha4
  obtain ⟨g5,hg5⟩ := (same_orbit_iff Γ beta d₅).mpr ht5
  obtain ⟨_,f3,_,_,_⟩ := local_quotient_parameter_transport ht g3 hg3
  obtain ⟨_,f4,_,_,_⟩ := local_quotient_parameter_transport ht g4 hg4
  obtain ⟨_,f5,_,_,_⟩ := local_quotient_parameter_transport ht g5 hg5
  have hω3 : Z Γ d₃ = omegaCenterIn (graphLocalGroup Γ d₃) := by
    have hh := graphLocalGroup_conjugate ht g3 beta
    change graphLocalGroup Γ (g3 • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g3).toMonoidHom at hh
    rw [←hg3,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g3).injective,hω]
  exact eight_path_reflected_elements_commute ht hB hS hob hb5
    h01 h12 h23 h34 h45 h56 h67 h78 h31 h42 h53 h64 h75
    (fun v₀ v₁ v₂ v₃ v₄ h01 h12 h23 h34 h20 h31 h42 hv₀ =>
      h4 v₀ v₁ v₂ v₃ v₄ h01 h12 h23 h34 h20 h31 h42 (htype.trans hv₀))
    hω3 ht7 (f3.symm.trans eβ) (f4.symm.trans eα) (f5.symm.trans eβ) htZ htQ huZ huQ

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
