module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceFiveFixed
/-!
# Characteristic two excludes critical distance five

The source four-path identity makes the commutator of the endpoint
neighborhood spans equal to the middle center. Exchange the two neighbors
of the fourth vertex in its actual linear local quotient, and transport the
original critical pair. This constructs an escaping center at the far end
of an eight-edge path. An element of that center reflects the original
four-path. The two reflected double commutators vanish by
`DistanceFiveReflections`; the sharp fixed-subgroup criterion in
`DistanceFiveFixed` then makes the whole reflected spans commute. Their
middle center would be trivial, contradicting the original local structure.

This proves the characteristic-two contradiction in DGS 9.11, printed p.151,
for the literal reduced F1.11 graph. Both linear markings and natural
sections are constructed by the preceding source results, rather than
assumed here. The earlier catalogue, Chapter 8 and 6.5 premises retain their
separate producers and final assembly discharge. Reduction of larger
critical distance to five and the distance-three field conclusions remain
separate Chapter 9 obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.11, printed pp.150--151.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem subgroup_le_of_outside {A C D : Subgroup G}
    (he : ¬ A ≤ C) (hout : ∀ t ∈ A, t ∉ C → t ∈ D) : A ≤ D := by
  obtain ⟨s,hs,hsC⟩ := SetLike.not_le_iff_exists.mp he
  have hsD := hout s hs hsC
  intro t ht
  by_cases htC : t ∈ C
  · have hstC : s*t ∉ C := fun hh => hsC ((C.mul_mem_cancel_right htC).mp hh)
    exact (D.mul_mem_cancel_left hsD).mp (hout (s*t) (A.mul_mem hs ht) hstC)
  · exact hout t ht htC

private theorem short_center_centralizes_span
    (h : LocallyRankOneTriple P B)
    (hS : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    {x y : Vertex (family P)} (hd : (graph (family P)).dist x y + 1 < b (family P)) :
    Z (family P) x ≤ centralizer (V (family P) y 1 : Set G) := by
  let := finite_endpoints h
  let Γ := family P
  apply le_centralizer_iff.mp
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  have hz' := (mem_ball_iff Γ h.generate y z 1).mp hz
  have htri := (connected Γ h.generate).dist_triangle (u := x) (v := y) (w := z)
  apply le_centralizer_iff.mp
  exact short_centers_commute Γ (fun v => (source_Z_Q_U h v).1) hS x z (by
    change (graph Γ).dist x y + 1 < b Γ at hd
    omega)

private theorem reflected_span_commutes
    (h : LocallyRankOneTriple P B)
    (hS : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (hb5 : b (family P) = 5)
    {a beta x w v a' : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hbx : (graph (family P)).Adj beta x)
    (hxw : (graph (family P)).Adj x w) (hwv : (graph (family P)).Adj w v)
    (hva : (graph (family P)).Adj v a')
    (hwhole : V (family P) beta 1 = Z (family P) a ⊔ Z (family P) x)
    (hesc : ¬ Z (family P) a ≤ Q (family P) a')
    {u : G} (huw : u • w = w)
    (hfixed : ∀ t ∈ V (family P) beta 1, ∀ z ∈ V (family P) (u • beta) 1,
      Commute z t → z ∉ Z (family P) (u • x) →
        t ∈ centralizer (V (family P) (u • beta) 1 : Set G))
    (href : ∀ t ∈ Z (family P) a, t ∉ Q (family P) a' → Commute (u*t*u⁻¹) t) :
    ⁅V (family P) beta 1,V (family P) (u • beta) 1⁆ = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  have hact : ∀ (g : G) {v w : Vertex Γ}, (graph Γ).Adj v w →
      (graph Γ).Adj (g • v) (g • w) :=
    fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso Γ g).toHom.map_adj he
  have huxw : (graph Γ).Adj (u • x) w := by simpa only [huw] using hact u hxw
  have hZQ : Z Γ x ≤ Q Γ a' := by
    apply Z_le_Q_of_dist_lt_b Γ (fun y => (source_Z_Q_U h y).1) hS
    have hh := (graph Γ).dist_le (Walk.cons hxw (Walk.cons hwv (Walk.cons hva Walk.nil)))
    simp only [Walk.length_cons,Walk.length_nil] at hh
    change b Γ = 5 at hb5
    omega
  have hA : Z Γ a ≤ centralizer (V Γ (u • beta) 1 : Set G) := by
    apply subgroup_le_of_outside hesc
    intro t ht htQ
    have htV := CommutingNontrivial.Z_neighbor_le_V Γ hab.symm ht
    have htV' : u*t*u⁻¹ ∈ V Γ (u • beta) 1 := by
      rw [V_translate]
      exact mem_map_of_mem (MulAut.conj u).toMonoidHom htV
    have htX : u*t*u⁻¹ ∉ Z Γ (u • x) := by
      rw [Z_translate]
      intro he
      have hh : t ∈ Z Γ x := by
        obtain ⟨t',ht',he'⟩ := he
        have he'' : t' = t := (MulAut.conj u).injective he'
        exact he'' ▸ ht'
      exact htQ (hZQ hh)
    exact hfixed t htV (u*t*u⁻¹) htV' (href t ht htQ) htX
  have hC : Z Γ x ≤ centralizer (V Γ (u • beta) 1 : Set G) := by
    apply short_center_centralizes_span h hS
    change (graph Γ).dist x (u • beta) + 1 < b Γ
    have hh := (graph Γ).dist_le (Walk.cons hxw (Walk.cons huxw.symm (Walk.cons (hact u hbx.symm) Walk.nil)))
    simp only [Walk.length_cons,Walk.length_nil] at hh
    change b Γ = 5 at hb5
    omega
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact hwhole.le.trans (sup_le hA hC)

private theorem bool_two {i j k : Bool} (h1 : i ≠ j) (h2 : j ≠ k) : i = k := by
  cases i <;> cases j <;> cases k <;> simp_all

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- Characteristic two excludes the actual critical distance five. -/
theorem reduced_critical_distance_five_false
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
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) : False := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,v₀,hx,hdx,hv₀,hdv,hwhole,hcard,hcent,hcent',hR,h4⟩ :=
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
  have hSyl := Reduction.reduced_kernel_sylow h
  have hZ := fun y => (source_Z_Q_U ht y).1
  have hb1 : 1 < b Γ := by change b Γ = 5 at hb5; omega
  have hd4 : (graph Γ).dist beta a' = 4 := by
    change (graph Γ).dist beta a' + 1 = b Γ at hd
    change b Γ = 5 at hb5
    omega
  have hdx3 : (graph Γ).dist x a' = 3 := by
    change (graph Γ).dist x a' + 2 = b Γ at hdx
    change b Γ = 5 at hb5
    omega
  obtain ⟨p,hp,hpe⟩ : ∃ p : BasedWalk (graph Γ) 3 x,
      p.Nonbacktracking ∧ p.endpoint = a' := by
    rw [←hdx3]
    exact BasedWalk.exists_geodesic ((connected Γ ht.generate) x a')
  let w := p.1.val
  let v := p.2.1.val
  have hxw : (graph Γ).Adj x w := p.1.property
  have hwv : (graph Γ).Adj w v := p.2.1.property
  have hva : (graph Γ).Adj v a' := by
    change p.2.2.1.val = a' at hpe
    exact hpe ▸ p.2.2.1.property
  have hvx : v ≠ x := hp.1
  have haw : a' ≠ w := by
    change p.2.2.1.val = a' at hpe
    exact hpe ▸ hp.2.1
  have hwb : w ≠ beta := by
    intro he
    have hh := (graph Γ).dist_le (Walk.cons hwv (Walk.cons hva Walk.nil))
    simp only [Walk.length_cons,Walk.length_nil,he,hd4] at hh
    omega
  have hav : a.type = v.type := by
    have hne1 := hab.1
    have hne2 := hx.1
    have hne3 := hxw.1
    have hne4 := hwv.1
    exact (bool_two hne1 hne2).trans (bool_two hne3 hne4)
  obtain ⟨k,hkv⟩ := (same_orbit_iff Γ a v).mpr hav
  obtain ⟨_,fv,_,_,_⟩ := local_quotient_parameter_transport ht k hkv
  obtain ⟨g,hg,hga',hgw⟩ : ∃ g : Reduction.G₀ L S₀,
      g ∈ graphLocalGroup Γ v ∧ g • a' = w ∧ g • w = a' := by
    obtain ⟨g,hg1,hg2,_⟩ := linear_local_neighbor_exchange ht hB hS hva hwv.symm (fv.symm.trans eα)
    exact ⟨g,g.property,hg1,hg2⟩
  have hgv : g • v = v := sylowGenerated_le _ hg
  have hact : ∀ (g : Reduction.G₀ L S₀) {v w : Vertex Γ}, (graph Γ).Adj v w →
      (graph Γ).Adj (g • v) (g • w) :=
    fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso Γ g).toHom.map_adj he
  have h56 : (graph Γ).Adj a' (g • x) := by
    simpa only [hgw] using hact g hxw.symm
  have h64 : g • x ≠ v := by
    rw [←hgv]
    exact fun he => hvx ((MulAction.toPerm g).injective he).symm
  have h75 : g • beta ≠ a' := by
    rw [←hgw]
    exact fun he => hwb ((MulAction.toPerm g).injective he).symm
  have hc' := criticalPair_translate Γ hc g
  have hesc' : ¬ Z Γ (g • a) ≤ Q Γ w := by
    intro he
    apply hc'.2
    rw [hga']
    exact he.trans (source_Z_Q_U ht w).2
  obtain ⟨u,hu,huQ⟩ := SetLike.not_le_iff_exists.mp hesc'
  have hu4 : u ∈ Q Γ v := by
    apply Z_le_Q_of_dist_lt_b Γ hZ hSyl _ _ ?_ hu
    have hh := (graph Γ).dist_le (Walk.cons (hact g hab)
      (Walk.cons (hact g hx) (Walk.cons (hact g hxw) (Walk.cons (hact g hwv) Walk.nil))))
    simp only [Walk.length_cons,Walk.length_nil,hgv] at hh
    change b Γ = 5 at hb5
    omega
  have huw : u • w = w := (source_Z_Q_U ht v).2.trans
    ((ballKernel_one_le_edge Γ hwv.symm).trans inf_le_right) hu4
  have hbw : beta.type = w.type := by
    exact bool_two hx.1 hxw.1
  obtain ⟨j,hjw⟩ := (same_orbit_iff Γ beta w).mpr hbw
  obtain ⟨_,fw,_,_,_⟩ := local_quotient_parameter_transport ht j hjw
  have humove := linear_core_element_moves_other_neighbor ht hB hS hwv hxw.symm hvx
    (fw.symm.trans eβ) hu4 huQ
  have href : ∀ t ∈ Z Γ a, t ∉ Q Γ a' → Commute (u*t*u⁻¹) t := by
    intro t htZ htQ
    exact reduced_critical_distance_five_reflected_elements h hc hab hd hb5 hcomm h8 hob
      Mα Mβ Mα' Mαsource a beta x w v a' (g • x) (g • beta) (g • a)
      hab hx hxw hwv hva h56 (hact g hx.symm) (hact g hab.symm)
      hwb hvx haw h64 h75 rfl t htZ htQ u hu huQ
  have hesc : ¬ Z Γ a ≤ Q Γ a' := fun he => hc.2 (he.trans (source_Z_Q_U ht a').2)
  have hwu : w ≠ u • beta := by
    rw [←huw]
    exact fun he => hwb ((MulAction.toPerm u).injective he)
  have huxw' : (graph Γ).Adj (u • x) w := by simpa only [huw] using hact u hxw
  have hfixed := reduced_critical_distance_five_fixed_element h hc hab hd hb5 hcomm h8 hob
    Mα Mβ Mα' Mαsource (u • beta) (u • x) w x beta
    (hact u hx) huxw' hxw.symm hx.symm hwu humove.symm hwb.symm rfl
  have hzero := reflected_span_commutes ht hSyl hb5 hab hx hxw hwv hva hwhole hesc
    huw hfixed href
  have huxw : (graph Γ).Adj w (u • x) := by simpa only [huw] using hact u hxw.symm
  have hubw : u • beta ≠ w := by
    rw [←huw]
    exact fun he => hwb ((MulAction.toPerm u).injective he).symm
  have hpath := h4 beta x w (u • x) (u • beta) hx hxw huxw (hact u hx.symm)
    hwb humove hubw rfl
  have hzw : Z Γ w = ⊥ := hpath.symm.trans hzero
  obtain ⟨r,hr⟩ := Subgroup.CosetGeometry.exists_smul_base Γ w
  rw [←hr,Z_translate] at hzw
  exact base_Z_ne_bot ht w.type ((map_eq_bot_iff_of_injective _ (MulAut.conj r).injective).mp hzw)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
