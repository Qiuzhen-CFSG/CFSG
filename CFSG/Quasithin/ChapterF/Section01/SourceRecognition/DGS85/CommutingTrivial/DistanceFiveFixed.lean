module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ElementCentralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceFiveReflections
/-!
# Fixed elements force a whole path-neighborhood centralizer

At critical distance five the sharp natural-section index says that an
opposing element either centralizes the entire neighborhood or fixes exactly
the first path center. The source short-path transitivity transports this
alternative to every nonbacktracking four-edge path of the same vertex type.
All actors are the original subgroups, and the actual quotient actions are
those constructed in `ElementCentralizers`.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.11, printed p.151, the passage from reflected elements to whole spans.
This is an intermediate implication; distance five is still assumed.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem four_path_transport_first
    (h : LocallyRankOneTriple P B)
    (htrans : ∀ v : Vertex (family P), RootPathTransitive (graph (family P)) G v 4)
    {beta x a' : Vertex (family P)} (hx : (graph (family P)).Adj beta x)
    (hd : (graph (family P)).dist beta a' = 4)
    (hdx : (graph (family P)).dist x a' = 3)
    {d₀ d₁ d₂ d₃ d₄ : Vertex (family P)}
    (h01 : (graph (family P)).Adj d₀ d₁) (h12 : (graph (family P)).Adj d₁ d₂)
    (h23 : (graph (family P)).Adj d₂ d₃) (h34 : (graph (family P)).Adj d₃ d₄)
    (h02 : d₂ ≠ d₀) (h13 : d₃ ≠ d₁) (h24 : d₄ ≠ d₂)
    (htype : beta.type = d₀.type) :
    ∃ g : G, g • beta = d₀ ∧ g • x = d₁ ∧ g • a' = d₄ := by
  let Γ := family P
  let hact : GraphAction (graph Γ) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso Γ g).toHom.map_adj he⟩
  obtain ⟨p,hp,hpe⟩ : ∃ p : BasedWalk (graph Γ) 3 x,
      p.Nonbacktracking ∧ p.endpoint = a' := by
    rw [←hdx]
    exact BasedWalk.exists_geodesic ((connected Γ h.generate) x a')
  let q : BasedWalk (graph Γ) 4 beta := ⟨⟨x,hx⟩,p⟩
  have hqe : q.endpoint = a' := hpe
  have hq : q.Nonbacktracking := nonbacktracking_of_geodesic q (by rw [hqe,hd])
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta d₀).mpr htype
  have hg0 : g⁻¹ • d₀ = beta := by rw [←hg,inv_smul_smul]
  let r : BasedWalk (graph Γ) 4 beta :=
    ⟨⟨g⁻¹ • d₁,by
      change (graph Γ).Adj beta (g⁻¹ • d₁)
      simpa only [hg0] using hact.map_adj g⁻¹ h01⟩,
      ⟨⟨g⁻¹ • d₂,hact.map_adj g⁻¹ h12⟩,
        ⟨⟨g⁻¹ • d₃,hact.map_adj g⁻¹ h23⟩,
          ⟨⟨g⁻¹ • d₄,hact.map_adj g⁻¹ h34⟩,PUnit.unit⟩⟩⟩⟩
  have hr : r.Nonbacktracking := by
    refine ⟨?_,?_,?_,trivial⟩
    · change g⁻¹ • d₂ ≠ beta
      rw [←hg0]
      exact fun he => h02 ((MulAction.toPerm g⁻¹).injective he)
    · exact fun he => h13 ((MulAction.toPerm g⁻¹).injective he)
    · exact fun he => h24 ((MulAction.toPerm g⁻¹).injective he)
  obtain ⟨k,hk,hkr⟩ := htrans beta q r hq hr
  have hkx : k • x = g⁻¹ • d₁ := by
    have hh := congrArg (fun l : List (Vertex Γ) => l[1]?) hkr
    simpa only [q,r,BasedWalk.vertices,List.map_cons,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.some.injEq] using hh
  have hka' : k • a' = g⁻¹ • d₄ := by
    have hh := endpoint_smul_of_vertices hact k q r hkr
    change k • q.endpoint = g⁻¹ • d₄ at hh
    rwa [hqe] at hh
  refine ⟨g*k,?_,?_,?_⟩
  · rw [mul_smul,hk,hg]
  · rw [mul_smul,hkx,smul_inv_smul]
  · rw [mul_smul,hka',smul_inv_smul]


private theorem mem_cyclic_centralizer_of_commute {x t : G} (hc : Commute x t) :
    x ∈ centralizer (zpowers t : Set G) := by
  rintro y ⟨k,rfl⟩
  exact (hc.zpow_right k).eq.symm

private theorem fixes_whole_of_fixed_outside_map (A B C : Subgroup G)
    (hc : ∀ t ∈ B, ∀ z ∈ A, Commute z t → z ∉ C → t ∈ centralizer (A : Set G))
    (e : G ≃* G) :
    ∀ t ∈ B.map e.toMonoidHom, ∀ z ∈ A.map e.toMonoidHom,
      Commute z t → z ∉ C.map e.toMonoidHom →
      t ∈ centralizer (A.map e.toMonoidHom : Set G) := by
  rintro _ ⟨t,ht,rfl⟩ _ ⟨z,hz,rfl⟩ hzt hzC _ ⟨w,hw,rfl⟩
  have hh := hc t ht z hz (Commute.of_map e.injective hzt)
    (fun he => hzC (mem_map_of_mem e.toMonoidHom he))
  exact (e.map_mul w t).symm.trans ((congrArg e (hh w hw)).trans (e.map_mul t w))

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- An opposing element fixing a vector outside the first path center fixes the whole span. -/
theorem reduced_critical_distance_five_fixed_element
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
    ∀ d₀ d₁ d₂ d₃ d₄ : Vertex Γ,
      (graph Γ).Adj d₀ d₁ → (graph Γ).Adj d₁ d₂ →
      (graph Γ).Adj d₂ d₃ → (graph Γ).Adj d₃ d₄ →
      d₂ ≠ d₀ → d₃ ≠ d₁ → d₄ ≠ d₂ → beta.type = d₀.type →
      ∀ t ∈ V Γ d₄ 1, ∀ z ∈ V Γ d₀ 1,
        Commute z t → z ∉ Z Γ d₁ → t ∈ centralizer (V Γ d₀ 1 : Set (Reduction.G₀ L S₀)) := by
  have hb : 3 < b (Reduction.reducedFamily L S₀) := by omega
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,v,hx,hdx,hv,hdv,hwhole,hcard,hcent,hcent',hR,hpoint,hpoint'⟩ :=
    reduced_critical_large_distance_element_centralizers h hc hab hd hb hcomm h8 hob Mα Mβ Mα' Mαsource
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
  obtain ⟨_,hrev,_,_,_⟩ := reduced_large_distance_natural_section h h8 hob
    hc hab hd hb hcomm hn hF eα eβ
  have hfixed : ∀ t ∈ V Γ a' 1, ∀ z ∈ V Γ beta 1,
      Commute z t → z ∉ Z Γ x → t ∈ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) := by
    intro t htV z hz hzt hzX
    by_cases htQ : t ∈ Q Γ beta
    · exact (commutator_eq_bot_iff_le_centralizer.mp hrev) ⟨htV,htQ⟩
    · exact (hzX ((hpoint t htV htQ).le ⟨hz,mem_cyclic_centralizer_of_commute hzt⟩)).elim
  have hd4 : (graph Γ).dist beta a' = 4 := by
    change (graph Γ).dist beta a' + 1 = b Γ at hd
    change b Γ = 5 at hb5
    omega
  have hdx3 : (graph Γ).dist x a' = 3 := by
    change (graph Γ).dist x a' + 2 = b Γ at hdx
    change b Γ = 5 at hb5
    omega
  dsimp only
  intro d₀ d₁ d₂ d₃ d₄ h01 h12 h23 h34 h20 h31 h42 htype
  obtain ⟨g,hg,hgx,hga'⟩ := four_path_transport_first ht
    (fun y => adjacent_linear_short_path_transitive ht hB hS hob hab eα eβ y 4 le_rfl)
    hx hd4 hdx3 h01 h12 h23 h34 h20 h31 h42 htype
  have hh := fixes_whole_of_fixed_outside_map (V Γ beta 1) (V Γ a' 1) (Z Γ x) hfixed (MulAut.conj g)
  rw [←V_translate,←V_translate,←Z_translate] at hh
  have hV0 := congrArg (fun y : Vertex Γ => V Γ y 1) hg
  have hV4 := congrArg (fun y : Vertex Γ => V Γ y 1) hga'
  have hZ1 := congrArg (fun y : Vertex Γ => Z Γ y) hgx
  intro t htV z hzV hzt hzZ
  exact centralizer_le hV0.ge (hh t (hV4.ge htV) z (hV0.ge hzV) hzt
    (fun he => hzZ (hZ1.le he)))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
