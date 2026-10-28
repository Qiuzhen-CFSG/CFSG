module
public import Theory.Representation.BinaryConjugationSection.SL2DisplacementCard
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.WholeSpan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeTorus

/-!
# The four-edge commutator identity at critical distance five

For a central-omega vertex, the centers of two distinct neighbors intersect
in exactly its center. The two actual neighboring cores generate its local
group; the source core-product formula supplies the remaining normalization.

The proved 9.8 bound transports to the first and last interior vertices of
every nonbacktracking four-edge path. Their intersection is the middle
center. The actual natural residual action has full Sylow image and hence
moves at least one field line, making this containment an equality.

The reduced F1.11 application constructs the quotient markings and natural
sections and retains every earlier-source premise. It assumes b=5; neither
the reduction to five nor the subsequent characteristic-two contradiction
is asserted here. No tree assumption is used.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), 9.11,
printed p.151, displayed identity (*); 9.4(a) and 9.8, pp.143--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem type_eq_of_common_neighbor {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
  cases i <;> cases j <;> cases k <;> simp_all

private theorem type_eq_of_two_edges {Γ : Bool → Subgroup G} {v w z : Vertex Γ}
    (hv : (graph Γ).Adj v w) (hz : (graph Γ).Adj w z) : v.type = z.type :=
  type_eq_of_common_neighbor hv.1 hz.1.symm

/-- Distinct neighboring centers intersect in the literal local central omega. -/
theorem linear_neighbor_centers_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z) (hne : w ≠ z)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (hω : Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,K)) :
    Z (family P) w ⊓ Z (family P) z = Z (family P) v := by
  let := finite_endpoints h
  let Γ := family P
  let I := Z Γ w ⊓ Z Γ z
  have hwe := core_escape_of_intersection_obstruction Γ (hob w v hw.symm)
  have hze := core_escape_of_intersection_obstruction Γ (hob z v hz.symm)
  have hwC : Q Γ w ≤ centralizer (I : Set G) :=
    (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ w
      (source_Z_Q_U h w).1)).trans (centralizer_le inf_le_left)
  have hzC : Q Γ z ≤ centralizer (I : Set G) :=
    (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ z
      (source_Z_Q_U h z).1)).trans (centralizer_le inf_le_right)
  have hIC : I ≤ centralizer (graphLocalGroup Γ v : Set G) := by
    apply le_centralizer_iff.mpr
    rw [linear_neighbor_core_generation h hB hS hw hz hne hwe hze e]
    apply sup_le (sup_le ?_ hwC) hzC
    rw [linear_middle_core_product h hB hS hob hw hz hne e ew]
    exact sup_le (inf_le_left.trans hwC) (inf_le_left.trans hzC)
  apply le_antisymm ?_ (le_inf (hω ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hw)
    (hω ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hz))
  intro x hx
  rw [hω]
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨neighbor_core_le_localGroup h hB hS hw (map_subtype_le _ ((source_Z_Q_U h w).1 hx.1)),
      hIC hx, ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hx.1)).2.2⟩

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

/-- Transport the 9.8 bound to every four-edge path in the same orbit. -/
theorem four_path_commutator_le_first_center
    (h : LocallyRankOneTriple P B)
    (htrans : ∀ v : Vertex (family P), RootPathTransitive (graph (family P)) G v 4)
    {beta x a' : Vertex (family P)} (hx : (graph (family P)).Adj beta x)
    (hd : (graph (family P)).dist beta a' = 4)
    (hdx : (graph (family P)).dist x a' = 3)
    (hR : ⁅V (family P) beta 1,V (family P) a' 1⁆ ≤ Z (family P) x)
    {d₀ d₁ d₂ d₃ d₄ : Vertex (family P)}
    (h01 : (graph (family P)).Adj d₀ d₁) (h12 : (graph (family P)).Adj d₁ d₂)
    (h23 : (graph (family P)).Adj d₂ d₃) (h34 : (graph (family P)).Adj d₃ d₄)
    (h02 : d₂ ≠ d₀) (h13 : d₃ ≠ d₁) (h24 : d₄ ≠ d₂)
    (htype : beta.type = d₀.type) :
    ⁅V (family P) d₀ 1,V (family P) d₄ 1⁆ ≤ Z (family P) d₁ := by
  let := finite_endpoints h
  obtain ⟨g,hg,hgx,hga'⟩ := four_path_transport_first h htrans hx hd hdx
    h01 h12 h23 h34 h02 h13 h24 htype
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hR
  rwa [map_commutator,←V_translate,←V_translate,←Z_translate,hg,hgx,hga'] at hh


/-- The forward and reversed bounds meet in the middle path center. -/
theorem four_path_commutator_le_middle_center
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {a beta x a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hx : (graph (family P)).Adj beta x)
    (hd : (graph (family P)).dist beta a' = 4)
    (hdx : (graph (family P)).dist x a' = 3)
    (hω : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hR : ⁅V (family P) beta 1,V (family P) a' 1⁆ ≤ Z (family P) x)
    {d₀ d₁ d₂ d₃ d₄ : Vertex (family P)}
    (h01 : (graph (family P)).Adj d₀ d₁) (h12 : (graph (family P)).Adj d₁ d₂)
    (h23 : (graph (family P)).Adj d₂ d₃) (h34 : (graph (family P)).Adj d₃ d₄)
    (h02 : d₂ ≠ d₀) (h13 : d₃ ≠ d₁) (h24 : d₄ ≠ d₂)
    (htype : beta.type = d₀.type) :
    ⁅V (family P) d₀ 1,V (family P) d₄ 1⁆ ≤ Z (family P) d₂ := by
  let Γ := family P
  let := finite_endpoints h
  have ht := fun v => adjacent_linear_short_path_transitive h hB hS hob hab ea eb v 4 le_rfl
  have hb2 : beta.type = d₂.type := htype.trans (type_eq_of_two_edges h01 h12)
  have hb4 : beta.type = d₄.type := hb2.trans (type_eq_of_two_edges h23 h34)
  have ha1 : a.type = d₁.type := type_eq_of_common_neighbor hab.1 (htype ▸ h01.1.symm)
  have hfirst := four_path_commutator_le_first_center h ht hx hd hdx hR
    h01 h12 h23 h34 h02 h13 h24 htype
  have hlast := four_path_commutator_le_first_center h ht hx hd hdx hR
    h34.symm h23.symm h12.symm h01.symm (Ne.symm h24) (Ne.symm h13) (Ne.symm h02) hb4
  rw [commutator_comm] at hlast
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta d₂).mpr hb2
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
  obtain ⟨k,hk⟩ := (same_orbit_iff Γ a d₁).mpr ha1
  obtain ⟨_,f',_,_,_⟩ := local_quotient_parameter_transport h k hk
  have hω2 : Z Γ d₂ = omegaCenterIn (graphLocalGroup Γ d₂) := by
    have hh := graphLocalGroup_conjugate h g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    rw [←hg,Z_translate,hh,←NilesRankOneKernel.omegaCenterIn_map_injective _
      (MulAut.conj g).injective,hω]
  exact (le_inf hfirst hlast).trans_eq (linear_neighbor_centers_intersection h hB hS
    h12.symm h23 (Ne.symm h13) hob hω2 (f.symm.trans eb) (f'.symm.trans ea))


universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The exact source identity (*) of 9.11 on the original reduced graph,
with both quotient markings and natural actions retained. -/
theorem reduced_critical_distance_five_path_commutator
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
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧ NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            (let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
             letI : Algebra (ZMod 2) K := ZMod.algebra K 2
             ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
               (T : Sylow 2 SL(2,K)),
               (∀ (l : H) (z : Additive (Z Γ a)),
                 ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                   (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
               Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
               ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                 ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ x v : Vertex Γ,
              (graph Γ).Adj beta x ∧ (graph Γ).dist x a' + 2 = b Γ ∧
              (graph Γ).Adj a' v ∧ (graph Γ).dist beta v + 2 = b Γ ∧
              V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
              V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x ∧
              V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) = Z Γ v ∧
              ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ v ⊓ Z Γ x ∧
              (∀ d₀ d₁ d₂ d₃ d₄ : Vertex Γ,
                (graph Γ).Adj d₀ d₁ → (graph Γ).Adj d₁ d₂ →
                (graph Γ).Adj d₂ d₃ → (graph Γ).Adj d₃ d₄ →
                d₂ ≠ d₀ → d₃ ≠ d₁ → d₄ ≠ d₂ → beta.type = d₀.type →
                ⁅V Γ d₀ 1,V Γ d₄ 1⁆ = Z Γ d₂) := by
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
  have hZ := fun y => (source_Z_Q_U ht y).1
  have hSyl := Reduction.reduced_kernel_sylow h
  have hb1 : 1 < b Γ := by change b Γ = 5 at hb5; omega
  have hb2 : 2 < b Γ := by change b Γ = 5 at hb5; omega
  have hd4 : (graph Γ).dist beta a' = 4 := by
    change (graph Γ).dist beta a' + 1 = b Γ at hd
    change b Γ = 5 at hb5
    omega
  have hdx3 : (graph Γ).dist x a' = 3 := by
    change (graph Γ).dist x a' + 2 = b Γ at hdx
    change b Γ = 5 at hb5
    omega
  obtain ⟨hodd,_,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  have htrans := fun y => adjacent_linear_short_path_transitive ht hB hS hob hab eα eβ y 4 le_rfl
  let := Z_elementary Γ hZ a
  have hnat₀ := hnat
  obtain ⟨ρα,Tα,hactα,hfaithα,hna,Eα,hEα⟩ := hnat
  obtain ⟨_,hcb⟩ := linear_natural_neighbor_center_orders ht hB hS hab
    (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
    ρα hactα hfaithα ⟨Tα,hna⟩
  rw [heq] at hcb
  have htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥ := by
    by_contra he
    have hh := h8 a beta a' hc hab hd hb1 hcomm he
    omega
  have hescape := linear_critical_reciprocal_escape ht hB hS hc hab hd hb2 hodd eα eβ
  obtain ⟨_,hi',_⟩ := reduced_large_neighbor_linear_indices h hc hab hd hb1 hcomm htriv hescape
    (fun z hz hzc hzcomm he => by
      have hh := h8 z a' beta hzc hz (by rwa [SimpleGraph.dist_comm]) hb1 hzcomm he
      omega) hn hF eβ
  let H := graphLocalGroup Γ beta
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let A := (V Γ beta 1).subgroupOf H
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  have hres₀ := hres
  obtain ⟨hb2β,σ,Tβ,hσ,hfaithβ,hnatβ,Eβ,hEβ⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate hZ hSyl beta hb2β H
  have hcomp : σ.comp q = Representation.NormalElementaryQuotient.fixedQuotientAction A (pResidual 2 H) :=
    MonoidHom.ext hσ
  obtain ⟨⟨c⟩,_,_⟩ := neighborhood_residual_section ht hSyl beta hb2β H
    (core_le_graphLocalGroup ht beta) (sylowGenerated_le _)
  have hDH : V Γ a' 1 ≤ H := neighbor_le_graphLocalGroup ht hSyl a' beta hb1
    (by
      change (graph Γ).dist a' beta + 1 ≤ b Γ
      rw [SimpleGraph.dist_comm]
      exact hd.le)
  let := V_elementary Γ ht.generate hZ hSyl a' (r := 1) (by simpa using hb2)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q Γ beta := hk ▸ graphLocalGroup_core ht beta
  let I := ((V Γ a' 1).subgroupOf H).map q
  have hcI : Nat.card I = Nat.card F := by
    change Nat.card (((V Γ a' 1).subgroupOf H).map q) = Nat.card F
    rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
      hkmap,map_subgroupOf_eq_of_le hDH]
    exact hi'
  have hpI : IsPGroup 2 I := (IsElementaryAbelian.isPGroup 2 (V Γ a' 1)).comap_subtype.map q
  obtain ⟨T,hT⟩ := hpI.exists_le_sylow
  have hIT : I = T := eq_of_le_of_card_ge hT (by
    rw [hcI]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).ge)
  have hquad : IsQuadratic σ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) Tβ T
    exact SL2SylowFixedRecognition.quadratic_conjugate σ hnatβ.2.2 g
  let : Finite (V Γ beta 1) := Finite.of_injective
    (inclusion ((V_le_Q Γ ht.generate hZ hSyl beta (r := 1) hb1).trans (Q_le_stabilizer Γ beta)))
    (inclusion_injective _)
  have hlow : Nat.card F ≤ Nat.card (⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) := by
    rw [commutator_comm]
    exact Representation.BinaryConjugationSection.natural_section_commutator_card_ge q σ
      (hcomp.symm ▸ c) hfaithβ T hn hF ⟨hnatβ.1,hnatβ.2.1,hquad⟩ (V Γ a' 1) hDH hIT
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres₀,K,instK,finK,charK,m,hm,hK,eα,
    heq,hcQ,hcV,hnat₀,x,v,hx,hdx,hv,hdv,hwhole,hcard,hcent,hcent',hR,?_⟩
  intro d₀ d₁ d₂ d₃ d₄ h01 h12 h23 h34 h02 h13 h24 htype
  have hbound := four_path_commutator_le_middle_center ht hB hS hob hab hx hd4 hdx3 hω eα eβ
    (hR.trans inf_le_right) h01 h12 h23 h34 h02 h13 h24 htype
  let : Finite (Z Γ d₂) := Finite.of_injective (inclusion (Z_le_stabilizer Γ d₂)) (inclusion_injective _)
  have htype2 : beta.type = d₂.type := htype.trans (type_eq_of_two_edges h01 h12)
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta d₂).mpr htype2
  have hcd₂ : Nat.card (Z Γ d₂) = Nat.card F := by
    have hh := card_map_of_injective (K := Z Γ beta)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [←Z_translate,hg] at hh
    exact hh.trans hcb
  obtain ⟨t,ht₀,htx,ht₄⟩ := four_path_transport_first ht htrans hx hd4 hdx3
    h01 h12 h23 h34 h02 h13 h24 htype
  have hcr := card_map_of_injective (K := ⁅V Γ beta 1,V Γ a' 1⁆)
    (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  rw [map_commutator,←V_translate,←V_translate] at hcr
  have htV₀ := congrArg (fun y : Vertex Γ => V Γ y 1) ht₀
  have htV₄ := congrArg (fun y : Vertex Γ => V Γ y 1) ht₄
  have hcr' : Nat.card (⁅V Γ d₀ 1,V Γ d₄ 1⁆ : Subgroup _) = Nat.card (⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup _) := by
    have he := congrArg₂ (fun (A B : Subgroup (Reduction.G₀ L S₀)) => ⁅A,B⁆) htV₀ htV₄
    exact (congrArg (fun A : Subgroup (Reduction.G₀ L S₀) => Nat.card A) he).symm.trans hcr
  exact eq_of_le_of_card_ge hbound (by rw [hcd₂,hcr']; exact hlow)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
