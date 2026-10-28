module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoPathCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualPairing

/-!
# A path-compatible Cartan and the tested residual

For the critical path (t, α, β, u, y), choose one full odd edge complement
and corrected local transporters. The resulting opposite-center residual has
its literal four-core description and direct decomposition. Its intersection
with the terminal core centralizes both transported alpha tori; the
three-subgroup lemma then makes their beta intersection act with displacement
centralizing the tested residual.

The proof uses the natural center actions and (10.4)(c): odd local tori lie in
the two-residual, so their displacement lies both in a center and its disjoint
residual. All assertions are also transported to the original completion.
This supplies the first part of DGS85 (10.8), printed pp.159--161. Escape from
Dα, the terminal-core intersection equality, residual order, and regular
paths remain separate obligations. The witnesses here are chosen for the
prescribed continuation y.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile

private theorem odd_intersection_le_residual {X : Type*} [Group X]
    (K A : Subgroup X) [Finite K] (ho : Odd (Nat.card K)) :
    K ⊓ A ≤ (pResidual 2 A).map A.subtype := by
  intro k hk
  refine ⟨⟨k,hk.2⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
  simpa only [Subgroup.orderOf_mk] using
    (Nat.coprime_two_left.mpr ho).of_dvd_right
      (_root_.orderOf_dvd_natCard (⟨k,hk.1⟩ : K))

universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- One path-compatible Cartan supplies residual decomposition and the source
three-subgroup centralization at the chosen terminal vertex. -/
theorem original_bTwo_path_cartan_residual
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    let E := stabilizer F α ⊓ stabilizer F β
    ∃ K : Subgroup (G₀ L S),
      K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
        stabilizer F u ⊓ stabilizer F y ∧
      Disjoint K (E.pCoreIn 2) ∧ K ⊔ E.pCoreIn 2 = E ∧
      Odd (Nat.card K) ∧ IsMulCommutative K ∧
      K = (K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F β) ∧
      ∃ g ∈ graphLocalGroup F α, g ∈ normalizer (K : Set (G₀ L S)) ∧ g • β = t ∧
      ∃ a ∈ graphLocalGroup F β, a ∈ normalizer (K : Set (G₀ L S)) ∧ a • α = u ∧
      let W := Z F u ⊔ Z F (g • u)
      let R := bTwoResidual F β t u (g • u)
      let J := R ⊓ Q F y
      W ⊔ Q F α = graphLocalGroup F α ∧
      R = (D F β t ⊓ Q F u) ⊓ Q F (g • u) ∧
      D F β t = Z F α ⊔ R ∧ Disjoint (Z F α) R ∧
      Disjoint R (Z F u) ∧
      K ≤ normalizer (W : Set (G₀ L S)) ⊓ normalizer (R : Set (G₀ L S)) ⊓
        normalizer (J : Set (G₀ L S)) ∧
      R ≤ centralizer ((K ⊓ graphLocalGroup F α : Subgroup (G₀ L S)) : Set (G₀ L S)) ∧
      J ≤ centralizer (((K ⊓ graphLocalGroup F α) ⊔
        (K ⊓ graphLocalGroup F u) : Subgroup (G₀ L S)) : Set (G₀ L S)) ∧
      ⁅V F β 1 ⊓ Q F α, ((K ⊓ graphLocalGroup F α) ⊔
        (K ⊓ graphLocalGroup F u)) ⊓ (K ⊓ graphLocalGroup F β)⁆ ≤
          centralizer (J : Set (G₀ L S)) ∧
      (K ⊓ graphLocalGroup F α).conjBy a = K ⊓ graphLocalGroup F u := by
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,hprod,⟨g,hg,hgK,hgt⟩,⟨a,ha,haK,hau⟩⟩ :=
    original_bTwo_path_cartan_transport h hc hne hb hβu ht htne hy hyne
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c,c',hactor,hactor',_,_,_⟩ :=
    Reduction.reduced_bTwo_equal_field_profile_actions h hc hne hb hab hβu
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hS := reduced_kernel_sylow h
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  let g' : c.actor := ⟨g,hactor ▸ hg⟩
  have hop : c.quotient g' ∉ normalizer (c.imageSylow : Set SL(2,k₀)) := by
    intro he
    exact htne (hgt.symm.trans (c.normalizer_fixes_neighbor H g' he))
  obtain ⟨d,hdactor,hker⟩ := c.exists_oppositeGeometry H hS hb g' hgt hop
  have hr := d.residual_eq_source H hS hb (hdactor.symm ▸ hω)
  let W := Z F u ⊔ Z F (g • u)
  let R := bTwoResidual F β t u (g • u)
  let J := R ⊓ Q F y
  have hRW : R ≤ centralizer (W : Set (G₀ L S)) := inf_le_right
  have hRQ : R ≤ Q F α := inf_le_left.trans d.separated
  have hrR : d.residual = R := hr
  have hdis : Disjoint (Z F α) R := by
    rw [←hrR]
    exact (disjoint_iff.mpr (bot_unique (hker.trans hω.le))).symm
  have hdis' : Disjoint R (Z F u) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hxm : x ∈ Z F β :=
      (c.central_critical_intersections H (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) hb hcentral).2.1 ▸ ⟨hx.2,hRQ hx.1⟩
    exact hdis.le_bot ⟨center_le_of_central_neighbor H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hab hcentral hxm,hx.1⟩
  have hfixg : K ≤ stabilizer F (g • u) := by
    intro k hk
    have hh := (mem_normalizer_iff.mp ((normalizer (K : Set (G₀ L S))).inv_mem hgK) k).mp hk
    have he : (g⁻¹*k*g) • u = u := (hfix (by simpa only [inv_inv] using hh)).1.2
    have he' := congrArg (g • ·) he
    change k • (g • u) = g • u
    simpa only [mul_smul,smul_inv_smul] using he'
  have nZ (v : Vertex F) : stabilizer F v ≤ normalizer (Z F v : Set (G₀ L S)) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F v)).mp (Z_normal F v)
  have nQ (v : Vertex F) : stabilizer F v ≤ normalizer (Q F v : Set (G₀ L S)) :=
    CommutingNontrivial.stabilizer_normalizes_Q F v
  have hnW : K ≤ normalizer (W : Set (G₀ L S)) :=
    (le_inf ((show K ≤ stabilizer F u from fun _ hk => (hfix hk).1.2).trans (nZ u))
      (hfixg.trans (nZ (g • u)))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnD : K ≤ normalizer (D F β t : Set (G₀ L S)) :=
    (le_inf ((show K ≤ stabilizer F β from fun _ hk => (hfix hk).1.1.2).trans (nQ β))
      ((show K ≤ stabilizer F t from fun _ hk => (hfix hk).1.1.1.1).trans (nQ t))).trans
        inf_normalizer_le_normalizer_inf
  have hnR : K ≤ normalizer (R : Set (G₀ L S)) :=
    (le_inf hnD (hnW.trans (normalizer_le_normalizer_centralizer W))).trans
      inf_normalizer_le_normalizer_inf
  have hnJ : K ≤ normalizer (J : Set (G₀ L S)) :=
    (le_inf hnR ((show K ≤ stabilizer F y from fun _ hk => (hfix hk).2).trans (nQ y))).trans
      inf_normalizer_le_normalizer_inf
  let _ : Finite K := Finite.of_injective
    (inclusion (show K ≤ stabilizer F α from fun _ hk => (hfix hk).1.1.1.2))
    (inclusion_injective _)
  have hmove := c.D_residual_commutator_le_center H hS hb ht htne
  rw [hactor] at hmove
  have hRC : R ≤ centralizer ((K ⊓ graphLocalGroup F α : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply hdis.le_bot.trans'
    exact le_inf ((commutator_mono inf_le_left (odd_intersection_le_residual K _ ho)).trans hmove)
      (le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hnR))
  have hmove' := c'.D_residual_commutator_le_center H hS hb hy hyne
  rw [hactor'] at hmove'
  have hJC : J ≤ centralizer ((K ⊓ graphLocalGroup F u : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply (hdis'.mono inf_le_left le_rfl).le_bot.trans'
    apply le_inf (le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hnJ))
    exact (commutator_mono
      (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right)
      (odd_intersection_le_residual K _ ho)).trans hmove'
  have hJunion : J ≤ centralizer (((K ⊓ graphLocalGroup F α) ⊔
      (K ⊓ graphLocalGroup F u) : Subgroup (G₀ L S)) : Set (G₀ L S)) :=
    le_centralizer_iff.mpr (sup_le
      (le_centralizer_iff.mp (inf_le_left.trans hRC)) (le_centralizer_iff.mp hJC))
  let T := ((K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F u)) ⊓
    (K ⊓ graphLocalGroup F β)
  have hJT : J ≤ centralizer (T : Set (G₀ L S)) :=
    hJunion.trans (centralizer_le inf_le_left)
  have hTZ : Z F β ≤ centralizer (T : Set (G₀ L S)) :=
    (hcentral.trans inf_le_right).trans (centralizer_le (inf_le_right.trans inf_le_right))
  have hJX : ⁅J,V F β 1 ⊓ Q F α⁆ ≤ Z F β := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left (inf_le_left.trans (inf_le_left.trans inf_le_left))).trans
      (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2.le
  have hthree : ⁅V F β 1 ⊓ Q F α,T⁆ ≤ centralizer (J : Set (G₀ L S)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm T J,commutator_eq_bot_iff_le_centralizer.mpr hJT,
        commutator_bot_left]
    · exact commutator_eq_bot_iff_le_centralizer.mpr (hJX.trans hTZ)
  refine ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,?_,hr.symm,
    ?_,hdis,hdis',le_inf (le_inf hnW hnR) hnJ,hRC,hJunion,hthree,?_⟩
  · exact d.actor_generators.symm.trans (hdactor.trans hactor)
  · exact (d.decomposition H hS hb).trans (congrArg (Z F α ⊔ ·) hr)
  · have haKn : K.map (MulAut.conj a).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp haK
    have hLa : (graphLocalGroup F α).map (MulAut.conj a).toMonoidHom =
        graphLocalGroup F u := (graphLocalGroup_conjugate H a α).symm.trans (congrArg _ hau)
    rw [conjBy,map_inf _ _ _ (MulAut.conj a).injective,haKn,hLa]

/-- Transport the path-compatible Cartan, residual and three-subgroup calculation
through the original reduced-completion inclusion and full parabolic cores. -/
theorem original_bTwo_path_cartan_control
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    let ι := (G₀ L S).subtype
    let E := stabilizer F α ⊓ stabilizer F β
    ∃ K : Subgroup (G₀ L S),
      K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
        stabilizer F u ⊓ stabilizer F y ∧
      Disjoint K (E.pCoreIn 2) ∧ K ⊔ E.pCoreIn 2 = E ∧
      Odd (Nat.card K) ∧ IsMulCommutative K ∧
      K = (K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F β) ∧
      ∃ g ∈ graphLocalGroup F α, g ∈ normalizer (K : Set (G₀ L S)) ∧ g • β = t ∧
      ∃ a ∈ graphLocalGroup F β, a ∈ normalizer (K : Set (G₀ L S)) ∧ a • α = u ∧
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      let J₀ := R₀ ⊓ (Q F y).map ι
      let Kα := (K ⊓ graphLocalGroup F α).map ι
      let Kβ := (K ⊓ graphLocalGroup F β).map ι
      let Ku := (K ⊓ graphLocalGroup F u).map ι
      W₀ ⊔ (parabolic L S 0).pCoreIn 2 = enlargedEndpoint L S 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      D₀ = (Z F α).map ι ⊔ R₀ ∧ Disjoint ((Z F α).map ι) R₀ ∧
      Disjoint R₀ ((Z F u).map ι) ∧
      K.map ι ≤ normalizer (W₀ : Set G) ⊓ normalizer (R₀ : Set G) ⊓
        normalizer (J₀ : Set G) ∧
      R₀ ≤ centralizer (Kα : Set G) ∧
      J₀ ≤ centralizer ((Kα ⊔ Ku : Subgroup G) : Set G) ∧
      ⁅(V F β 1 ⊓ Q F α).map ι,(Kα ⊔ Ku) ⊓ Kβ⁆ ≤ centralizer (J₀ : Set G) ∧
      Kα.conjBy (a : G) = Ku := by
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    hW,hR,hD,hdis,hdis',hn,hRC,hJC,hthree,hconj⟩ :=
    original_bTwo_path_cartan_residual h hc hne hb hβu ht htne hy hyne
  let ι := (G₀ L S).subtype
  have hι : Function.Injective ι := (G₀ L S).subtype_injective
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
  let W := Z F u ⊔ Z F (g • u)
  let R := bTwoResidual F β t u (g • u)
  let J := R ⊓ Q F y
  let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
  let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
  let J₀ := R₀ ⊓ (Q F y).map ι
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hWm : W.map ι = W₀ := Subgroup.map_sup _ _ _
  have hRm : R.map ι = R₀ := by
    change (D F β t ⊓ centralizer (W : Set (G₀ L S))).map ι = _
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,hWm]
  have hJm : J.map ι = J₀ := by
    rw [show J = R ⊓ Q F y from rfl,map_inf _ _ _ (G₀ L S).subtype_injective,hRm]
  have mapC (A B : Subgroup (G₀ L S))
      (hab : A ≤ centralizer (B : Set (G₀ L S))) :
      A.map ι ≤ centralizer (B.map ι : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨z,hz,rfl⟩
    simpa only [map_mul] using congrArg ι (hab hx z hz)
  have mapN (A B : Subgroup (G₀ L S))
      (hab : A ≤ normalizer (B : Set (G₀ L S))) :
      A.map ι ≤ normalizer (B.map ι : Set G) :=
    (map_mono hab).trans (le_normalizer_map ι)
  refine ⟨K,hfix,hd,hgen,ho,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map ι) hW
    rw [Subgroup.map_sup,reduced_base_Q_map h false,reduced_graphLocalGroup_image h false] at hh
    simpa only [Subgroup.map_sup, family, Bool.false_eq_true, ↓reduceIte, enlargedEndpoint] using hh
  · have hh := congrArg (Subgroup.map ι) hR
    change R.map ι = _ at hh
    simpa only [hRm,Subgroup.map_inf _ _ _ hι,hDm] using hh
  · have hh := congrArg (Subgroup.map ι) hD
    change (D F β t).map ι = ((Z F α) ⊔ R).map ι at hh
    simpa only [hDm,Subgroup.map_sup,hRm] using hh
  · change Disjoint ((Z F α).map ι) R₀
    rw [←hRm]
    exact Subgroup.disjoint_map hι hdis
  · change Disjoint R₀ ((Z F u).map ι)
    rw [←hRm]
    exact Subgroup.disjoint_map hι hdis'
  · change K.map ι ≤ normalizer (W₀ : Set G) ⊓ normalizer (R₀ : Set G) ⊓
        normalizer (J₀ : Set G)
    exact le_inf (le_inf (hWm ▸ mapN K W (hn.trans (inf_le_left.trans inf_le_left)))
      (hRm ▸ mapN K R (hn.trans (inf_le_left.trans inf_le_right))))
      (hJm ▸ mapN K J (hn.trans inf_le_right))
  · change R₀ ≤ centralizer ((K ⊓ graphLocalGroup F α).map ι : Set G)
    rw [←hRm]
    exact mapC R _ hRC
  · have hh := mapC J _ hJC
    rw [hJm,Subgroup.map_sup] at hh
    exact hh
  · have hh := mapC _ J hthree
    change ⁅(V F β 1 ⊓ Q F α).map ι,
      ((K ⊓ graphLocalGroup F α).map ι ⊔ (K ⊓ graphLocalGroup F u).map ι) ⊓
        (K ⊓ graphLocalGroup F β).map ι⁆ ≤ centralizer (J₀ : Set G)
    simpa only [map_commutator,Subgroup.map_inf _ _ _ hι,
      Subgroup.map_sup,hJm] using hh
  · have hh := congrArg (Subgroup.map ι) hconj
    rw [conjBy,Subgroup.map_map] at hh
    change ((K ⊓ graphLocalGroup F α).map ι).map
      (MulAut.conj (a : G)).toMonoidHom = _
    rw [Subgroup.map_map]
    exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
