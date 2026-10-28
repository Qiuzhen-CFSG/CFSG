module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.OriginalBTwoEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCoreSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearModuleSource
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitarySolvability

/-!
# The original nonsolvable distance-two branch

The source critical-center actions, middle-vertex centrality, and exact
radius-one commutator supply all earlier premises of the Chapter 10 profile
calculations. A binary natural field would make the intrinsic actor and
then the original parabolic solvable. Thus both original nonsolvable
parabolics exclude the exceptional D = Z alternative, in either vertex
orbit and at every opposite neighbor. Strict containment survives the
literal reduced-completion inclusion.

At the original base edge the same construction gives the saturated alpha
core, the beta-core product, its exact Frattini and derived subgroups, the
positive field-power relation, and the elementary alpha-core quotient of
order q_beta squared. The actual full endpoint and Borel normalizers and
all original inclusion maps are retained. BTwoRegularConsumers applies
these results to the original Chapter 12 configuration.

The residual separation, regular path parameters and marked recognition
in (10.10) remain separate source obligations; strict D > Z alone does not
assert a Tits system or an amalgam comparison.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(7.1), (7.4), (10.6)--(10.10), pp.126--128,157--165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

private theorem base_adj : (graph F).Adj α β :=
  ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩

private theorem linear_two_solvable {k : Type*} [Field k] [Finite k]
    (hk : Nat.card k = 2) : Group.IsSolvable SL(2,k) := by
  let := Fintype.ofFinite k
  let e := ZMod.ringEquivOfPrime k Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) e.symm.toRingHom
  have hf : Function.Injective f := by
    intro a b hab
    ext i j
    exact e.symm.injective (congrArg (fun z : SL(2,ZMod 2) => z.val i j) hab)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsSolvable SL(2,ZMod 2) := Group.isSolvable_of_isSolvable_injective
    (f := SLTwoPermThree.sl2Two_equiv_perm_three.some.toMonoidHom)
    SLTwoPermThree.sl2Two_equiv_perm_three.some.injective
  exact Group.isSolvable_of_isSolvable_injective hf

/-- The genuine original nonsolvable endpoint forces its distance-two field to be nonbinary. -/
theorem field_gt_two_of_nonsolvable
    {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (h : HypothesisF11 L S) {u : Vertex F}
    (c : BTwoCenterActionData F α β u k W)
    (hactor : c.actor = graphLocalGroup F α)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) : 2 < Nat.card k := by
  by_contra hsmall
  have hk : Nat.card k = 2 := by have := (show 1 < Nat.card k from Finite.one_lt_card); omega
  let : Group.IsSolvable SL(2,k) := linear_two_solvable hk
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let : Finite (stabilizer F α) := by
    change Finite (MulAction.stabilizer (G₀ L S) α)
    rw [Subgroup.CosetGeometry.stabilizer_base]
    infer_instance
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  have hker : IsPGroup 2 c.quotient.ker := by
    rw [c.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer F α)).comap_subtype
  let : Group.IsNilpotent c.quotient.ker := hker.isNilpotent
  let : Group.IsSolvable c.actor := Group.isSolvable_of_ker_le_range
    c.quotient.ker.subtype c.quotient (by rw [range_subtype])
  let e := c.actor.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective
  let : Group.IsSolvable (c.actor.map (G₀ L S).subtype) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hL : L 0 ≤ c.actor.map (G₀ L S).subtype := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    exact (local_le_starredParabolic 0).trans le_sup_left
  let : Group.IsSolvable (L 0) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hL)
  exact hns ((h.parabolic_solvable_iff_local_quotient 0).mpr inferInstance)

/-- Nonsolvability of the two original parabolics persists in every intrinsic actor. -/
theorem graph_actor_not_solvable (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i)) (v : Vertex F) :
    ¬ Group.IsSolvable (graphLocalGroup F v) := by
  have hbase (i : Bool) : ¬ Group.IsSolvable (graphLocalGroup F (base F i)) := by
    intro hs
    let := hs
    let A := graphLocalGroup F (base F i)
    let e := A.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective
    let : Group.IsSolvable (A.map (G₀ L S).subtype) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have hL : L (if i then 1 else 0) ≤ A.map (G₀ L S).subtype := by
      rw [show A = graphLocalGroup F (base F i) from rfl,reduced_graphLocalGroup_image h i]
      cases i <;> exact (local_le_starredParabolic _).trans le_sup_left
    let : Group.IsSolvable (L (if i then 1 else 0)) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hL)
    exact hns (if i then 1 else 0) ((h.parabolic_solvable_iff_local_quotient (if i then 1 else 0)).mpr inferInstance)
  intro hs
  let := hs
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let A := graphLocalGroup F (base F v.type)
  have he : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let e : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr he)
  exact hbase v.type (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

private theorem field_gt_two_at
    {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v) : 2 < Nat.card k := by
  by_contra hsmall
  have hk : Nat.card k = 2 := by
    have := (show 1 < Nat.card k from Finite.one_lt_card)
    omega
  let : Group.IsSolvable SL(2,k) := linear_two_solvable hk
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  have hker : IsPGroup 2 c.quotient.ker := by
    rw [c.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer F v)).comap_subtype
  let : Group.IsNilpotent c.quotient.ker := hker.isNilpotent
  have hs : Group.IsSolvable c.actor := Group.isSolvable_of_ker_le_range
    c.quotient.ker.subtype c.quotient (by rw [range_subtype])
  exact graph_actor_not_solvable h hns v (hactor ▸ hs)

/-- At either original vertex orbit, every distance-two noncommuting path
lies in the strict D > Z branch; the full reduced-to-original images retain strictness. -/
theorem strict_core_intersections_of_critical_bTwo (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) :
    ∃ m : Vertex F, (graph F).Adj v m ∧ (graph F).Adj m w ∧
      Z F m ≤ centerIn (graphLocalGroup F m) ∧
      ∀ t : Vertex F, (graph F).Adj v t → t ≠ m →
        Z F v < D F m t ∧
        (Z F v).map (G₀ L S).subtype <
          (Q F m).map (G₀ L S).subtype ⊓ (Q F t).map (G₀ L S).subtype := by
  let H := reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints H
  have hdist : (graph F).dist v w = 2 := hc.1.trans hb
  obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero (by rw [hdist]; decide)
  have hlen : p.length = 2 := hp.trans hdist
  let m := p.getVert 1
  have hvm : (graph F).Adj v m := by
    simpa only [SimpleGraph.Walk.getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
  have hmw : (graph F).Adj m w := by
    have hh : (graph F).Adj (p.getVert 1) (p.getVert p.length) := by
      simpa only [hlen] using p.adj_getVert_succ (by omega : 1 < p.length)
    simpa only [SimpleGraph.Walk.getVert_length] using hh
  have hcentral := reduced_bTwo_middle_central h hc hne hb hvm hmw
  obtain ⟨k,f,fin,ch,a,c,hactor⟩ := Reduction.reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk := field_gt_two_at h hns c hactor
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hvm hmw).2.2.2
  have hnot := reduced_graph_core_obstruction h v m hvm
  refine ⟨m,hvm,hmw,hcentral,?_⟩
  intro t ht htne
  obtain ⟨n,hn,K,fK,finK,hK,⟨eK⟩⟩ := c.beta_quotient_linear H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht htne
    hcomm hnot (LinearEquiv.refl _ _) (reduced_actor_models_of_nonsolvable_parabolics h hns m)
  let := fK
  let := finK
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eβ := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hD : D F m t ≠ Z F v := by
    intro hD
    have htwo := c.exceptional_linear_alpha_field_binary H
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht htne
      hcomm.le hnot eβ hD (LinearEquiv.refl _ _)
    omega
  have hle : Z F v ≤ D F m t := le_inf
    (graph_Z_le_Q_of_short H (reduced_kernel_sylow h)
      (by change (graph F).dist v m < b F
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvm,hb]; decide))
    (graph_Z_le_Q_of_short H (reduced_kernel_sylow h)
      (by change (graph F).dist v t < b F
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr ht,hb]; decide))
  have hlt : Z F v < D F m t := lt_of_le_of_ne hle (Ne.symm hD)
  refine ⟨hlt,?_⟩
  rw [←map_inf _ _ _ (G₀ L S).subtype_injective]
  apply lt_of_le_of_ne (map_mono hle)
  intro he
  exact (ne_of_lt hlt) (map_injective (G₀ L S).subtype_injective he)

/-- All earlier geometric premises of the regular distance-two core layers are discharged.
The original full parabolic cores and the actual reduced-to-original inclusion are retained. -/
theorem original_core_layers
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F α β u k (Fin 2 → k),
      c.actor = graphLocalGroup F α ∧ 2 < Nat.card k ∧
      ∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
      (∃ r : ℕ, 0 < r ∧ 2^n = Nat.card k ^ r) ∧
      enlargedEndpoint L S 1 = starredParabolic L S 1 ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁ ⊓ (Q F t).map (G₀ L S).subtype
      let Z₀ := (Z F α).map (G₀ L S).subtype
      let Z₁ := (Z F β).map (G₀ L S).subtype
      D₀ ≠ Z₀ ∧
      (centralSeed F α β t).map (G₀ L S).subtype = Q₀ ∧
      Q₁ = (V F β 1).map (G₀ L S).subtype ⊔ D₀ ∧
      (frattini Q₁).map Q₁.subtype = Z₁ ∧ ⁅Q₁,Q₁⁆ = Z₁ ∧
      Nat.card k ≤ 2^n ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 := by
  obtain ⟨k,f,fin,ch,a,c,hactor,hext,n,hn,hm,hpow,hs,hnP,hnB,hN,hE,hcard⟩ :=
    Reduction.original_bTwo_central_core_field h hc hne hb hβu ht htne
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk := field_gt_two_of_nonsolvable h c hactor hns
  have hcentral := reduced_bTwo_middle_central h hc hne hb base_adj hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb base_adj hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β base_adj
  obtain ⟨K,fK,finK,hK,⟨e⟩⟩ := hm
  let := fK
  let := finK
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  have hcore := NoncommutingProfile.Reduction.original_bTwo_linear_core_layers h hb c hactor
    hcentral ht htne hcomm hnot e
  dsimp only at hcore
  have hbound : Nat.card k ≤ 2^n := hK ▸ hcore.2.2.2.1
  have hn2 : 1 < n := by
    by_contra hn2
    have he : n = 1 := by omega
    subst n
    norm_num at hbound
    omega
  have hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype ≠
      (Z F α).map (G₀ L S).subtype := by
    intro hD
    have htwo := (NoncommutingProfile.Reduction.original_bTwo_exceptional_fields_and_orders
      h hb c hactor hcentral ht htne hcomm hnot e hD (LinearEquiv.refl _ _)).1
    omega
  exact ⟨k,f,fin,ch,inferInstance,c,hactor,hk,n,hn2,⟨K,fK,finK,hK,⟨e⟩⟩,
    hpow,hext,hD,hs,hcore.1,hcore.2.1,hcore.2.2.1,hbound,hnP,hnB,hN,hE,hcard⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
