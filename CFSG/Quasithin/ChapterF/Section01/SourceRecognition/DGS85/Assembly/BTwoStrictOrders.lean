module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidualOrderPath
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearValence
public import Theory.SpecificGroups.SL2.FieldCardinality
public import Theory.SpecificGroups.SL2.OriginalSylowPair

/-!
# Marked orders in the strict distance-two branch

The terminal Cartan residual has the beta field order.  Its disjoint
factorization with the alpha center computes D, and the existing core
quotient computes Q.  Finally the edge two-core is a Sylow of the alpha
actor, whose quotient has the alpha field order.  All fields retain the
original quotient markings, so the resulting order can be compared with
the literal forward-path counts.

Source: DGS, Groups and Graphs (1985), (10.10)(b), pp.164--165.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

private theorem action_field_card
    (h : HypothesisF11 L S) {v : Vertex F}
    {k K : Type*} [Field k] [Finite k] [CharP k 2]
    [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) k]
    (c : BTwoCenterActionData F α β v k (Fin 2 → k))
    (hactor : c.actor = graphLocalGroup F α)
    (e : (graphLocalGroup F α ⧸ pCore 2 (graphLocalGroup F α)) ≃* SL(2,K)) :
    Nat.card k = Nat.card K := by
  have hcore : c.actor.pCoreIn 2 = Q F α := by
    rw [hactor]
    exact CommutingTrivial.graphLocalGroup_core (reduced_triple h) α
  have hker : c.quotient.ker = pCore 2 c.actor := by
    rw [c.kernel,←hcore]
    exact comap_map_eq_self_of_injective c.actor.subtype_injective _
  let eA := MulEquiv.subgroupCongr hactor
  let eQ := QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)
  let f := (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (eQ.trans e))
  exact Matrix.SL2.field_card_eq_of_equiv f

/-- The edge core modulo its incident vertex core has the marked field order. -/
theorem marked_edge_core_relIndex
    (h : HypothesisF11 L S) {v w : Vertex F} (hvw : (graph F).Adj v w)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,k)) :
    (Q F v).relIndex ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2) = Nat.card k := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let A := graphLocalGroup F v
  let : Finite A := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow H (reduced_vertex_sylow h) hvw
  have hTe := sylow_image_eq_edge_core (stabilizer F v)
    (stabilizer F v ⊓ stabilizer F w) inf_le_left
    (source_edge_core_sylow H (reduced_borel_core_sylow h) hvw) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le
    (H := A) (sylowGenerated_le _) (sylow_le_sylowGenerated _ T)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  rw [←hTe,←hR,←CommutingTrivial.graphLocalGroup_core H v]
  exact (relIndex_map_map_of_injective _ _ A.subtype_injective).trans
    (Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk R)

/-- The strict source edge core has exactly the order of the edge-rooted
seven-path set.  The fields are those of the two literal original markings. -/
theorem original_strict_edge_core_card
    (h : HypothesisF11 L S) {v t y : Vertex F}
    (hc : IsCriticalPair F α v) (hne : ⁅Z F α,Z F v⁆ ≠ ⊥)
    (hb : b F = 2) (hβv : (graph F).Adj β v)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj v y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i)) :
    Nat.card ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2) =
      Nat.card (K false)^3 * Nat.card (K true)^3 := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans (eSL i).symm
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,n,hn,hm,hpow,hext,hDne,hs,hQ,hPhi,hder,
    hbound,hnP,hnB,hN,hE,hquot⟩ := original_core_layers h hc hne hb hβv ht htne hns
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hka : Nat.card k = Nat.card (K false) := action_field_card h c hactor (eG false)
  have hnb : 2^n = Nat.card (K true) := by
    obtain ⟨B,fB,finB,hB,⟨eB⟩⟩ := hm
    let _ := fB
    let _ := finB
    let _ : Fintype B := Fintype.ofFinite B
    let _ : CharP B 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hB)
    let eB' := (reduced_graphLinearQuotient h true eB).trans
      (MulEquiv.ofBijective (BenderSuzuki.Converse.pi B)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact hB.symm.trans (Matrix.SL2.field_card_eq_of_equiv (eB'.symm.trans (eG true)))
  obtain ⟨C,hfix,hd,hgen,ho,hcomm,_,g,hg,hgC,hgt,_,_,_,_,
    hW,hR,hdec,hdis,hdisv,hCn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
    original_bTwo_path_cartan_residual_trivial h hc hne hb hβv ht htne hy hyne hns
  let R := bTwoResidual F β t v (g • v)
  have hytype : y.type = true := by
    have hvne := hβv.1
    have hyne' := hy.1
    change true ≠ v.type at hvne
    cases hv : v.type
    · cases hyt : y.type
      · exact False.elim (hyne' (hv.trans hyt.symm))
      · rfl
    · exact False.elim (hvne hv.symm)
  let ey := source_linear_quotient_at H K eG y
  have hcardR : Nat.card R = Nat.card (K true) := by
    have hnormal : C ≤ normalizer (R : Set (G₀ L S)) := fun x hx => (hCn hx).1.2
    have hdisj : Disjoint R (Q F y) := disjoint_iff.mpr (by simpa only [R] using hzero)
    have hh := path_cartan_residual_card h hy hfix hd hgen ho g hR hRne hdisj hnormal ey
    simpa only [hytype] using hh
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor (reduced_bTwo_middle_central h hc hne hb hab hβv)
  have hcardZ : Nat.card (Z F α) = Nat.card (K false)^2 := by
    rw [←hka]
    exact c.central_center_card (LinearEquiv.refl _ _) hω
  have hnZ : stabilizer F α ≤ normalizer (Z F α : Set (G₀ L S)) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F α)).mp (Z_normal F α)
  have hRa : R ≤ stabilizer F α :=
    ((show R ≤ D F β t from inf_le_left).trans inf_le_left).trans
      ((graph_Q_le_edgeCore H hab.symm).trans ((map_subtype_le _).trans inf_le_right))
  have hcardD : Nat.card (D F β t) = Nat.card (K false)^2 * Nat.card (K true) := by
    rw [hdec,card_sup_eq_mul_of_normalizes_of_disjoint _ _ (hRa.trans hnZ) hdis,
      hcardZ,hcardR]
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
  have hbasem (i : Bool) : (Q F (base F i)).map ι =
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 :=
    reduced_base_Q_map h i
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hbasem true]
    rfl
  have hDQ : D₀ ≤ Q₀ := by
    change (centralSeed F α β t).map ι = Q₀ at hs
    rw [←hs,←hDm]
    exact map_mono (show D F β t ≤ centralSeed F α β t from le_sup_right)
  have hcardD₀ : Nat.card D₀ = Nat.card (K false)^2 * Nat.card (K true) := by
    rw [←hDm,card_map_of_injective (G₀ L S).subtype_injective,hcardD]
  have hcardQ₀ : Nat.card Q₀ = Nat.card (K false)^2 * Nat.card (K true)^3 := by
    let _ := hN
    change Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 at hquot
    have hh := card_eq_card_quotient_mul_card_subgroup (D₀.subgroupOf Q₀)
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv,hcardD₀,hquot,hnb] at hh
    exact hh.trans (by ring)
  have hcardQ : Nat.card (Q F α) = Nat.card (K false)^2 * Nat.card (K true)^3 := by
    rw [←card_map_of_injective (f := ι) (G₀ L S).subtype_injective,
      hbasem false]
    exact hcardQ₀
  have hi := marked_edge_core_relIndex h hab (eG false)
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F α)
    ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2) bot_le (graph_Q_le_edgeCore H hab)
  rw [relIndex_bot_left,relIndex_bot_left,hi,hcardQ] at hh
  exact hh.symm.trans (by ring)

private theorem edge_core_card_eq_base {a d : Vertex F} (had : (graph F).Adj a d) :
    Nat.card ((stabilizer F a ⊓ stabilizer F d).pCoreIn 2) =
      Nat.card ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2) := by
  obtain ⟨g,ha,hd⟩ := incident_common_translate F had.2
  have he : (stabilizer F a ⊓ stabilizer F d).pCoreIn 2 =
      ((stabilizer F (base F a.type) ⊓ stabilizer F (base F d.type)).pCoreIn 2).map
        (MulAut.conj g).toMonoidHom := by
    rw [←ha,←hd,stabilizer_translate,stabilizer_translate,
      ←map_inf _ _ _ (MulAut.conj g).injective,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    rfl
  rw [he,card_map_of_injective (MulAut.conj g).injective]
  have hne := had.1
  cases hat : a.type <;> cases hdt : d.type
  · exact False.elim (hne (hat.trans hdt.symm))
  · rfl
  · rw [inf_comm]
  · exact False.elim (hne (hat.trans hdt.symm))

/-- The marked strict edge-core order holds at every edge, in either orientation.
This supplies the cardinal premise for the literal seven-path orbit count. -/
theorem original_strict_edge_core_card_at
    (h : HypothesisF11 L S) {v t y : Vertex F}
    (hc : IsCriticalPair F α v) (hne : ⁅Z F α,Z F v⁆ ≠ ⊥)
    (hb : b F = 2) (hβv : (graph F).Adj β v)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj v y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i))
    {a d : Vertex F} (had : (graph F).Adj a d) :
    Nat.card ((stabilizer F a ⊓ stabilizer F d).pCoreIn 2) =
      Nat.card (K false)^3 * Nat.card (K true)^3 :=
  (edge_core_card_eq_base had).trans
    (original_strict_edge_core_card h hc hne hb hβv ht htne hy hyne hns K e)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
