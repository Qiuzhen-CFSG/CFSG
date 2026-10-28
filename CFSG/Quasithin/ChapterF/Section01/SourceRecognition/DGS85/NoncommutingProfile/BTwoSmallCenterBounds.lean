module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualPairing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalVerticesSource
public import Theory.GroupTheory.BinaryPairingCard
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Binary-alpha residual and core bounds

The residual's faithful commutator pairing with the adjacent-core
intersection takes values in the beta center. When the alpha field is
binary, that center has order two. Binary duality and centralization of
D_alpha bound the residual by the index of D_alpha in the intersection,
which is exactly q_beta. This extends the binary evaluation argument
without assuming that the beta field is binary or that a terminal-core
intersection vanishes.

The source application compares the original alpha quotient marking with
the constructed natural action, obtaining its binary field size internally.
It retains one opposite-center lift and the literal residual/core maps.
The exact orders over D_alpha then give both core bounds and the full
original Borel two-core bound. The mixed S3/A5 application includes the
exceptional and strict cases without assuming either case or a core bound.
It does not establish the strict equality or its path and quaternion clauses.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7)--(10.10), printed pp.158--165, especially the binary commutator
calculation on p.161 and the strict order formulas on p.164.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction

private theorem card_le_index_of_faithful_binary_commutators
    {H : Type*} [Group H] (A U D C : Subgroup H) [Finite A] [Finite U] [Finite C]
    [IsMulCommutative C]
    (hDA : A ≤ centralizer (D : Set H))
    (hCA : A ≤ centralizer (C : Set H)) (hCU : U ≤ centralizer (C : Set H))
    (hcard : Nat.card C = 2) (hcomm : ⁅A,U⁆ ≤ C)
    (hfaith : A ⊓ centralizer (U : Set H) = ⊥) : Nat.card A ≤ D.relIndex U := by
  have hvalue (a : A) (u : U) : ⁅(a:H),(u:H)⁆ ∈ C :=
    hcomm (commutator_mem_commutator a.property u.property)
  let f : A →* (U →* C) := {
    toFun := fun a => {
      toFun := fun u => ⟨⁅(a:H),(u:H)⁆,hvalue a u⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro u v
        apply Subtype.ext
        change ⁅(a:H),(u:H)*(v:H)⁆ = ⁅(a:H),(u:H)⁆*⁅(a:H),(v:H)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hc := mem_centralizer_iff.mp (hCU u.property) _ (hvalue a v)
        calc
          _ = ⁅(a:H),(u:H)⁆*((u:H)*⁅(a:H),(v:H)⁆)*(u:H)⁻¹ := by group
          _ = _ := by rw [←hc]; group }
    map_one' := by ext u; simp
    map_mul' := by
      intro a b
      ext u
      change ⁅(a:H)*(b:H),(u:H)⁆ = ⁅(a:H),(u:H)⁆*⁅(b:H),(u:H)⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hc := mem_centralizer_iff.mp (hCA a.property) _ (hvalue b u)
      rw [←hc,mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨_,hvalue b u⟩ : C) ⟨_,hvalue a u⟩) }
  have hk : f.ker = ⊥ := by
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfaith]
    refine ⟨a.property,?_⟩
    intro u hu
    have hh := congrArg (fun l : U →* C => (l ⟨u,hu⟩ : H)) ha
    exact (commutatorElement_eq_one_iff_commute.mp hh).symm.eq
  have hDker : D.subgroupOf U ≤ f.flip.ker := by
    intro u hu
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_commute.mpr
      ((mem_centralizer_iff.mp (hDA a.property) u hu).symm)
  have hc := MonoidHom.binary_pairing_kernel_card hcard f
  rw [hk,card_bot,mul_one] at hc
  have hd := card_le_of_le hDker
  have hi := (D.subgroupOf U).index_mul_card
  have hpos : 0 < Nat.card (D.subgroupOf U) := Nat.card_pos
  change D.relIndex U * Nat.card (D.subgroupOf U) = Nat.card U at hi
  have hh := (Nat.mul_le_mul_left (Nat.card A) hd).trans_eq (hc.trans hi.symm)
  nlinarith


universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- Binary commutator duality bounds the residual by the actual beta field order.
The chosen lift and all original core maps are retained. -/
theorem original_bTwo_small_center_residual_bound
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    {k : Type u} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (hactor : c.actor = graphLocalGroup F α)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hk : Nat.card k = 2)
    (g : c.actor) (hg : (g : G₀ L S) • β = t)
    (hgen : ((Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι) ⊔
      (parabolic L S 0).pCoreIn 2 = enlargedEndpoint L S 0)
    (hDel : IsElementaryAbelian 2
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G)) :
    Nat.card (((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) ⊓
      centralizer (((Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι : Subgroup G) : Set G) :
        Subgroup G) ≤ Nat.card K := by
  have halg : ‹Algebra (ZMod 2) k› = ZMod.algebra k 2 := Subsingleton.elim _ _
  cases halg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁ ⊓ (Q F t).map ι
  let Z₁ := (Z F β).map ι
  let I := Q₀ ⊓ Q₁
  let W₀ := (Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι
  let R := D₀ ⊓ centralizer (W₀ : Set G)
  have hQam : (Q F α).map ι = Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι = Q₁ := reduced_base_Q_map h true
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  have hIm : (Q F α ⊓ Q F β).map ι = I := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQam,hQbm]
  have hi : D₀.relIndex I = Nat.card K := by
    rw [←hDm,←hIm,relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact (c.linear_seed_factor_index H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) (reduced_kernel_sylow h) hb ht htne hnot eβ)
  have hder : ⁅Q₁,Q₁⁆ = Z₁ := by
    have hh := congrArg (map ι) (c.beta_core_frattini_eq H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm).2
    change (⁅Q F β,Q F β⁆).map ι = Z₁ at hh
    rwa [map_commutator,hQbm] at hh
  have hZcard : Nat.card Z₁ = 2 := by
    rw [show Z₁ = (Z F β).map ι from rfl,card_map_of_injective (G₀ L S).subtype_injective]
    exact (c.central_middle_center_card H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _)).trans hk
  have hQC : Q₁ ≤ centralizer (Z₁ : Set G) := by
    have hqc : Q F β ≤ centralizer (Z F β : Set (G₀ L S)) := graph_Q_centralizes_Z H β
    have hh := (map_mono (f := ι) hqc).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [hQbm] at hh
    exact hh
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite I := Finite.of_injective
    (inclusion (show I ≤ Q₁ from inf_le_right)) (inclusion_injective _)
  let : Finite R := Finite.of_injective
    (inclusion (show R ≤ Q₁ from inf_le_left.trans inf_le_left)) (inclusion_injective _)
  let : Finite Z₁ := Finite.of_injective (inclusion (show Z₁ ≤ Q₁ from by
    rw [←hder]; exact (Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl))) (inclusion_injective _)
  let := hDel
  have hRD : R ≤ centralizer (D₀ : Set G) := inf_le_left.trans (le_centralizer D₀)
  have hRI : ⁅R,I⁆ ≤ Z₁ := hder ▸ commutator_mono
    (show R ≤ Q₁ from inf_le_left.trans inf_le_left) (show I ≤ Q₁ from inf_le_right)
  have hfaith := Assembly.BTwoSource.original_bTwo_residual_endpoint_centralizer
    h hc hne hb hβu ht htne c hactor eβ g hg hgen hDel
  let : IsMulCommutative Z₁ := le_centralizer_iff_isMulCommutative.mp
    ((show Z₁ ≤ Q₁ from by rw [←hder]; exact (Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl)).trans hQC)
  exact (card_le_index_of_faithful_binary_commutators R I D₀ Z₁ hRD
    ((inf_le_left.trans inf_le_left).trans hQC) (inf_le_right.trans hQC)
    hZcard hRI hfaith).trans_eq hi


variable {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]

private theorem center_field_card_of_original_marking
    (h : HypothesisF11 L S) {u : Vertex F}
    {k : Type u} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (hactor : c.actor = graphLocalGroup F α)
    (e₀ : (L 0 ⧸ pCore 2 (L 0)) ≃* PSL(2,K₀)) : Nat.card k = Nat.card K₀ := by
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hc : pCore 2 c.actor = (Q F α).subgroupOf c.actor := by
    apply map_injective c.actor.subtype_injective
    rw [map_subgroupOf_eq_of_le c.core_le]
    change c.actor.pCoreIn 2 = _
    rw [hactor]
    exact sylowGenerated_core (stabilizer F α)
  let ec : (c.actor ⧸ pCore 2 c.actor) ≃* SL(2,k) :=
    (QuotientGroup.quotientMulEquivOfEq (hc.trans c.kernel.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto)
  let ea : (c.actor ⧸ pCore 2 c.actor) ≃* SL(2,K₀) := by
    rw [hactor]
    exact (reduced_graphLinearQuotient h false e₀).trans
      (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K₀)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  exact Matrix.SL2.field_card_eq_of_equiv (ec.symm.trans ea)

/-- With binary alpha field, the original strict residual has order at most
q_beta. Consequently both endpoint cores and the full Borel two-core have
the source upper bounds, without terminal-core separation. -/
theorem original_bTwo_alpha_binary_strict_bounds
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (e₀ : (L 0 ⧸ pCore 2 (L 0)) ≃* PSL(2,K₀)) (hK₀ : Nat.card K₀ = 2)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι) :
    ∃ g ∈ graphLocalGroup F α, g • β = t ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁ ⊓ (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      1 < Nat.card R₀ ∧ Nat.card R₀ ≤ Nat.card K ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      Nat.card D₀ = 4 * Nat.card R₀ ∧
      Nat.card Q₀ = 4 * Nat.card K ^ 2 * Nat.card R₀ ∧
      Nat.card Q₁ = 8 * Nat.card K * Nat.card R₀ ∧
      (commonBorel L S).pCoreIn 2 = Q₀ ⊔ Q₁ ∧
      Nat.card ((commonBorel L S).pCoreIn 2) = 8 * Nat.card K ^ 2 * Nat.card R₀ ∧
      Nat.card D₀ ≤ 4 * Nat.card K ∧
      Nat.card Q₀ ≤ 4 * Nat.card K ^ 3 ∧
      Nat.card Q₁ ≤ 8 * Nat.card K ^ 2 ∧
      Nat.card ((commonBorel L S).pCoreIn 2) ≤ 8 * Nat.card K ^ 3 := by
  obtain ⟨k,f,fin,ch,alg,c,hactor,hkmin,n,hn,hm,hpow,g,hg,
    hgen,hfour,hwhole,hRne,hDel,hRel,hdec,hdis,hprod,hZ,hDcard,hQcard,hnP,hnB⟩ :=
    original_bTwo_strict_residual h hc hne hb hβu ht htne hD
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  change c.actor = graphLocalGroup F α at hactor
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk : Nat.card k = 2 := (center_field_card_of_original_marking h c hactor e₀).trans hK₀
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁ ⊓ (Q F t).map ι
  let W₀ := (Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι
  let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
  have hRle : Nat.card R₀ ≤ Nat.card K := original_bTwo_small_center_residual_bound
    h hc hne hb hβu ht htne c hactor e hk g hg hgen hDel
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite R₀ := Finite.of_injective
    (inclusion (show R₀ ≤ Q₁ from inf_le_left.trans inf_le_left)) (inclusion_injective _)
  have hRpos : 1 < Nat.card R₀ := R₀.one_lt_card_iff_ne_bot.mpr hRne
  have hDc : Nat.card D₀ = 4 * Nat.card R₀ := by
    change Nat.card D₀ = Nat.card k ^ 2 * Nat.card R₀ at hDcard
    simpa [hk] using hDcard
  have hQam : (Q F α).map ι = Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι = Q₁ := reduced_base_Q_map h true
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  obtain ⟨hQa,hQb⟩ := c.linear_core_orders_over_D H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ
  change Nat.card (Q F α) = Nat.card K ^ 2 * Nat.card (D F β t) at hQa
  change Nat.card (Q F β) = Nat.card k * Nat.card K * Nat.card (D F β t) at hQb
  have hDr : Nat.card (D F β t) = 4 * Nat.card R₀ := by
    rw [←card_map_of_injective (f := ι) (G₀ L S).subtype_injective,hDm]
    exact hDc
  have hQac : Nat.card Q₀ = 4 * Nat.card K ^ 2 * Nat.card R₀ := by
    rw [←hQam,card_map_of_injective (G₀ L S).subtype_injective,hQa,hDr]
    ring
  have hQbc : Nat.card Q₁ = 8 * Nat.card K * Nat.card R₀ := by
    rw [←hQbm,card_map_of_injective (G₀ L S).subtype_injective,hQb,hk,hDr]
    ring
  have hSc : Nat.card ((commonBorel L S).pCoreIn 2) = 8 * Nat.card K ^ 2 * Nat.card R₀ := by
    let : Finite (Q F β) := Finite.of_injective
      (inclusion (Q_le_stabilizer F β)) (inclusion_injective _)
    have hi : (Q F β).relIndex (Q F β ⊔ Q F α) = Nat.card K := by
      have hnQ : Q F β ≤ normalizer (Q F α : Set (G₀ L S)) :=
        c.neighbor_core_le.trans (c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F α))
      rw [sup_comm,relIndex_sup_of_normalizes _ _ hnQ]
      exact (c.linear_seed_eq_core_and_index H (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) (reduced_kernel_sylow h) hb ht htne hnot eβ).2
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F β)
      (Q F β ⊔ Q F α) bot_le le_sup_left
    rw [relIndex_bot_left,relIndex_bot_left,hi,hQb,hk,hDr] at hh
    rw [original_bTwo_borel_core_eq_product h c]
    change Nat.card (Q₀ ⊔ Q₁ : Subgroup G) = _
    rw [←hQam,←hQbm,←Subgroup.map_sup,card_map_of_injective (G₀ L S).subtype_injective,sup_comm,←hh]
    ring
  refine ⟨g,hactor ▸ g.property,hg,hRpos,hRle,hfour,hwhole,hDc,hQac,hQbc,
    original_bTwo_borel_core_eq_product h c,hSc,?_,?_,?_,?_⟩
  · rw [hDc]; exact Nat.mul_le_mul_left _ hRle
  · rw [hQac]
    convert Nat.mul_le_mul_left (4 * Nat.card K ^ 2) hRle using 1; ring
  · rw [hQbc]
    convert Nat.mul_le_mul_left (8 * Nat.card K) hRle using 1; ring
  · rw [hSc]
    convert Nat.mul_le_mul_left (8 * Nat.card K ^ 2) hRle using 1; ring

private theorem original_borel_core_card
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hb : b F = 2) (ht : (graph F).Adj α t) (htne : t ≠ β)
    {k : Type u} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    Nat.card ((commonBorel L S).pCoreIn 2) =
      Nat.card K * Nat.card ((parabolic L S 1).pCoreIn 2) := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let : Finite (Q F β) := Finite.of_injective
    (inclusion (Q_le_stabilizer F β)) (inclusion_injective _)
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hnot := reduced_graph_core_obstruction h α β c.middle
  have hi : (Q F β).relIndex (Q F β ⊔ Q F α) = Nat.card K := by
    have hnQ : Q F β ≤ normalizer (Q F α : Set (G₀ L S)) :=
      c.neighbor_core_le.trans (c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F α))
    rw [sup_comm,relIndex_sup_of_normalizes _ _ hnQ]
    exact (c.linear_seed_eq_core_and_index H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) (reduced_kernel_sylow h) hb ht htne hnot eβ).2
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F β)
    (Q F β ⊔ Q F α) bot_le le_sup_left
  rw [relIndex_bot_left,relIndex_bot_left,hi] at hh
  have hQa : (Q F α).map ι = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQb : (Q F β).map ι = (parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  rw [original_bTwo_borel_core_eq_product h c,←hQa,←hQb,←Subgroup.map_sup,
    card_map_of_injective (G₀ L S).subtype_injective,
    card_map_of_injective (G₀ L S).subtype_injective,sup_comm,←hh,mul_comm]

/-- The binary-alpha source upper bounds hold in both the exceptional and
strict branches. The only model inputs are the actual original local
quotient isomorphisms; all center actions and residual data are constructed. -/
theorem original_bTwo_alpha_binary_core_bounds
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (e₀ : (L 0 ⧸ pCore 2 (L 0)) ≃* PSL(2,K₀)) (hK₀ : Nat.card K₀ = 2)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    Nat.card ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G) ≤ 4 * Nat.card K ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) ≤ 4 * Nat.card K ^ 3 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) ≤ 8 * Nat.card K ^ 2 ∧
      Nat.card ((commonBorel L S).pCoreIn 2) ≤ 8 * Nat.card K ^ 3 := by
  classical
  by_cases hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι = (Z F α).map ι
  · obtain ⟨k,f,fin,ch,alg,c,hactor,hZD,hDQ,hDel,hZ,hQa,hQb,hlower,hiff,hstrict,
      hPhi,hder,hbound,hnP,hnB⟩ :=
      original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne e
    have hk : Nat.card k = 2 := (center_field_card_of_original_marking h c hactor e₀).trans hK₀
    have hDc : Nat.card ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G) = 4 := by
      rw [hD,hZ,hk]
      norm_num
    have hBc := original_borel_core_card h hb ht htne c e
    have hq : 1 ≤ Nat.card K := Nat.card_pos
    have hq2 : Nat.card K ≤ Nat.card K ^ 2 := by nlinarith
    have hq3 : Nat.card K ^ 2 ≤ Nat.card K ^ 3 := by
      calc
        Nat.card K ^ 2 = Nat.card K ^ 2 * 1 := (Nat.mul_one _).symm
        _ ≤ Nat.card K ^ 2 * Nat.card K := Nat.mul_le_mul_left _ hq
        _ = Nat.card K ^ 3 := (pow_succ (Nat.card K) 2).symm
    refine ⟨?_,?_,?_,?_⟩
    · rw [hDc]; omega
    · rw [hQa,hDc]
      nlinarith
    · rw [hQb,hk,hDc]
      nlinarith
    · rw [hBc,hQb,hk,hDc]
      nlinarith
  · obtain ⟨g,hg,hgt,hRpos,hRle,hfour,hwhole,hDc,hQa,hQb,hB,hBc,hbounds⟩ :=
      original_bTwo_alpha_binary_strict_bounds h hc hne hb hβu ht htne e₀ hK₀ e hD
    exact hbounds

/-- The mixed S₃/A₅ original quotient row has endpoint-core bounds 256 and
128 and full Borel two-core bound 512. This includes both D=Z and D≠Z. -/
theorem original_bTwo_mixed_core_bounds
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (e₀ : (L 0 ⧸ pCore 2 (L 0)) ≃* PSL(2,K₀)) (hK₀ : Nat.card K₀ = 2)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 4) :
    Nat.card ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G) ≤ 16 ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) ≤ 256 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) ≤ 128 ∧
      Nat.card ((commonBorel L S).pCoreIn 2) ≤ 512 := by
  simpa only [hK,show 4*4=16 by decide,show 4*4^3=256 by decide,
    show 8*4^2=128 by decide,show 8*4^3=512 by decide] using
    original_bTwo_alpha_binary_core_bounds h hc hne hb hβu ht htne e₀ hK₀ e

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
