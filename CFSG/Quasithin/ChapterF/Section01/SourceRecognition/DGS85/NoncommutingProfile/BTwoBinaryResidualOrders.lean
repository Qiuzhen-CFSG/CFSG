module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualPairing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalVerticesSource

/-!
# The strict binary residual and original core orders

For the binary beta quotient the adjacent-core intersection has index two
above D_alpha. The residual centralizes D_alpha and its commutators with
the intersection lie in Z_beta, which has order two. The established
faithful endpoint pairing makes evaluation on a single nontrivial coset
injective, so the residual has order at most two. In the strict source
case D_alpha ≠ Z_alpha, it is nontrivial and therefore has order two.

The same opposite-center lift then gives |D_alpha| = 8, both original
core orders 32, and full original Borel two-core order 64. The direct
product, four-core intersection, whole-core centralizer and beta Frattini
and derived subgroup retain their original inclusion maps. No nonsolvability
is imposed, and no terminal-core separation or strict path bound is assumed.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
the binary calculation in (10.8), printed p.161, and (10.10)(b), p.164.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction

private theorem card_le_of_faithful_index_two_commutators
    {H : Type*} [Group H] (A U D C : Subgroup H) [Finite A] [Finite C]
    (hDA : A ≤ centralizer (D : Set H)) (hCA : A ≤ centralizer (C : Set H))
    (hindex : (D.subgroupOf U).index = 2) (hcomm : ⁅A,U⁆ ≤ C)
    (hfaith : A ⊓ centralizer (U : Set H) = ⊥) : Nat.card A ≤ Nat.card C := by
  classical
  have hnot : ¬ U ≤ D := by
    intro hle
    have heq : D.subgroupOf U = ⊤ := subgroupOf_eq_top.mpr hle
    rw [heq,index_top] at hindex
    contradiction
  obtain ⟨u,hu,huD⟩ := SetLike.not_le_iff_exists.mp hnot
  have hvalue (a : A) : ⁅u,(a:H)⁆ ∈ C := by
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator hu a.property
  let displacement : A →* C := {
    toFun := fun a => ⟨⁅u,(a:H)⁆,hvalue a⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅u,(a:H)*(b:H)⁆ = ⁅u,(a:H)⁆*⁅u,(b:H)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := mem_centralizer_iff.mp (hCA a.property) _ (hvalue b)
      calc
        _ = ⁅u,(a:H)⁆*((a:H)*⁅u,(b:H)⁆)*(a:H)⁻¹ := by group
        _ = _ := by rw [←hc]; group }
  apply Nat.card_le_card_of_injective displacement
  apply (MonoidHom.ker_eq_bot_iff displacement).mp
  apply bot_unique
  intro a ha
  have hua : Commute u (a:H) := commutatorElement_eq_one_iff_commute.mp
    (congrArg Subtype.val (MonoidHom.mem_ker.mp ha))
  have hcentral : (a:H) ∈ centralizer (U : Set H) := by
    rw [mem_centralizer_iff]
    intro w hw
    by_cases hwD : w ∈ D
    · exact mem_centralizer_iff.mp (hDA a.property) w hwD
    have hprod : u⁻¹*w ∈ D := by
      have hh : (⟨u,hu⟩:U)⁻¹*⟨w,hw⟩ ∈ D.subgroupOf U := by
        rw [mul_mem_iff_of_index_two hindex]
        change u⁻¹∈D ↔ w∈D
        simp [huD,hwD]
      exact hh
    have hz : Commute (u⁻¹*w) (a:H) :=
      mem_centralizer_iff.mp (hDA a.property) _ hprod
    simpa only [mul_inv_cancel_left] using (hua.mul_left hz).eq
  exact Subtype.ext (mem_bot.mp (hfaith ▸ (show (a:H) ∈ A ⊓ centralizer (U : Set H) from
    ⟨a.property,hcentral⟩)))

universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- Faithful commutator evaluation bounds the actual binary residual by two.
The chosen lift and all original core maps are retained. -/
theorem original_bTwo_binary_residual_card_le_two
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    {k : Type u} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (hactor : c.actor = graphLocalGroup F α)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 2)
    (g : c.actor) (hg : (g : G₀ L S) • β = t)
    (hgen : ((Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι) ⊔
      (parabolic L S 0).pCoreIn 2 = enlargedEndpoint L S 0)
    (hDel : IsElementaryAbelian 2
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G)) :
    Nat.card (((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) ⊓
      centralizer (((Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι : Subgroup G) : Set G) :
        Subgroup G) ≤ 2 := by
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
  have hk : Nat.card k = 2 := by
    have hh := (c.linear_central_core_structure H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ).1
    rw [hK] at hh
    have : 1 < Nat.card k := Finite.one_lt_card
    omega
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
  have hi : (D₀.subgroupOf I).index = 2 := by
    change D₀.relIndex I = 2
    rw [←hDm,←hIm,relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact (c.linear_seed_factor_index H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) (reduced_kernel_sylow h) hb ht htne hnot eβ).trans hK
  have hder : ⁅Q₁,Q₁⁆ = Z₁ := by
    have hh := congrArg (map ι) (c.beta_core_frattini_eq H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm).2
    change (⁅Q F β,Q F β⁆).map ι = Z₁ at hh
    rwa [map_commutator,hQbm] at hh
  have hZcard : Nat.card Z₁ = 2 := by
    rw [show Z₁ = (Z F β).map ι from rfl,card_map_of_injective (G₀ L S).subtype_injective]
    exact (c.central_middle_center_card H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _)).trans hk
  have hRC : R ≤ centralizer (Z₁ : Set G) := by
    have hqc : Q F β ≤ centralizer (Z F β : Set (G₀ L S)) := graph_Q_centralizes_Z H β
    have hh := (map_mono (f := ι) hqc).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [hQbm] at hh
    exact (inf_le_left.trans inf_le_left).trans hh
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
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
  exact (card_le_of_faithful_index_two_commutators R I D₀ Z₁ hRD hRC hi hRI hfaith).trans_eq hZcard


/-- The strict binary row has residual order two, D order eight, both core
orders thirty-two and full Borel two-core order sixty-four. All natural
coordinates and the residual marking are constructed from the original source. -/
theorem original_bTwo_binary_strict_orders
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 2)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι) :
    ∃ g ∈ graphLocalGroup F α, g • β = t ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁ ⊓ (Q F t).map ι
      let Z₀ := (Z F α).map ι
      let Z₁ := (Z F β).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      Nat.card R₀ = 2 ∧ IsElementaryAbelian 2 D₀ ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
      (∃ f : Z₀ × R₀ ≃* D₀, ∀ z r, (f (z,r) : G) = (z : G) * (r : G)) ∧
      Nat.card Z₀ = 4 ∧ Nat.card Z₁ = 2 ∧ Nat.card D₀ = 8 ∧
      Nat.card Q₀ = 32 ∧ Nat.card Q₁ = 32 ∧
      (commonBorel L S).pCoreIn 2 = Q₀ ⊔ Q₁ ∧
      Nat.card ((commonBorel L S).pCoreIn 2) = 64 ∧
      (frattini Q₁).map Q₁.subtype = Z₁ ∧ ⁅Q₁,Q₁⁆ = Z₁ := by
  obtain ⟨k,f,fin,ch,alg,c,hactor,hkmin,n,hn,hm,hpow,g,hg,
    hgen,hfour,hwhole,hRne,hDel,hRel,hdec,hdis,hprod,hZ,hDcard,hQcard,hnP,hnB⟩ :=
    original_bTwo_strict_residual h hc hne hb hβu ht htne hD
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  change c.actor = graphLocalGroup F α at hactor
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
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
  have hk : Nat.card k = 2 := by
    have hh := (c.linear_central_core_structure H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ).1
    rw [hK] at hh
    omega
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁ ⊓ (Q F t).map ι
  let Z₀ := (Z F α).map ι
  let Z₁ := (Z F β).map ι
  let W₀ := (Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι
  let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
  have hRle : Nat.card R₀ ≤ 2 := original_bTwo_binary_residual_card_le_two
    h hc hne hb hβu ht htne c hactor e hK g hg hgen hDel
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite R₀ := Finite.of_injective
    (inclusion (show R₀ ≤ Q₁ from inf_le_left.trans inf_le_left)) (inclusion_injective _)
  have hRcard : Nat.card R₀ = 2 := by
    have hh := R₀.one_lt_card_iff_ne_bot.mpr hRne
    omega
  have hDc : Nat.card D₀ = 8 := by
    change Nat.card D₀ = Nat.card k ^ 2 * Nat.card R₀ at hDcard
    simpa [hk,hRcard] using hDcard
  have hQam : (Q F α).map ι = Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι = Q₁ := reduced_base_Q_map h true
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  obtain ⟨hQa,hQb⟩ := c.linear_core_orders_over_D H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ
  change Nat.card (Q F α) = Nat.card K ^ 2 * Nat.card (D F β t) at hQa
  change Nat.card (Q F β) = Nat.card k * Nat.card K * Nat.card (D F β t) at hQb
  have hDr : Nat.card (D F β t) = 8 := by
    rw [←card_map_of_injective (f := ι) (G₀ L S).subtype_injective,hDm]
    exact hDc
  have hQac : Nat.card Q₀ = 32 := by
    rw [←hQam,card_map_of_injective (G₀ L S).subtype_injective,hQa,hK,hDr]
    norm_num
  have hQbc : Nat.card Q₁ = 32 := by
    rw [←hQbm,card_map_of_injective (G₀ L S).subtype_injective,hQb,hk,hK,hDr]
  have hZc : Nat.card Z₀ = 4 := by
    change Nat.card Z₀ = Nat.card k ^ 2 at hZ
    rw [hk] at hZ
    norm_num at hZ
    exact hZ
  have hZbc : Nat.card Z₁ = 2 := by
    rw [show Z₁ = (Z F β).map ι from rfl,card_map_of_injective (G₀ L S).subtype_injective]
    exact (c.central_middle_center_card H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _)).trans hk
  have hSc : Nat.card ((commonBorel L S).pCoreIn 2) = 64 := by
    let : Finite (Q F β) := Finite.of_injective
      (inclusion (Q_le_stabilizer F β)) (inclusion_injective _)
    have hi : (Q F β).relIndex (Q F β ⊔ Q F α) = 2 := by
      have hnQ : Q F β ≤ normalizer (Q F α : Set (G₀ L S)) :=
        c.neighbor_core_le.trans (c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F α))
      rw [sup_comm,relIndex_sup_of_normalizes _ _ hnQ]
      exact (c.linear_seed_eq_core_and_index H (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) (reduced_kernel_sylow h) hb ht htne hnot eβ).2.trans hK
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F β)
      (Q F β ⊔ Q F α) bot_le le_sup_left
    rw [relIndex_bot_left,relIndex_bot_left,hi,hQb,hk,hK,hDr] at hh
    rw [original_bTwo_borel_core_eq_product h c]
    change Nat.card (Q₀ ⊔ Q₁ : Subgroup G) = 64
    rw [←hQam,←hQbm,←Subgroup.map_sup,card_map_of_injective (G₀ L S).subtype_injective,sup_comm]
    exact hh.symm
  have hlayers := original_bTwo_linear_core_layers h hb c hactor hcentral
    ht htne hcomm hnot e
  exact ⟨g,hactor ▸ g.property,hg,hfour,hwhole,hRcard,hDel,hdec,hdis,hprod,
    hZc,hZbc,hDc,hQac,hQbc,original_bTwo_borel_core_eq_product h c,hSc,
    hlayers.2.1,hlayers.2.2.1⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
