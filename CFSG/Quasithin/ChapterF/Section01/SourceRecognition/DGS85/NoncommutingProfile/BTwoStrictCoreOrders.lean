module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoTerminalResidual

/-!
# Exact orders in the unrestricted strict Chapter 10 branch

The original terminal separation gives the same residual order in every
characteristic-two field. Multiplication in the opposite-center decomposition
then computes D_alpha. The saturated quotient and the adjacent-core index
compute both original endpoint cores and the full original Borel two-core.
The field coordinates are compared through the literal alpha quotient,
and the beta Frattini and derived subgroup maps are preserved.

This proves the order clause used by the strict seven-path count without
assuming nonsolvability or excluding binary fields. The original Sylow S
can extend the Borel two-core; the statement retains that distinction.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10)(b), printed pp.164--165, using (10.7)--(10.8).
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
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

/-- The exact strict core and full Borel two-core orders in the original
markings, including binary fields. The beta Frattini and derived maps
are retained alongside the numerical profile. -/
theorem original_bTwo_strict_core_orders
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁⊓(Q F t).map ι
    let Z₀ := (Z F α).map ι
    let Z₁ := (Z F β).map ι
    Z₀≤D₀ ∧ D₀≤Q₀ ∧ IsElementaryAbelian 2 D₀ ∧
      Nat.card Z₀=Nat.card (K false)^2 ∧ Nat.card Z₁=Nat.card (K false) ∧
      Nat.card D₀=Nat.card (K false)^2*Nat.card (K true) ∧
      Nat.card Q₀=Nat.card (K false)^2*Nat.card (K true)^3 ∧
      Nat.card Q₁=Nat.card (K false)^3*Nat.card (K true)^2 ∧
      (commonBorel L S).pCoreIn 2=Q₀⊔Q₁ ∧
      Nat.card ((commonBorel L S).pCoreIn 2)=Nat.card (K false)^3*Nat.card (K true)^3 ∧
      (frattini Q₁).map Q₁.subtype=Z₁ ∧ ⁅Q₁,Q₁⁆=Z₁ := by
  obtain ⟨k,f,fin,ch,alg,c,hactor,hZD,hDQ,hDel,hZ,hQa,hQb,_,_,_,hPhi,hder,_,_,_⟩ :=
    original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne (e true)
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K i)).symm
  have hka : Nat.card k=Nat.card (K false) := action_field_card h c hactor (eG false)
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  obtain ⟨g,hg,hgt,hcardR,_⟩ :=
    original_bTwo_strict_terminal_residual h hc hne hb hβu ht htne K e hD
  let g' : c.actor := ⟨g,hactor.symm ▸ hg⟩
  have hop : c.quotient g'∉normalizer (c.imageSylow:Set SL(2,k)) := by
    intro he
    exact htne (hgt.symm.trans (c.normalizer_fixes_neighbor H g' he))
  obtain ⟨d,hdactor,_⟩ := c.exists_oppositeGeometry H (reduced_kernel_sylow h) hb g' hgt hop
  obtain ⟨dp,_⟩ := d.direct_product H (reduced_kernel_sylow h) hb (hdactor.symm ▸ hω)
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁⊓(Q F t).map ι
  let Z₀ := (Z F α).map ι
  let Z₁ := (Z F β).map ι
  let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
  let R₀ := D₀⊓centralizer (W₀:Set G)
  let R := bTwoResidual F β t u (g • u)
  have hQam : (Q F α).map ι=Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι=Q₁ := reduced_base_Q_map h true
  have hDm : (D F β t).map ι=D₀ := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  have hRm : R.map ι=R₀ := by
    change (D F β t⊓centralizer ((Z F u⊔Z F (g • u):Subgroup (G₀ L S)):Set (G₀ L S))).map ι=_
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,Subgroup.map_sup]
  have hDr : Nat.card (D F β t)=Nat.card (K false)^2*Nat.card (K true) := by
    have hp : Nat.card (D F β t)=Nat.card (Z F α)*Nat.card R :=
      (Nat.card_congr dp.symm.toEquiv).trans (Nat.card_prod _ _)
    rw [hp]
    have hzmap : Nat.card (Z F α)=Nat.card Z₀ :=
      (card_map_of_injective (f:=ι) (G₀ L S).subtype_injective).symm
    have hrmap : Nat.card R=Nat.card R₀ := by
      rw [←hRm,card_map_of_injective (G₀ L S).subtype_injective]
    rw [hzmap,hrmap]
    change Nat.card Z₀*Nat.card R₀=_
    change Nat.card R₀=Nat.card (K true) at hcardR
    change Nat.card Z₀=Nat.card k^2 at hZ
    rw [hcardR,hZ,hka]
  have hDc : Nat.card D₀=Nat.card (K false)^2*Nat.card (K true) := by
    rw [←hDm,card_map_of_injective (G₀ L S).subtype_injective,hDr]
  have hQac : Nat.card Q₀=Nat.card (K false)^2*Nat.card (K true)^3 := by
    change Nat.card Q₀=Nat.card (K true)^2*Nat.card D₀ at hQa
    rw [hQa,hDc]
    ring
  have hQbc : Nat.card Q₁=Nat.card (K false)^3*Nat.card (K true)^2 := by
    change Nat.card Q₁=Nat.card k*Nat.card (K true)*Nat.card D₀ at hQb
    rw [hQb,hDc,hka]
    ring
  have hZac : Nat.card Z₀=Nat.card (K false)^2 := by
    change Nat.card Z₀=Nat.card k^2 at hZ
    exact hZ.trans (congrArg (·^2) hka)
  have hZbc : Nat.card Z₁=Nat.card (K false) := by
    rw [show Z₁=(Z F β).map ι from rfl,card_map_of_injective (G₀ L S).subtype_injective]
    exact (c.central_middle_center_card H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _)).trans hka
  have hSc : Nat.card ((commonBorel L S).pCoreIn 2)=
      Nat.card (K false)^3*Nat.card (K true)^3 := by
    let : Finite (Q F β) := Finite.of_injective
      (inclusion (Q_le_stabilizer F β)) (inclusion_injective _)
    have hi : (Q F β).relIndex (Q F β⊔Q F α)=Nat.card (K true) := by
      have hnQ : Q F β≤normalizer (Q F α:Set (G₀ L S)) :=
        c.neighbor_core_le.trans (c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F α))
      rw [sup_comm,relIndex_sup_of_normalizes _ _ hnQ]
      exact (c.linear_seed_eq_core_and_index H (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) (reduced_kernel_sylow h) hb ht htne
        (reduced_graph_core_obstruction h α β hab) (eG true)).2
    have hQbr : Nat.card (Q F β)=Nat.card (K false)^3*Nat.card (K true)^2 := by
      rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective,hQbm]
      exact hQbc
    have hh := relIndex_mul_relIndex (⊥:Subgroup (G₀ L S)) (Q F β)
      (Q F β⊔Q F α) bot_le le_sup_left
    rw [relIndex_bot_left,relIndex_bot_left,hi,hQbr] at hh
    rw [original_bTwo_borel_core_eq_product h c]
    change Nat.card (Q₀⊔Q₁:Subgroup G)=_
    rw [←hQam,←hQbm,←Subgroup.map_sup,card_map_of_injective (G₀ L S).subtype_injective,sup_comm]
    exact hh.symm.trans (by ring)
  exact ⟨hZD,hDQ,hDel,hZac,hZbc,hDc,hQac,hQbc,
    original_bTwo_borel_core_eq_product h c,hSc,hPhi,hder⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
