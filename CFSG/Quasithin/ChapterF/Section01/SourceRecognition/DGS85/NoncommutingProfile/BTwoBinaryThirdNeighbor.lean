module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryExchange

/-!
# The third neighbor in binary residual separation

The binary beta quotient gives exactly three neighbors. The actual strict
residual centralizes the two critical centers, whereas its join with
Z(V_beta) is dihedral of order eight. If the residual lay in the third
neighbor's core, it would centralize all three neighboring centers and
hence V_beta, contradicting that dihedral structure. Its intersection
with the third core is therefore trivial.

In the contrary terminal-intersection case of (10.8), the previously
constructed actor centralizes this same dihedral subgroup. Preservation
of the residual forces the actor to exchange both critical endpoints
and fix the third neighbor. The terminal center also centralizes the
same dihedral subgroup, providing the correcting subgroup used next
in the source. All subgroups are literal original images, with one
opposite-center conjugator retained throughout.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed p.162. Correction of the actor into the third core and
the ensuing centralizer contradiction remain to be proved; the theorem
does not assert the tested terminal intersection is trivial.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

private theorem third_of_card_three {X : Type*} [Finite X]
    (hc : Nat.card X=3) (a b : X) (hab : a≠b) :
    ∃ c : X, c≠a ∧ c≠b ∧ ∀ x:X, x=a ∨ x=b ∨ x=c := by
  classical
  let : Fintype X := Fintype.ofFinite X
  have hnot : ¬ (Finset.univ : Finset X) ⊆ {a,b} := by
    intro hh
    have hh' := Finset.card_le_card hh
    rw [Finset.card_univ,←Nat.card_eq_fintype_card,hc] at hh'
    simp [hab] at hh'
  obtain ⟨c,_,hc'⟩ := Finset.not_subset.mp hnot
  have hca : c≠a := fun he => hc' (by simp [he])
  have hcb : c≠b := fun he => hc' (by simp [he])
  have hall : ({a,b,c}:Finset X)=Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [←Nat.card_eq_fintype_card,hc]
    simp [hab,Ne.symm hca,Ne.symm hcb]
  refine ⟨c,hca,hcb,fun x => ?_⟩
  have hx : x∈({a,b,c}:Finset X) := hall ▸ Finset.mem_univ x
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hx

private theorem dihedral_not_central_radius
    {G : Type*} [Group G] (R V : Subgroup G) [IsMulCommutative R]
    (e : (R⊔centerIn V : Subgroup G)≃*DihedralGroup 4) :
    ¬ R≤centralizer (V:Set G) := by
  intro hh
  have hRV : R≤centralizer (centerIn V:Set G) := hh.trans (centralizer_le (show centerIn V≤V from inf_le_left))
  let : IsMulCommutative (R⊔centerIn V : Subgroup G) := by
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le R.le_centralizer (le_centralizer_iff.mp hRV))
    · exact le_centralizer_iff.mpr (sup_le hRV (show centerIn V≤centralizer (centerIn V:Set G) from inf_le_right.trans (centralizer_le (show centerIn V≤V from inf_le_left))))
  apply DihedralGroup.not_commutative (n:=4) (by decide) (by decide)
  exact ⟨⟨fun x y => by
    obtain ⟨a,rfl⟩ := e.surjective x
    obtain ⟨b,rfl⟩ := e.surjective y
    rw [←map_mul,←map_mul,mul_comm a b]⟩⟩

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The third beta neighbor separates the strict binary residual. Under the
contrary terminal intersection, the actual dihedral-centralizing actor swaps
both critical endpoints and fixes that third neighbor. The terminal center
centralizes the same dihedral subgroup. -/
theorem original_bTwo_binary_third_neighbor
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e : (L 1 ⧸ pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=2)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let V₁ := (V F β 1).map ι
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      let Δ := R₀⊔centerIn V₁
      Nat.card R₀=2 ∧ Nat.card Δ=8 ∧ Nonempty (Δ≃*DihedralGroup 4) ∧
      ∃ δ : Vertex F, (graph F).Adj β δ ∧ δ≠α ∧ δ≠u ∧
        (∀ v : Vertex F, (graph F).Adj β v → v=α ∨ v=u ∨ v=δ) ∧
        R₀⊓(Q F δ).map ι=⊥ ∧
        ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι≠⊥ →
          (Z F y).map ι≤centralizer (Δ:Set G) ∧
          ∃ x∈graphLocalGroup F β, x • α=u ∧ x • u=α ∧ x • δ=δ ∧
            ι x∈enlargedEndpoint L S 1⊓centralizer (Δ:Set G) ∧ ι x∉Q₁ := by
  classical
  obtain ⟨g,hg,hgt,hRcard,hΔcard,⟨eΔ⟩,hexchange⟩ :=
    original_bTwo_binary_exchanging_actor h hc hne hb hβu ht htne e hK hD
  obtain ⟨k,f,fin,ch,alg,c,hactor,hZD,hDQ,hDel,_⟩ :=
    original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne e
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β := c.middle
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let V₁ := (V F β 1).map ι
  let D₀ := Q₁⊓(Q F t).map ι
  let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
  let R := D₀⊓centralizer (W₀:Set G)
  let Δ := R⊔centerIn V₁
  change Nat.card R=2 at hRcard
  change Nat.card Δ=8 at hΔcard
  change Δ≃*DihedralGroup 4 at eΔ
  change (Z F α).map ι≤D₀ at hZD
  change D₀≤Q₀ at hDQ
  change IsElementaryAbelian 2 D₀ at hDel
  let := hDel
  let : IsMulCommutative R :=
    le_centralizer_iff_isMulCommutative.mp
      ((show R≤D₀ from inf_le_left).trans (D₀.le_centralizer.trans (centralizer_le inf_le_left)))
  have hRnot : ¬R≤centralizer (V₁:Set G) := dihedral_not_central_radius R V₁ eΔ
  have hRZa : R≤centralizer ((Z F α).map ι:Set G) :=
    inf_le_left.trans (D₀.le_centralizer.trans (centralizer_le hZD))
  have hRZu : R≤centralizer ((Z F u).map ι:Set G) :=
    inf_le_right.trans (centralizer_le (show (Z F u).map ι≤W₀ from le_sup_left))
  have hRα : R≤(Q F α).map ι := by
    rw [reduced_base_Q_map h false]
    exact inf_le_left.trans hDQ
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hval : Nat.card ((graph F).neighborSet β)=3 := by
    have hi := source_linear_edge_index_of_quotient H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hab.symm eβ
    rw [card_neighbor_base]
    change (F false).relIndex (F true)=3
    change (stabilizer F α).relIndex (stabilizer F β)=Nat.card K+1 at hi
    simpa only [Subgroup.CosetGeometry.stabilizer_base,hK] using hi
  have hau : α≠u := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    contradiction
  let : Finite ((graph F).neighborSet β) := Nat.finite_of_card_ne_zero (by rw [hval]; decide)
  obtain ⟨⟨δ,hδ⟩,hδα,hδu,hall⟩ := third_of_card_three hval
    (⟨α,hab.symm⟩ : (graph F).neighborSet β) ⟨u,hβu⟩ (fun he => hau (congrArg Subtype.val he))
  have hδα' : δ≠α := fun he => hδα (Subtype.ext he)
  have hδu' : δ≠u := fun he => hδu (Subtype.ext he)
  have hall' (v : Vertex F) (hv : (graph F).Adj β v) : v=α ∨ v=u ∨ v=δ := by
    rcases hall ⟨v,hv⟩ with hh|hh|hh
    · exact Or.inl (congrArg Subtype.val hh)
    · exact Or.inr (Or.inl (congrArg Subtype.val hh))
    · exact Or.inr (Or.inr (congrArg Subtype.val hh))
  have hZmZa : Z F β≤Z F α := center_le_of_central_neighbor H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab hcentral
  have hZmZu : Z F β≤Z F u := center_le_of_central_neighbor H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hβu.symm hcentral
  have hspan : V F β 1≤(Z F α⊔Z F u)⊔Z F δ := by
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    rcases (mem_ball_one F β v).mp hv with hv|rfl
    · rcases hall' v hv with rfl|rfl|rfl
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact hZmZa.trans (le_sup_left.trans le_sup_left)
  have hRQδ : ¬R≤(Q F δ).map ι := by
    intro hle
    have hRZδ : R≤centralizer ((Z F δ).map ι:Set G) := hle.trans
      ((map_mono (f:=ι) (graph_Q_centralizes_Z H δ)).trans
        (map_centralizer_le_centralizer_image _ _))
    apply hRnot
    apply le_centralizer_iff.mp
    have hm := map_mono (f:=ι) hspan
    rw [Subgroup.map_sup,Subgroup.map_sup] at hm
    exact hm.trans (sup_le (sup_le (le_centralizer_iff.mp hRZa)
      (le_centralizer_iff.mp hRZu)) (le_centralizer_iff.mp hRZδ))
  have hsep : R⊓(Q F δ).map ι=⊥ := by
    by_contra hn
    let : Finite R := Nat.finite_of_card_ne_zero (by rw [hRcard]; decide)
    let J := R⊓(Q F δ).map ι
    let : Finite J := Finite.of_injective (inclusion (show J≤R from inf_le_left)) (inclusion_injective _)
    have hj : 1<Nat.card J := J.one_lt_card_iff_ne_bot.mpr hn
    have he : J=R := eq_of_le_of_card_ge inf_le_left (by rw [hRcard]; omega)
    exact hRQδ (he ▸ (show J≤(Q F δ).map ι from inf_le_right))
  refine ⟨g,hg,hgt,hRcard,hΔcard,⟨eΔ⟩,δ,hδ,hδα',hδu',hall',hsep,?_⟩
  intro y hy hyne hJne
  obtain ⟨x,hx,hxu,hxΔ,hxQ⟩ := hexchange y hy hyne hJne
  have hxβ : x • β=β := sylowGenerated_le _ hx
  have hQconj (v : Vertex F) :
      ((Q F v).map ι).map (MulAut.conj (ι x)).toMonoidHom=(Q F (x • v)).map ι := by
    rw [Q_translate,map_map,map_map]
    congr 1
  have hRx : R≤(Q F (x • α)).map ι := by
    intro r hr
    have hm := mem_map_of_mem (MulAut.conj (ι x)).toMonoidHom (hRα hr)
    rw [hQconj] at hm
    have he : ι x*r*(ι x)⁻¹=r := by
      rw [←hxΔ.2 r (mem_sup_left hr),mul_inv_cancel_right]
    change ι x*r*(ι x)⁻¹∈_ at hm
    rwa [he] at hm
  rw [hxu] at hRx
  have hRxu : R≤(Q F (x • u)).map ι := by
    intro r hr
    have hm := mem_map_of_mem (MulAut.conj (ι x)).toMonoidHom (hRx hr)
    rw [hQconj] at hm
    have he : ι x*r*(ι x)⁻¹=r := by
      rw [←hxΔ.2 r (mem_sup_left hr),mul_inv_cancel_right]
    change ι x*r*(ι x)⁻¹∈_ at hm
    rwa [he] at hm
  have hxuadj : (graph F).Adj β (x • u) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F x).map_adj_iff.mpr hβu
    change (graph F).Adj (x • β) (x • u) at hh
    rwa [hxβ] at hh
  have hxback : x • u=α := by
    rcases hall' (x • u) hxuadj with hh|hh|hh
    · exact hh
    · exact False.elim (hau ((MulAction.injective x) (hxu.trans hh.symm)))
    · exact False.elim (hRQδ (hh ▸ hRxu))
  have hxδ : x • δ=δ := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F x).map_adj_iff.mpr hδ
    change (graph F).Adj (x • β) (x • δ) at hh
    rw [hxβ] at hh
    rcases hall' (x • δ) hh with hh|hh|hh
    · exact False.elim (hδu' ((MulAction.injective x) (hh.trans hxback.symm)))
    · exact False.elim (hδα' ((MulAction.injective x) (hh.trans hxu.symm)))
    · exact hh
  have hRy : R≤(Q F y).map ι := by
    let : Finite R := Nat.finite_of_card_ne_zero (by rw [hRcard]; decide)
    let J := R⊓(Q F y).map ι
    let : Finite J := Finite.of_injective (inclusion (show J≤R from inf_le_left)) (inclusion_injective _)
    have hj : 1<Nat.card J := J.one_lt_card_iff_ne_bot.mpr hJne
    have he : J=R := eq_of_le_of_card_ge inf_le_left (by rw [hRcard]; omega)
    exact he ▸ (show J≤(Q F y).map ι from inf_le_right)
  obtain ⟨s,hs,hsy⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) u ⟨β,hβu.symm⟩ ⟨y,hy⟩
  change s • β=y at hsy
  have hsu : s • u=u := sylowGenerated_le _ hs
  have hZyZu : Z F y≤Z F u := by
    have hh := map_mono (f:=(MulAut.conj s).toMonoidHom) hZmZu
    rwa [←Z_translate,←Z_translate,hsy,hsu] at hh
  have hZyV : (Z F y).map ι≤V₁ := map_mono (hZyZu.trans
    (le_iSup_of_le u (le_iSup_of_le ((mem_ball_one F β u).mpr (Or.inl hβu)) le_rfl)))
  have hZyC : (Z F y).map ι≤centralizer (Δ:Set G) := by
    apply le_centralizer_iff.mp
    apply sup_le
    · exact hRy.trans ((map_mono (f:=ι) (graph_Q_centralizes_Z H y)).trans
        (map_centralizer_le_centralizer_image _ _))
    · intro z hz a ha
      exact hz.2 a (hZyV ha)
  exact ⟨hZyC,x,hx,hxu,hxback,hxδ,hxΔ,hxQ⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
