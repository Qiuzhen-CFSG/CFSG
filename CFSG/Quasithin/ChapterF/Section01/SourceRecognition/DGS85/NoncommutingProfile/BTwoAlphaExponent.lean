module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicCoreOrders

/-!
# Fourth powers in the original linear alpha core

The actual neighboring-core intersection D_alpha is elementary. The
canonical quotient of the whole alpha core by that same subgroup is also
elementary in the linear beta branch. Squaring therefore lands in D_alpha,
and a second squaring is trivial. No strictness, nonbinary-field or
selected module hypothesis is needed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction Noncommuting NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- Every element of the whole original alpha core has fourth power one,
from the elementary actual D-subgroup and its canonical elementary quotient. -/
theorem original_bTwo_linear_alpha_fourth_power
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K)) :
    ∀ x∈(parabolic L S 0).pCoreIn 2, x^4=1 := by
  obtain ⟨k,f,fin,ch,alg,c,hactor,_,_,hD,_⟩ :=
    original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne e
  let _ := f
  let _ := fin
  let _ := ch
  let _ := alg
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  obtain ⟨_,_,_,_,hN,hE,_⟩ := original_bTwo_linear_core_layers h hb c hactor
    hcentral ht htne hcomm (reduced_graph_core_obstruction h α β hab) e
  let _ := hN
  let _ := hE
  let _ := hD
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype
  intro x hx
  let y : Q₀ := ⟨x,hx⟩
  have hquot : (QuotientGroup.mk' (D₀.subgroupOf Q₀) y)^2=1 :=
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) _)
  have hsq : x^2∈D₀ := by
    have hh : y^2∈D₀.subgroupOf Q₀ := (QuotientGroup.eq_one_iff (y^2)).mp
      (by
        change QuotientGroup.mk' (D₀.subgroupOf Q₀) (y^2)=1
        rw [map_pow]
        exact hquot)
    exact hh
  have hh : (x^2)^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x^2) hsq
  simpa only [←pow_mul] using hh

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
