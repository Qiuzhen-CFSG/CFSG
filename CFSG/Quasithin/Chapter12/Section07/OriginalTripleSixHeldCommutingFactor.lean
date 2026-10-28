module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldComponentCover
public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphResidualSubgroup
public import Theory.GroupTheory.DisjointCommutingProduct

/-! One actual A₅ factor for the fourth Held local subgroup. The graph
residual is transported into the original ambient group, and its full
centralizer contains the original central four-group. Multiplication gives
the actual direct product with this full centralizer. Identifying that
centralizer as a second A₅ and its product normalizer remains a separate
source 42.14 obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem center_eq_bot_of_alternating_five {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 5)) : center A = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  rw [map_one]
  apply mem_bot.mp
  rw [← alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5))]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)

/-- Construct a literal PSL₂(4) inside the original point component and its
commuting direct product with the full ambient centralizer. -/
theorem original_tripleSix_escaping_commuting_factor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    ∃ R : Subgroup G, R ≤ B ∧
      Nonempty (R ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) Matrix.PSL3Four.F) ∧
      Nonempty (R ≃* alternatingGroup (Fin 5)) ∧
      Nat.card R = 60 ∧ center R = ⊥ ∧
      tripleSixPoint D a t ≤ centralizer (R : Set G) ∧
      Disjoint R (centralizer (R : Set G)) ∧
      ∃ e : R × centralizer (R : Set G) ≃* ↥(R ⊔ centralizer (R : Set G)),
        ∀ r c, (e (r,c) : G) = (r : G) * (c : G) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨hcenter, ⟨c⟩⟩ := original_tripleSix_escaping_component_cover
    h structural D a t ht heven hout
  obtain ⟨γ, _, ⟨e₀⟩, ⟨f₀⟩⟩ := c.exists_graph_residual_subgroup
  let R₀ := (pResidual 2 γ.fixedSubgroup).map γ.fixedSubgroup.subtype
  let R := R₀.map B.subtype
  let j : R ≃* R₀ := (R₀.equivMapOfInjective B.subtype B.subtype_injective).symm
  let e := j.trans e₀
  let f := j.trans f₀
  have hRB : R ≤ B := map_subtype_le R₀
  have hRc : Nat.card R = 60 := by
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hRz : center R = ⊥ := center_eq_bot_of_alternating_five f
  have hVC : tripleSixPoint D a t ≤ centralizer (R : Set G) := by
    rw [← hcenter]
    intro v hv r hr
    exact hv.2 r (hRB hr)
  have hdis : Disjoint R (centralizer (R : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hc
    have hz : (⟨x,hx⟩ : R) ∈ center R :=
      mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property))
    rw [hRz, mem_bot] at hz
    exact congrArg Subtype.val hz
  refine ⟨R, hRB, ⟨e⟩, ⟨f⟩, hRc, hRz, hVC, hdis, ?_⟩
  apply exists_mulEquiv_prod_sup_of_disjoint_of_commuting R _ hdis
  intro r hr c hc
  exact (hc r hr).symm

end CFSG.Quasithin.Chapter12.Section07
