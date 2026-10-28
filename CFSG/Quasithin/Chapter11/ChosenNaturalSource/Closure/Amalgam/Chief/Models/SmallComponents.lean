module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Orders
public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.SolvableResidual.Transport
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.Representation.BinaryPlaneSolvable
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# C-components of the complete G.6.4 models

For GL(n,2) and the symmetric models, the solvable residual is trivial or
one of the six small simple groups. Perfectness places every C-component
in that residual, and minimality identifies it. For the full two-factor
extension, the normal closure has cyclic quotient; every C-component lies
in it. The literal commuting, disjoint factors identify that closure with
their product, whose components are the embedded residual factors.

No factor is treated as normal in the full actor: the actual extension and
product embeddings are retained. Simplicity and orders are transported by
the group equivalences in `HasModelOn`. The higher-rank PSL simplicity port
retains its ATLAS attribution in its owning imported module.
Source: Aschbacher--Smith G.6.4, pp.345--346, and 11.5.8, p.784.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models

private theorem simple_perfect_quasisimple {H : Type*} [Group H]
    [IsSimpleGroup H] [Group.IsPerfect H] : IsQuasisimple H := by
  have hz : center H = ⊥ := by
    apply (inferInstance : (center H).Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    exact Group.IsPerfect.not_isSolvable H
      (Group.isSolvable_of_comm fun a b =>
        mem_center_iff.mp (show b ∈ center H from ht.symm ▸ mem_top b) a)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩

private theorem binary_card (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem binary_component {n : ℕ} (hn : 3 ≤ n) (hn5 : n ≤ 5)
    (N : Subgroup (LinearGroup n)) (hN : N.IsCComponent) :
    IsSimpleGroup N ∧ SmallSimpleOrder (Nat.card N) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hn
  let : IsSimpleGroup (LinearGroup n) :=
    (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  let : Group.IsPerfect (LinearGroup n) := BinaryLinear.linearGroup_isPerfect n hn
  let : IsQuasisimple (LinearGroup n) := simple_perfect_quasisimple
  have ht : (⊤ : Subgroup (LinearGroup n)).IsCComponent :=
    (show IsComponent (LinearGroup n) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have he := hN.eq_of_le ht le_top
  let e : N ≃* LinearGroup n := (MulEquiv.subgroupCongr he).trans topEquiv
  refine ⟨e.isSimpleGroup, ?_⟩
  rw [Nat.card_congr e.toEquiv, binary_card]
  interval_cases n <;> norm_num [SmallSimpleOrder, Fin.prod_univ_succ]

private theorem symmetric_component {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8)
    (N : Subgroup (Equiv.Perm (Fin n))) (hN : N.IsCComponent) :
    IsSimpleGroup N ∧ SmallSimpleOrder (Nat.card N) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa)
  let : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa)⟩
  let : IsQuasisimple (alternatingGroup (Fin n)) := simple_perfect_quasisimple
  have hA : (alternatingGroup (Fin n)).IsCComponent :=
    (show IsComponent _ (alternatingGroup (Fin n)) from
      ⟨(inferInstance : (alternatingGroup (Fin n)).Normal).isSubnormal, inferInstance⟩).isCComponent
  let := hN.perfect
  have he := hN.eq_of_le hA (le_of_isPerfect_of_index_eq_two N _
    alternatingGroup.index_eq_two)
  let e : N ≃* alternatingGroup (Fin n) := MulEquiv.subgroupCongr he
  refine ⟨e.isSimpleGroup, ?_⟩
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  interval_cases n <;> norm_num [SmallSimpleOrder, Nat.factorial]

private def ResidualData (H : Type*) [Group H] : Prop :=
  solvableResidual H = ⊥ ∨
    IsQuasisimple (solvableResidual H) ∧ IsSimpleGroup (solvableResidual H) ∧
      SmallSimpleOrder (Nat.card (solvableResidual H))

private theorem residualData_equiv {D H : Type*} [Group D] [Group H] [Finite D]
    (e : D ≃* H) (hH : ResidualData H) : ResidualData D := by
  let r := e.solvableResidualEquiv
  rcases hH with hb | ⟨hq, hs, hc⟩
  · left
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [map_solvableResidual_eq e.toMonoidHom e.surjective, hb]
  · let := hq
    let := hs
    exact Or.inr ⟨IsQuasisimple.of_mulEquiv r.symm, r.isSimpleGroup,
      (Nat.card_congr r.toEquiv).symm ▸ hc⟩

private theorem binary_residual (n : ℕ) (hn : 2 ≤ n) (hn5 : n ≤ 5) :
    ResidualData (LinearGroup n) := by
  by_cases h2 : n = 2
  · subst n
    let : Group.IsSolvable (LinearGroup 2) :=
      BinaryLinear.SmallParabolicLevi.linearGroup_solvable_of_finrank_two (by simp)
    exact Or.inl solvableResidual_eq_bot
  have h3 : 3 ≤ n := by omega
  let : Group.IsPerfect (LinearGroup n) := BinaryLinear.linearGroup_isPerfect n h3
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n h3
  let : IsSimpleGroup (LinearGroup n) :=
    (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  let : IsQuasisimple (LinearGroup n) := simple_perfect_quasisimple
  have he : solvableResidual (LinearGroup n) = ⊤ := solvableResidual_eq_top
  let e : solvableResidual (LinearGroup n) ≃* LinearGroup n :=
    (MulEquiv.subgroupCongr he).trans topEquiv
  have hcomp : (solvableResidual (LinearGroup n)).IsCComponent := by
    rw [he]
    exact (show IsComponent (LinearGroup n) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact Or.inr ⟨IsQuasisimple.of_mulEquiv e.symm, binary_component h3 hn5 _ hcomp⟩

private theorem symmetric_residual (n : ℕ) (hn : 5 ≤ n) (hn8 : n ≤ 8) :
    ResidualData (Equiv.Perm (Fin n)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa)
  let : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa)⟩
  let : IsQuasisimple (alternatingGroup (Fin n)) := simple_perfect_quasisimple
  have he : solvableResidual (Equiv.Perm (Fin n)) = alternatingGroup (Fin n) := by
    exact le_antisymm
      (le_of_isPerfect_of_index_eq_two _ _ alternatingGroup.index_eq_two)
      (le_solvableResidual_of_isPerfect _)
  let e : solvableResidual (Equiv.Perm (Fin n)) ≃* alternatingGroup (Fin n) :=
    MulEquiv.subgroupCongr he
  have hcomp : (solvableResidual (Equiv.Perm (Fin n))).IsCComponent := by
    rw [he]
    exact (show IsComponent _ (alternatingGroup (Fin n)) from
      ⟨(inferInstance : (alternatingGroup (Fin n)).Normal).isSubnormal, inferInstance⟩).isCComponent
  exact Or.inr ⟨IsQuasisimple.of_mulEquiv e.symm, symmetric_component hn hn8 _ hcomp⟩

private theorem component_of_residual {H : Type*} [Group H] [Finite H]
    (hH : ResidualData H) (N : Subgroup H) (hN : N.IsCComponent) :
    IsSimpleGroup N ∧ SmallSimpleOrder (Nat.card N) := by
  let := hN.perfect
  have hle := le_solvableResidual_of_isPerfect N
  rcases hH with hb | ⟨hq, hs, hc⟩
  · exact (hN.ne_bot (bot_unique (hle.trans hb.le))).elim
  let := hq
  let := hs
  have hr : (solvableResidual H).IsCComponent :=
    (show IsComponent H (solvableResidual H) from
      ⟨(inferInstance : (solvableResidual H).Normal).isSubnormal, inferInstance⟩).isCComponent
  let e := MulEquiv.subgroupCongr (hN.eq_of_le hr hle)
  exact ⟨e.isSimpleGroup, (Nat.card_congr e.toEquiv).symm ▸ hc⟩

open ChapterG.Section06 in
private theorem factor_residual {H W : Type*} [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W)
    (K : Subgroup H) (U : Submodule (ZMod 2) W) (hm : FactorModel ρ K U) :
    ResidualData K := by
  rcases hm with ⟨n, h2, h5, e, _⟩ | ⟨n, h5, h8, e, _⟩ | ⟨n, hn, e, _⟩
  · exact residualData_equiv e (binary_residual n h2 h5)
  · exact residualData_equiv e (symmetric_residual n h5 h8)
  · exact residualData_equiv e (symmetric_residual n (by omega) (by omega))

open ChapterG.Section06 in
private theorem small_factor_residual {H W : Type*} [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W)
    (K : Subgroup H) (U : Submodule (ZMod 2) W) (hm : SmallFactorModel ρ K U) :
    ResidualData K := by
  apply factor_residual ρ K U
  rcases hm with h | h | h
  · exact Or.inl ⟨2, le_rfl, by decide, h⟩
  · exact Or.inl ⟨3, by decide, by decide, h⟩
  · exact Or.inr (Or.inl ⟨5, le_rfl, by decide, h⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models

private theorem product_component {D H : Type*} [Group D] [Group H] [Finite D] [Finite H]
    (hD : ResidualData D) (hH : ResidualData H)
    (N : Subgroup (D × H)) (hN : N.IsCComponent) :
    IsSimpleGroup N ∧ SmallSimpleOrder (Nat.card N) := by
  have hd : solvableResidual D = ⊥ ∨ IsQuasisimple (solvableResidual D) :=
    hD.imp_right And.left
  have hh : solvableResidual H = ⊥ ∨ IsQuasisimple (solvableResidual H) :=
    hH.imp_right And.left
  rcases cComponent_eq_residual_factor hd hh hN with he | he
  · rcases hD with hb | ⟨_, hs, hc⟩
    · exact (hN.ne_bot (by rw [he, hb, bot_prod_bot])).elim
    let := hs
    let e : N ≃* solvableResidual D := (MulEquiv.subgroupCongr he).trans residualLeftEquiv
    exact ⟨e.isSimpleGroup, (Nat.card_congr e.toEquiv).symm ▸ hc⟩
  · rcases hH with hb | ⟨_, hs, hc⟩
    · exact (hN.ne_bot (by rw [he, hb, bot_prod_bot])).elim
    let := hs
    let e : N ≃* solvableResidual H := (MulEquiv.subgroupCongr he).trans residualRightEquiv
    exact ⟨e.isSimpleGroup, (Nat.card_congr e.toEquiv).symm ▸ hc⟩

open ChapterG.Section06 in
private theorem two_factor_component {H W : Type*} [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W)
    (a : H) (d : TwoFactors ρ a) (N : Subgroup H) (hN : N.IsCComponent) :
    IsSimpleGroup N ∧ SmallSimpleOrder (Nat.card N) := by
  let K := normalClosure ({a} : Set H)
  obtain ⟨t, _, _, hgen, _⟩ := d.extension
  let f := (QuotientGroup.mk' K).comp (zpowers t).subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    have hmap := congrArg (map (QuotientGroup.mk' K)) hgen
    change map (QuotientGroup.mk' K) (K ⊔ zpowers t) = _ at hmap
    simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] using hmap
  let : Group.IsSolvable (H ⧸ K) := Group.isSolvable_of_surjective hf
  let := hN.perfect
  have hNK : N ≤ K := le_of_isPerfect_of_solvable_quotient N K
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    d.first d.second (disjoint_iff.mpr d.disjoint)
    (commutator_eq_bot_iff_le_centralizer.mp d.commute)
  let eK : K ≃* d.first × d.second :=
    (MulEquiv.subgroupCongr d.join_eq.symm).trans e.symm
  let N' := (N.subgroupOf K).map eK.toMonoidHom
  have hN' : N'.IsCComponent := (hN.subgroupOf hNK).map_equiv eK
  obtain ⟨hs, hc⟩ := product_component
    (small_factor_residual ρ d.first _ d.first_model)
    (small_factor_residual ρ d.second _ d.second_model) N' hN'
  let := hs
  let eN : N ≃* N' := (subgroupOfEquivOfLe hNK).symm.trans (eK.subgroupMap _)
  exact ⟨eN.isSimpleGroup, (Nat.card_congr eN.toEquiv).symm ▸ hc⟩

/-- Every C-component of a complete G.6.4 model is simple and has one of
its six possible simple-component orders. This also covers the full
commuting-pair extension, via its literal index-at-most-two normal subgroup. -/
theorem classified_component_small {H W : Type*} [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W)
    (a : H) (hclass : ChapterG.Section06.Conclusion ρ a)
    (N : Subgroup H) (hN : N.IsCComponent) :
    IsSimpleGroup N ∧ SmallSimpleOrder (Nat.card N) := by
  rcases hclass with ⟨hclass, _⟩
  rcases hclass with h | hd
  · have htop := factor_residual ρ ⊤ _ h.2.1
    have hH := residualData_equiv (topEquiv : (⊤ : Subgroup H) ≃* H).symm htop
    exact component_of_residual hH N hN
  · obtain ⟨d⟩ := hd
    exact two_factor_component ρ a d N hN

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
