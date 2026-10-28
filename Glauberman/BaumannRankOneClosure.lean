module
public import Glauberman.SmallMoverBaumann
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# The Baumann normal closure in an active rank-one quotient

If the original Baumann subgroup escapes the full two-core and the quotient
is SL₂ over a nonbinary characteristic-two field, its normal closure covers
the quotient. The restricted quotient map identifies the closure's whole
two-core with the literal intersection. Characteristic two passes to this
normal subgroup, and the SL₂ Sylow theorem gives unique maximality above
its Sylow intersection with the original Sylow.

Source: the F₀ construction in MS93 (5.1), printed p.913, preceding Niles's
application. This proves the normal-closure supplement and its local data;
it does not identify the Sylow intersection with the Baumann subgroup.
The actual source application is CriticalReduction.RootProductClosure.
-/

public noncomputable section
open Subgroup
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The Baumann normal closure covers the original rank-one quotient when
the original Baumann subgroup escapes its full two-core. The Sylow
intersection is retained literally; it is not identified with Baumann here. -/
theorem baumann_normalClosure_rank_one (hF : 4 ≤ Nat.card F) (S : Sylow 2 G)
    (q : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (hker : q.ker = pCore 2 G)
    (hB : ¬ baumannSubgroup (S : Subgroup G) ≤ pCore 2 G)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    let N := normalClosure (baumannSubgroup (S : Subgroup G) : Set G)
    N ⊔ pCore 2 G = ⊤ ∧
    Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
    (pCore 2 N).map N.subtype = N ⊓ pCore 2 G ∧
    Theory.GroupTheory.generalizedFitting N = pCore 2 N ∧
    ∃ T : Sylow 2 N, (T : Subgroup N).map N.subtype = (S : Subgroup G) ⊓ N ∧
      Order.HasUniqueMaximalOver (T : Subgroup N) ⊤ := by
  let N := normalClosure (baumannSubgroup (S : Subgroup G) : Set G)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  let : (N.map q).Normal := Normal.map inferInstance q hq
  have hN : N.map q = ⊤ := by
    rcases (inferInstance : (N.map q).Normal).eq_bot_or_eq_top with hz | ht
    · apply False.elim
      apply hB
      rw [←hker]
      exact (show baumannSubgroup (S : Subgroup G) ≤ N from le_normalClosure).trans
        ((map_eq_bot_iff N).mp hz)
    · exact ht
  have hgen : N ⊔ pCore 2 G = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hN
    rwa [comap_map_eq,hker,comap_top] at hh
  let qN := q.comp N.subtype
  have hqN : Function.Surjective qN := by
    intro x
    obtain ⟨y,hy,he⟩ := (show x ∈ N.map q from hN ▸ mem_top _)
    exact ⟨⟨y,hy⟩,he⟩
  have hkN : qN.ker = (pCore 2 G).comap N.subtype := by
    change q.ker.comap N.subtype = _
    rw [hker]
  have hpN : IsPGroup 2 qN.ker := hkN ▸ pCore_isPGroup.comap_subtype
  have hcore : qN.ker = pCore 2 N := by
    have hh := qN.comap_pCore_of_ker_isPGroup hqN hpN
    rwa [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot] at hh
  have hcores : (pCore 2 N).map N.subtype = N ⊓ pCore 2 G := by
    rw [←hcore,hkN,map_comap_eq,range_subtype,inf_comm]
  obtain ⟨T,hT⟩ := S.exists_sylow_map_eq_inf_of_normal N
  have hu := Subgroup.hasUniqueMaximalOver_of_surjective qN hqN
    (by rw [hcore]; exact pCore_isPGroup.le_sylow_of_normal T)
    (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver (F := F) 2 (T.mapSurjective hqN))
  exact ⟨hgen,⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective qN hqN)⟩,hcores,
    Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
      (normal_core_selfCentralizing hself N),T,hT,hu⟩
end Glauberman
