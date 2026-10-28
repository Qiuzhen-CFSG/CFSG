module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.Representation.SL3NaturalFlagInvariant
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.GroupAction.SolvableSylowInvariance
public import Theory.GroupTheory.EquivariantParabolicLift

/-!
# Two invariant parabolics in a natural SL3 block

A solvable supplement normalizing a marked natural SL3 block contains the
inner image of a component Sylow subgroup. Solvable Sylow-overgroup control
therefore makes its quotient action preserve that Sylow. The induced additive
action on the actual block module distinguishes the two maximal parabolics.
Their full preimages are proper, generate the original block, and contain its
intersection with the supplement.

This supplies the literal two-parabolic input to Aschbacher–Smith 15.3.20,
printed p.1127. All quotient maps retain the full SL3 center.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem solvable_SL3_sylow_normalizer (hF : 4 ≤ Nat.card F)
    (P : Sylow 2 SL(3,F)) (H : Subgroup SL(3,F))
    (hs : Group.IsSolvable H) (hPH : (P : Subgroup _) ≤ H) :
    H ≤ normalizer (P : Set SL(3,F)) := by
  let := Fintype.ofFinite F
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F 2
  rw [← Nat.card_eq_fintype_card] at hcard
  obtain ⟨g,hg,_⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate
    F n.pos hcard P
  let e := MulAut.conj g⁻¹
  have hP : (P : Subgroup SL(3,F)).map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotentSL F := by
    rw [← hg]
    rw [Subgroup.map_map]
    have he : e.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
      simp [mul_assoc]
    rw [he, Subgroup.map_id]
  let : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hU : Matrix.PSL3.LinearThree.unipotentSL F ≤ H.map e.toMonoidHom :=
    hP ▸ map_mono hPH
  have hN := (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_le_borelSL
    F hF (H.map e.toMonoidHom) hU).trans
      (Matrix.PSL3.LinearThree.borelSL_le_normalizer_unipotentSL F)
  rw [← hP, ← map_equiv_normalizer_eq (P : Subgroup SL(3,F)) e] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN

namespace BlockModuleModel
variable {L A : Subgroup G}
variable {ρ : SL(3,F) →* MulAut (Multiplicative (Fin 3 → F))}

/-- A solvable normalizing supplement preserves two generating proper
parabolics in a marked natural SL3 block. -/
theorem exists_invariant_SL3_parabolics (m : BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd = g.val.mulVec v.toAdd)
    (hF : 4 ≤ Nat.card F) (hn : A ≤ normalizer (L : Set G))
    [Group.IsSolvable A] (S : Sylow 2 L)
    (hSA : (S : Subgroup L).map L.subtype ≤ A) :
    ∃ P Q : Subgroup G, P < L ∧ Q < L ∧ P ⊔ Q = L ∧
      A ≤ normalizer (P : Set G) ∧ A ≤ normalizer (Q : Set G) ∧ A ⊓ L ≤ P ⊓ Q := by
  let c : A →* MulAut L := L.normalizerMonoidHom.comp (inclusion hn)
  let α : A →* MulAut SL(3,F) := m.quotientAction.comp c
  let U : Sylow 2 SL(3,F) := S.mapSurjective (f := m.actor) m.actor_surjective
  have heq (a : A) (l : L) : m.actor (L.normalizerMonoidHom (inclusion hn a) l) =
      α a (m.actor l) := (m.quotientAction_actor (c a) l).symm
  have hinner (l : L) (hl : (l : G) ∈ A) : α ⟨l,hl⟩ = MulAut.conj (m.actor l) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨k,rfl⟩ := m.actor_surjective x
    rw [← heq]
    change m.actor (l * k * l⁻¹) = m.actor l * m.actor k * (m.actor l)⁻¹
    simp only [map_mul, map_inv]
  let : Group.IsSolvable α.range := Group.isSolvable_of_surjective α.rangeRestrict_surjective
  have hUA : (U : Subgroup SL(3,F)).map MulAut.conj ≤ α.range := by
    rintro _ ⟨u, hu, rfl⟩
    change u ∈ (S : Subgroup L).map m.actor at hu
    obtain ⟨l,hl,rfl⟩ := hu
    exact ⟨⟨l,hSA (mem_map_of_mem L.subtype hl)⟩,hinner l (hSA (mem_map_of_mem L.subtype hl))⟩
  have hU (a : A) : (U : Subgroup SL(3,F)).map (α a).toMonoidHom = U :=
    MulAut.sylow_map_eq_of_solvable_overgroups U (solvable_SL3_sylow_normalizer hF U)
      α.range hUA (α a) ⟨a,rfl⟩
  obtain ⟨P,Q,hP,hQ,hgen,hbase,hfix⟩ :=
    Representation.SL3NaturalFlagInvariant.exists_invariant_parabolic_pair U
  have himpl (a : A) : ∃ b : (Fin 3 → F) ≃+ (Fin 3 → F),
      ∀ g v, b (g.val.mulVec v) = (α a g).val.mulVec (b v) := by
    let b₀ := m.moduleAction (c a)
    let b : (Fin 3 → F) ≃+ (Fin 3 → F) :=
      { toFun v := (b₀ (Multiplicative.ofAdd v)).toAdd
        invFun v := (b₀.symm (Multiplicative.ofAdd v)).toAdd
        left_inv v := congrArg Multiplicative.toAdd (b₀.symm_apply_apply (Multiplicative.ofAdd v))
        right_inv v := congrArg Multiplicative.toAdd (b₀.apply_symm_apply (Multiplicative.ofAdd v))
        map_add' v w := congrArg Multiplicative.toAdd (b₀.map_mul
          (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
    refine ⟨b, fun g v => ?_⟩
    have hh := congrArg Multiplicative.toAdd (m.actions_compatible (c a) g (Multiplicative.ofAdd v))
    rw [hρ] at hh
    have hr := hρ g (Multiplicative.ofAdd v)
    change (ρ g (Multiplicative.ofAdd v)).toAdd = g.val.mulVec v at hr
    change (b₀ (ρ g (Multiplicative.ofAdd v))).toAdd = _ at hh
    change b (g.val.mulVec v) = _
    rw [← hr]
    exact hh
  let P' := EquivariantLift.lift L m.actor P
  let Q' := EquivariantLift.lift L m.actor Q
  refine ⟨P',Q',EquivariantLift.lift_lt L m.actor m.actor_surjective hP.ne_top,
    EquivariantLift.lift_lt L m.actor m.actor_surjective hQ.ne_top, ?_, ?_, ?_, ?_⟩
  · rw [← EquivariantLift.lift_sup L m.actor m.actor_surjective, hgen,
      EquivariantLift.lift_top]
  · exact EquivariantLift.normalizes_lift L m.actor hn α heq
      (fun a => (hfix (α a) (hU a) (himpl a)).1)
  · exact EquivariantLift.normalizes_lift L m.actor hn α heq
      (fun a => (hfix (α a) (hU a) (himpl a)).2)
  · have hb : ((A ⊓ L).subgroupOf L).map m.actor ≤ P ⊓ Q := by
      rintro _ ⟨l,hl,rfl⟩
      apply hbase
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [← hinner l hl.1]
      exact hU ⟨l,hl.1⟩
    exact le_inf (EquivariantLift.le_lift L m.actor inf_le_right (hb.trans inf_le_left))
      (EquivariantLift.le_lift L m.actor inf_le_right (hb.trans inf_le_right))
end BlockModuleModel
end CFSG.Quasithin.ChapterC
