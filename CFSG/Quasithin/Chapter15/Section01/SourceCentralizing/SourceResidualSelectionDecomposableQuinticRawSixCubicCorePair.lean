module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicPair
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicPair

/-!
# The native cubic pair above the original two-core

Pull the canonical parabolics back through exactly O₂(X). Each has full
kernel O₂(X), characteristic two, and S₃ quotient by its own two-core.
The pair contains the same Sylow and generates X. The final invariance
clause retains the genuine induced action on both successive quotients.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.RawSixCubicSplit
open Theory.SpecificGroups.SymmetricSix
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem lift_model (N : Subgroup X) [N.Normal] {D : Subgroup (X ⧸ N)}
    (e : D ≃* Equiv.Perm (Fin 4)) :
    let P := D.comap (QuotientGroup.mk' N)
    ∃ f : P →* Equiv.Perm (Fin 4), Function.Surjective f ∧ f.ker = N.subgroupOf P := by
  let q := QuotientGroup.mk' N
  let P := D.comap q
  let r : P →* D := q.subgroupComap D
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hxy⟩ := QuotientGroup.mk'_surjective N y
    refine ⟨⟨x,?_⟩,Subtype.ext hxy⟩
    change q x ∈ D
    exact hxy ▸ y.property
  refine ⟨e.toMonoidHom.comp r,e.surjective.comp hr,?_⟩
  ext x
  change e (r x) = 1 ↔ (x : X) ∈ N
  rw [←map_one e,e.injective.eq_iff,Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

/-- Two literal parabolics above the same full two-core, with their complete
quotient maps and invariance under the actual natural central action. -/
theorem full_core_pair
    (hfit : generalizedFitting X = pCore 2 X)
    (hperfect : Group.IsPerfect (X ⧸ pCore 2 X))
    (e : ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) ≃* A6)
    (hc : IsPGroup 3 (center (X ⧸ pCore 2 X))) (S : Sylow 2 X) :
    ∃ P Q : Subgroup X,
      (S : Subgroup X) ≤ P ∧ (S : Subgroup X) ≤ Q ∧ P ⊔ Q = ⊤ ∧
      generalizedFitting P = pCore 2 P ∧ generalizedFitting Q = pCore 2 Q ∧
      (∃ f : P →* Equiv.Perm (Fin 4), Function.Surjective f ∧
        f.ker = (pCore 2 X).subgroupOf P) ∧
      (∃ f : Q →* Equiv.Perm (Fin 4), Function.Surjective f ∧
        f.ker = (pCore 2 X).subgroupOf Q) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) ∧
      ∀ a : MulAut X,
        MulAut.centralQuotientAction e (quotientAut (pCore 2 X) a) ∈
          _root_.AlternatingSix.ShadowLocal.natural →
        (S : Subgroup X).map a.toMonoidHom = S →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q := by
  let := hperfect
  let N := pCore 2 X
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  let S' := S.mapSurjective hq
  obtain ⟨D,E,hSD,hSE,hDE,⟨eD⟩,⟨eE⟩,hinv⟩ := central_cover_pair e hc S'
  let P := D.comap q
  let Q := E.comap q
  have hSP : (S : Subgroup X) ≤ P := map_le_iff_le_comap.mp hSD
  have hSQ : (S : Subgroup X) ≤ Q := map_le_iff_le_comap.mp hSE
  have hNP : N ≤ P := (pCore_isPGroup.le_sylow_of_normal S).trans hSP
  have hNQ : N ≤ Q := (pCore_isPGroup.le_sylow_of_normal S).trans hSQ
  have hgen : P ⊔ Q = ⊤ := by
    have hh : (P ⊔ Q).map q = ⊤ := by
      rw [Subgroup.map_sup,map_comap_eq_self_of_surjective hq,
        map_comap_eq_self_of_surjective hq,hDE]
    have hh' := congrArg (Subgroup.comap q) hh
    rw [comap_map_eq,QuotientGroup.ker_mk',comap_top,
      sup_eq_left.mpr (hNP.trans le_sup_left)] at hh'
    exact hh'
  obtain ⟨fP,hfP,hkP⟩ := lift_model N eD
  obtain ⟨fQ,hfQ,hkQ⟩ := lift_model N eE
  have hPk : IsPGroup 2 fP.ker := hkP ▸ pCore_isPGroup.comap_subtype
  have hQk : IsPGroup 2 fQ.ker := hkQ ▸ pCore_isPGroup.comap_subtype
  refine ⟨P,Q,hSP,hSQ,hgen,
    generalizedFitting_eq_pCore_of_normalized_by_pCore P hfit (hNP.trans P.le_normalizer),
    generalizedFitting_eq_pCore_of_normalized_by_pCore Q hfit (hNQ.trans Q.le_normalizer),
    ⟨fP,hfP,hkP⟩,⟨fQ,hfQ,hkQ⟩,
    ⟨(fP.pCoreQuotientEquiv hfP hPk).trans
      (Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv (MulEquiv.refl _))⟩,
    ⟨(fQ.pCoreQuotientEquiv hfQ hQk).trans
      (Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv (MulEquiv.refl _))⟩,?_⟩
  intro a ha hS
  let b := quotientAut N a
  have hab : ∀ x, q (a x) = b (q x) := fun x => (quotientAut_apply_mk N a x).symm
  have hSb : (S' : Subgroup (X ⧸ N)).map b.toMonoidHom = S' := by
    change ((S : Subgroup X).map q).map b.toMonoidHom = (S : Subgroup X).map q
    rw [map_map]
    have hh : b.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext fun x => (hab x).symm
    rw [hh,←map_map,hS]
  obtain ⟨hD,hE⟩ := hinv b ha hSb
  exact ⟨preimage_preserved q a b hab D hD,preimage_preserved q a b hab E hE⟩

end CFSG.Quasithin.Chapter15.Section01.RawSixCubicSplit
