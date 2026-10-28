module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal

/-!
# The extraspecial lift from the selected orthogonal configuration

The selected moved module in U/Z(U) supplies both its order and the invariant
interval needed to construct A=[U,i] and D=[U,i]⟨i,z⟩. Its constructed quotient
A/⟨z⟩ also supplies the original action used in the exchanged-core argument.
Thus the action and symmetric-local calculations have one common input, with
no separate irreducibility, lifted-module, core, or local Sylow premise.

The result retains the full transvection group, both literal quotient actions,
the intrinsic core images, symmetry with U^x, and both Sylow witnesses for the
original T. The existing Normalizer theorems give irreducibility and the final
core intersection. The case-(3) coordinates, U=O₂(C_G(z)), and selected component,
moved-module and centralizer-modulo-⟨z⟩ data remain the precise earlier inputs
from 14.4.2, 14.4.7 and the orthogonal selection. Their source assembly and the
terminal Appendix A.3.14 exclusion belong to the parent Orthogonal task.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G]

/-- The selected binary module itself supplies the rank-four cardinality. -/
theorem MovedCoreModel.card_movedImage {U K : Subgroup G} {i : G}
    {hKU : K ≤ normalizer (U : Set G)} (m : MovedCoreModel U K i hKU) :
    Nat.card (movedImage U i) = 16 := by
  calc
    Nat.card (movedImage U i) = Nat.card (BinaryPermutation.core (Fin 5)) :=
      Nat.card_congr m.equiv.toEquiv
    _ = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        BinaryPermutation.finrank_core]
      rfl

variable [Finite G]

/-- The original quotient action required by the symmetry argument is
constructed from the proved A/⟨z⟩ factor. Its quotient map has exactly the
central-line kernel, and its residual actor still covers the whole A₅. -/
noncomputable def ChiefModuleResult.originalMovedAction
    {U : Subgroup G} {z i : G}
    {hKU : diagonalResidual (centralizer ({z} : Set G)) i ≤ normalizer (U : Set G)}
    {m : MovedCoreModel U (diagonalResidual (centralizer ({z} : Set G)) i) i hKU}
    (r : ChiefModuleResult U (diagonalResidual (centralizer ({z} : Set G)) i) z i hKU m) :
    ExchangedModel.OriginalMovedAction U z i := by
  let _ := r.normal_ZA
  let q := QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i))
  refine {
    normalizes := le_sup_left.trans r.series.normalizes_A
    quotient := r.base.equiv.toMonoidHom.comp q
    surjective := r.base.equiv.surjective.comp (QuotientGroup.mk'_surjective _)
    kernel := ?_
    actor := m.π.comp (inclusion le_sup_left)
    actor_surjective := m.restriction_surjective
    equivariant := ?_ }
  · rw [MonoidHom.ker_comp_of_injective q r.base.equiv.toMonoidHom r.base.equiv.injective]
    exact QuotientGroup.ker_mk' _
  · intro k a
    change r.base.equiv (q _) = Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5)
        (m.π (inclusion le_sup_left k)).val (r.base.equiv (q a)).toAdd)
    rw [← r.base.equivariant]
    apply congrArg r.base.equiv
    exact (r.base.formula (inclusion le_sup_left k) a).symm

/-- Output of the lift construction. The action field includes elementary
orders 32 and 64, the chief factors and their actual quotient actions, the
element-centralizer bound, the two original centralizer equalities, and the
full group of central transvections. Every field is constructed by
`lift_of_selected_configuration`; none is a source assumption. -/
structure LiftResult (U : Subgroup G) (T : Sylow 2 G) (z x : G)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (U : Set G))
    (m : MovedCoreModel U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU) where
  actions : LiftActionResult U
    (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
    z (conjugateElement z x) hKU m
  joint_core : centralizerLift U z (conjugateElement z x) =
    (centralizer ((zpowers z ⊔ zpowers (conjugateElement z x) : Subgroup G) : Set G)).pCoreIn 2
  overgroup_core : U ⊔ centralizerLift U z (conjugateElement z x) =
    (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ⊔ U ⊔
      centralizerLift U z (conjugateElement z x)).pCoreIn 2
  symmetric_residual : diagonalResidual (conjugateCore (centralizer ({z} : Set G)) x) z =
    diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)
  symmetric_lift : centralizerLift (conjugateCore U x) (conjugateElement z x) z =
    centralizerLift U z (conjugateElement z x)
  conjugate_normalizes : conjugateCore U x ≤
    normalizer (centralizerLift U z (conjugateElement z x) : Set G)
  conjugate_fixed_line : centralizerLift U z (conjugateElement z x) ⊓
    centralizer (conjugateCore U x : Set G) = zpowers (conjugateElement z x)
  local_sylow : ∃ P : Sylow 2 (centralizer ({z} : Set G) ⊓
      normalizer (centralizerLift U z (conjugateElement z x) : Set G) : Subgroup G),
    (P : Subgroup (centralizer ({z} : Set G) ⊓
      normalizer (centralizerLift U z (conjugateElement z x) : Set G) : Subgroup G)) =
      (localSylow (T : Subgroup G) (centralizerLift U z (conjugateElement z x))).subgroupOf
        (centralizer ({z} : Set G) ⊓
          normalizer (centralizerLift U z (conjugateElement z x) : Set G))
  symmetric_normalizes : symmetricActor U z x ≤
    normalizer (centralizerLift U z (conjugateElement z x) : Set G)
  irreducible : ∀ E : Subgroup G, E ≤ centralizerLift U z (conjugateElement z x) →
    symmetricActor U z x ≤ normalizer (E : Set G) →
    E = ⊥ ∨ E = centralizerLift U z (conjugateElement z x)
  normalizer_core : let D := centralizerLift U z (conjugateElement z x)
    let N := normalizer (D : Set G)
    D ≤ N.pCoreIn 2 ∧ N.pCoreIn 2 ≤ centralizer (D : Set G) ∧
      (U ⊔ D) ⊓ N.pCoreIn 2 = D
  global_sylow : ∃ P : Sylow 2 (normalizer (centralizerLift U z (conjugateElement z x) : Set G)),
    (P : Subgroup (normalizer (centralizerLift U z (conjugateElement z x) : Set G))) =
      (localSylow (T : Subgroup G) (centralizerLift U z (conjugateElement z x))).subgroupOf
        (normalizer (centralizerLift U z (conjugateElement z x) : Set G))

/-- The complete extraspecial-lift and symmetric-local implication of
14.4.9, through promotion of the original T_D to Syl₂(N_G(D)). Only the
earlier selected configuration is an input. The moved rank, irreducibility,
original lifted action, core identities and both Sylow witnesses are proved. -/
theorem lift_of_selected_configuration
    (U : Subgroup G) [IsExtraspecial 2 U] (T : Sylow 2 G) (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T)
    (hout : conjugateElement z x ∉ U)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (U : Set G))
    (m : MovedCoreModel U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
    (exchanged : ExchangedModel.CaseThreeAction
      (centralizer ({conjugateElement z x} : Set G)) (conjugateCore U x))
    (components : QuotientModel.SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,hTz hiT⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))))
    (hcompare : ((commutatorPreimage (centralizer ({z} : Set G))
        (zpowers (conjugateElement z x)) (zpowers z)).subgroupOf
        (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) =
      centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,hTz hiT⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) :
    Nonempty (LiftResult U T z x hKU m) := by
  let i := conjugateElement z x
  let H := centralizer ({z} : Set G)
  have hi : orderOf i = 2 := by
    simpa only [i, conjugateElement, MulEquiv.orderOf_eq] using hz
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hiU := hHU (hTz hiT)
  have hmoved := m.card_movedImage
  obtain ⟨a⟩ := diagonalResidual_lift_actions U z i hz hi hZ hiU (hTz hiT)
    hout hKU hUcard hmoved m
  obtain ⟨hD,_,hjoint,hover,hres,_,hlift,hnorm,hUxD,hCU,hCUx,hself,hlocal⟩ :=
    lift_symmetric_local_of_selected U T z x hz hZ hUcore hUcard hTz hiT hout hmoved
      (m.invariant_interval z hZ hiU hmoved) a.chief.originalMovedAction
      exchanged components hcompare
  have hUT : U ≤ (T : Subgroup G) := by
    rw [← hUcore]
    rintro u ⟨v,hv,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTz) hv
  have hY : symmetricActor U z x ≤ normalizer (centralizerLift U z i : Set G) :=
    sup_le hnorm hUxD
  exact ⟨{
    actions := a
    joint_core := hjoint
    overgroup_core := hover
    symmetric_residual := hres
    symmetric_lift := hlift
    conjugate_normalizes := hUxD
    conjugate_fixed_line := hCUx
    local_sylow := hlocal
    symmetric_normalizes := hY
    irreducible := lift_irreducible_of_symmetric_centralizers U z x hz
      (IsExtraspecial.isPGroup 2 U) hD hCU hCUx
    normalizer_core := lift_normalizer_core U z x hz
      (IsExtraspecial.isPGroup 2 U) hD hY hCU hCUx hself
    global_sylow := lift_normalizer_sylow U T z i hz hUT
      (le_sup_right.trans hnorm) hTz hCU hlocal }⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
