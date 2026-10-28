module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalar
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCoreRestriction

/-!
# The scalar commutator of the original whole two-core

The exact pair denominator is central modulo U. Two-perfect coprime
commutator idempotence therefore improves the scalar bound on the pair
layer to a bound by U itself. Applying idempotence twice more gives the
same bound for the actual whole two-core of KT.

Source: the first step of Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal scalar residual centralizes the unchanged whole core of
KT modulo the original chosen module U. -/
theorem original_tripleSix_central_closure_scalar_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    ⁅(K ⊔ (T : Subgroup G)).pCoreIn 2,tripleSixScalarResidual K⁆ ≤ U := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  obtain ⟨g,hKI,hIe,hscalar⟩ :=
    original_tripleSix_central_closure_scalar h structural D a z hz hzT hnot houter
  let Wg := W.map (MulAut.conj g.val).toMonoidHom
  let I := W ⊔ Wg
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let Q := I.pCoreIn 2
  let P := ⁅Q,I⁆
  let N := (W ⊓ Wg) ⊔ U
  have hXK : X ≤ K := map_subtype_le _
  have hXI : X ≤ I := hXK.trans hKI
  have hXM : X ≤ M := hXK.trans le_sup_left
  have hXp : IsPPerfect 2 X := by
    let Z := centralPreimage (pCore 2 K)
    let R := (pResidual 2 Z).map Z.subtype
    let e := R.equivMapOfInjective K.subtype K.subtype_injective
    exact (isPPerfect_embedded_pResidual_of_finite 2 Z).of_surjective
      e.toMonoidHom e.surjective
  have hWT : W ≤ (T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot).1
  have hIM : I ≤ M := hIe.le.trans (sup_le le_sup_left (hWT.trans le_sup_right))
  have hMU : M ≤ normalizer (U : Set G) :=
    sup_le D.normalizes ((structural K h).2.2 U D).1
  have hIU : I ≤ normalizer (U : Set G) := hIM.trans hMU
  have hphi : (frattini W).map W.subtype ≤ zpowers (z : G) :=
    (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).2.2.2.1
  have hWW : ⁅W,W⁆ ≤ U :=
    (derived_le_of_frattini_image_le (T.isPGroup'.to_le hWT) hphi).trans
      (zpowers_le.mpr z.property)
  have hWgWg : ⁅Wg,Wg⁆ ≤ U := by
    have hh := map_mono (f := (MulAut.conj g.val).toMonoidHom) hWW
    have hUg : U.map (MulAut.conj g.val).toMonoidHom=U :=
      mem_normalizer_iff_map_conj_eq.mp (D.normalizes g.property)
    rw [map_commutator,hUg] at hh
    exact hh
  have hNI : ⁅N,I⁆ ≤ U :=
    commutator_sup_le_of_relative_normal I (W ⊓ Wg) U I U hIU
      (inf_le_left.trans le_sup_left) (D.le_component.trans hKI)
      (intersection_commutator_sup_le hWW hWgWg hIU)
      (le_normalizer_iff_commutator_le_left.mp hIU)
  have hIQ : I ≤ normalizer (Q : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hP2 : IsPGroup 2 P := (isPGroup_pCoreIn 2 I).to_le
    (le_normalizer_iff_commutator_le_left.mp hIQ)
  have hPX : ⁅P,X⁆ ≤ U := by
    rw [←commutator_isPPerfect_idempotent X P hXp hP2
      (hXI.trans (normalizer_commutator_ge_right Q I))]
    exact (commutator_mono hscalar hXI).trans hNI
  have hQX : ⁅Q,X⁆ ≤ U := by
    rw [←commutator_isPPerfect_idempotent X Q hXp (isPGroup_pCoreIn 2 I)
      (hXI.trans hIQ)]
    exact (commutator_mono (commutator_mono le_rfl hXI) le_rfl).trans hPX
  have hMK : M ≤ normalizer (K : Set G) :=
    sup_le K.le_normalizer D.sylow_normalizes_component
  have hMQ : M ≤ normalizer (M.pCoreIn 2 : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hstep : ⁅M.pCoreIn 2,X⁆ ≤ Q := by
    apply le_trans _ (pCoreIn_mono_of_normalizes hKI (hIM.trans hMK))
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show K ≤ M from le_sup_left))
    exact le_inf
      ((commutator_mono le_rfl hXK).trans
        (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 M).trans hMK)))
      (le_normalizer_iff_commutator_le_left.mp (hXM.trans hMQ))
  rw [←commutator_isPPerfect_idempotent X (M.pCoreIn 2) hXp (isPGroup_pCoreIn 2 M)
    (hXM.trans hMQ)]
  exact (commutator_mono hstep le_rfl).trans hQX

end CFSG.Quasithin.Chapter12.Section07
