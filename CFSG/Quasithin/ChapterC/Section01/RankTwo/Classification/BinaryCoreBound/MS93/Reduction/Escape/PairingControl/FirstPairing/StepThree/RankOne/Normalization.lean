module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.Source
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Lifting fixation modulo the moving radical to commutator normalization

If a two-perfect actor fixes A modulo a normal layer D, and its commutator
with D lies in Z, idempotence of its action on a two-group gives [A,T] ≤ Z.
When Z centralizes Q, this says that T normalizes the literal [A,Q].
The argument uses a commutator preimage, so it does not assume A is T-invariant.

For the moving section D = Z[V,Q], the triple clause supplies [D,T] ≤ Z.
Thus the remaining representation input is fixation of Z_delta modulo that
actual radical by a marked line residual. No coordinates on Vcirc/U or
identification H = U enter this reduction.

The conjugation calculation adapts the private normalization helper in
FirstPairing/Orientation/QuotientApplication/Verification/CommutatorBounds/
CyclicNormalization.lean. Source: MS93 (4.3.2)(3), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne

private theorem normalizes_pairing_of_fixed_mod_centralizer
    {G : Type*} [Group G] (A Q Z T : Subgroup G) [Q.Normal]
    (hZQ : Z ≤ centralizer (Q : Set G)) (hAT : ⁅A, T⁆ ≤ Z) :
    T ≤ normalizer (⁅A, Q⁆ : Subgroup G) := by
  have hreduce := commutator_eq_of_centralizing_sup
    (B := Z ⊔ A) rfl hZQ
    (show A ≤ normalizer (Q : Set G) from le_normalizer_of_normal)
  apply le_normalizer_iff.mpr
  intro t ht k hk
  have hAmap : A.map (MulAut.conj t).toMonoidHom ≤ Z ⊔ A := by
    rintro y ⟨x, hx, rfl⟩
    have hcomm : ⁅t, x⁆ ∈ Z := by
      apply hAT
      rw [commutator_comm]
      exact commutator_mem_commutator ht hx
    have hh := (Z ⊔ A).mul_mem (mem_sup_left hcomm) (mem_sup_right hx)
    change t * x * t⁻¹ ∈ Z ⊔ A
    simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  have hQmap : Q.map (MulAut.conj t).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (show t ∈ normalizer (Q : Set G) from
      le_normalizer_of_normal (mem_top t))
  have hh := mem_map_of_mem (MulAut.conj t).toMonoidHom hk
  rw [map_commutator, hQmap] at hh
  have h := commutator_mono hAmap (le_refl Q) hh
  rw [commutator_comm (Z ⊔ A), ← hreduce, commutator_comm] at h
  exact h

/-- Two-perfect idempotence removes one normal radical layer, without any
invariance assumption on the original subgroup A. -/
theorem pairing_normalized_of_radical_fixed {G : Type*} [Group G] [Finite G]
    (A Q D Z T : Subgroup G) [Q.Normal] [D.Normal]
    (hQ : IsPGroup 2 Q) (hT : IsPPerfect 2 T) (hAQ : A ≤ Q)
    (hAT : ⁅A, T⁆ ≤ D) (hDT : ⁅D, T⁆ ≤ Z)
    (hZQ : Z ≤ centralizer (Q : Set G)) :
    T ≤ normalizer (⁅A, Q⁆ : Subgroup G) := by
  let N := commutatorPreimage Q T D
  have hNT : ⁅N, T⁆ ≤ D :=
    commutator_commutatorPreimage_le Q T D le_normalizer_of_normal
  have hTN : T ≤ normalizer (N : Set G) :=
    commutatorPreimage_normalized Q T D T le_normalizer_of_normal
      le_normalizer_of_normal T.le_normalizer le_normalizer_of_normal
  have hNZ : ⁅N, T⁆ ≤ Z := by
    rw [← commutator_isPPerfect_idempotent T N hT
      (hQ.to_le (commutatorPreimage_le Q T D)) hTN]
    exact (commutator_mono hNT le_rfl).trans hDT
  exact normalizes_pairing_of_fixed_mod_centralizer A Q Z T hZQ
    ((commutator_mono (le_commutatorPreimage hAQ hAT) le_rfl).trans hNZ)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {a d : Vertex R}

/-- Fixation in the original moving section is sufficient for the actual
rank-one residual to normalize the moving-neighbor commutator. -/
theorem moving_commutator_normalized_of_radical_fixed
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (ha : color R a = false) (hd : d ∈ movingNeighbors geometry a)
    (o : MovingOrientationAt a) (flag : SL)
    (hfix : ⁅(Z R d).subgroupOf (stabilizer R a), lineResidual o flag⁆ ≤
      radicalPreimage ((Q R a).subgroupOf (stabilizer R a))
        ((V R a).subgroupOf (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a))) :
    lineResidual o flag ≤ normalizer
      ((⁅Z R d, Q R a⁆).subgroupOf (stabilizer R a) : Set (stabilizer R a)) := by
  let := finite_stabilizer R a
  let := Q_normal R a
  let := o.natural_section.normal_kernel
  let := o.natural_section.radical_normal
  let S := stabilizer R a
  let Q₀ := (Q R a).subgroupOf S
  let Z₀ := (Z R a).subgroupOf S
  let V₀ := (V R a).subgroupOf S
  let D₀ := radicalPreimage Q₀ V₀ Z₀
  let T := lineResidual o flag
  have hTL : T ≤ pResidual 2 S := lineResidual_le_localResidual source ha o flag
  have hDZ : ⁅D₀, T⁆ ≤ Z₀ := by
    have hpre : D₀ ≤ commutatorPreimage ⊤ T Z₀ :=
      sup_le (le_commutatorPreimage le_top (commutator_le_left _ _))
        (le_commutatorPreimage le_top
          ((commutator_mono le_rfl hTL).trans o.natural_section.triple_le))
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ T Z₀ le_normalizer_of_normal)
  have hZdQ : Z R d ≤ Q R a := (moving_Z_le_V hd).trans (geometry.V_le_Q hb a ha)
  have hQG : Q R a ≤ S := fun _ hx => hx.1
  have heq : (⁅Z R d, Q R a⁆).subgroupOf S =
      ⁅(Z R d).subgroupOf S, Q₀⁆ := by
    apply map_injective S.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (hZdQ.trans hQG),
      map_subgroupOf_eq_of_le hQG,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans
        (sup_le (hZdQ.trans hQG) hQG))]
  rw [heq]
  apply pairing_normalized_of_radical_fixed _ Q₀ D₀ Z₀ T
    (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
    (lineResidual_isPPerfect source ha o flag) (fun _ hx => hZdQ hx) hfix hDZ
  intro z hz q hq
  apply Subtype.ext
  exact commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha) hz q hq

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne
