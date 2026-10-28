module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.Geometry

/-!
# Coordinates on the original core modulo its center

The factorization Q_H = U_H Z(Q_H) identifies the two central quotients.
Transporting the established quaternion square coordinates gives a surjective
map from Q_H to the binary plus space with kernel exactly Z(Q_H). Conjugation
by H agrees with its original starred wreath action. These are the coordinates
used to bound elementary subgroups in the Thompson argument.

Source: Aschbacher–Smith, Proposition 13.5.16, printed p.921.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
  (b : CFSG.Quasithin.Chapter13.Section05.NormalBranch.Conclusions D M 6 g)
include d h e hseed hn hU b

theorem core_central_factorization (x : D.QH) :
    ∃ u : D.UH, ∃ z : center D.QH, inclusion h.UH_le_QH u * z = x := by
  let Z := (center D.QH).map D.QH.subtype
  have hf : D.QH = D.UH ⊔ Z := by
    dsimp only [Z]
    rw [core_center_image d h e hseed hn hU b]
    exact SourceQuaternionCentralizer.core_eq_closure_sup_local_centralizer d h e hseed hn hU
  have hc : Z ≤ centralizer (D.UH : Set G) := by
    rintro z ⟨z,hz,rfl⟩ u hu
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨u,h.UH_le_QH hu⟩)
  have hx : (x : G) ∈ (D.UH : Set G) * (Z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left D.UH Z
      (hc.trans (Subgroup.centralizer_le_normalizer _)), ← hf]
    exact x.property
  obtain ⟨u,hu,z,⟨z,hz,rfl⟩,hh⟩ := hx
  exact ⟨⟨u,hu⟩,⟨z,hz⟩,Subtype.ext hh⟩

private def closureCoreProjection : D.UH →* (D.QH ⧸ center D.QH) :=
  (QuotientGroup.mk' (center D.QH)).comp (inclusion h.UH_le_QH)

private theorem closureCoreProjection_surjective :
    Function.Surjective (closureCoreProjection h) := by
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center D.QH) v
  obtain ⟨u,z,hz⟩ := core_central_factorization d h e hseed hn hU b x
  refine ⟨u, ?_⟩
  have hz0 : QuotientGroup.mk' (center D.QH) (z : D.QH) = 1 :=
    (QuotientGroup.eq_one_iff (z : D.QH)).mpr z.property
  rw [← hz, map_mul, hz0, mul_one]
  rfl

private theorem closureCoreProjection_ker :
    (closureCoreProjection h).ker = center D.UH := by
  ext u
  change QuotientGroup.mk' (center D.QH) (inclusion h.UH_le_QH u) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hu
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    exact congrArg (fun y : D.QH => (y : G))
      (mem_center_iff.mp hu (inclusion h.UH_le_QH v))
  · intro hu
    apply mem_center_iff.mpr
    intro x
    obtain ⟨v,z,rfl⟩ := core_central_factorization d h e hseed hn hU b x
    have huv : Commute (inclusion h.UH_le_QH v) (inclusion h.UH_le_QH u) :=
      (show Commute v u from mem_center_iff.mp hu v).map (inclusion h.UH_le_QH)
    have hzu : Commute (z : D.QH) (inclusion h.UH_le_QH u) :=
      (show Commute (inclusion h.UH_le_QH u) (z : D.QH) from
        mem_center_iff.mp z.property _).symm
    exact (huv.mul_left hzu).eq

private noncomputable def closureCoreEquiv :
    (D.UH ⧸ center D.UH) ≃* (D.QH ⧸ center D.QH) :=
  QuotientGroup.liftEquiv (center D.UH)
    (closureCoreProjection_surjective d h e hseed hn hU b)
    (closureCoreProjection_ker d h e hseed hn hU b).symm

noncomputable def coreQuotientCoordinates :
    (D.QH ⧸ center D.QH) ≃* Multiplicative BinaryFourPlus.V :=
  (closureCoreEquiv d h e hseed hn hU b).symm.trans
    (SourceOrthogonal.quaternion d h e hseed hn hU).squareCoordinates.toAddEquiv.toMultiplicativeRight

noncomputable def coreCoordinates : D.QH →* Multiplicative BinaryFourPlus.V :=
  (coreQuotientCoordinates d h e hseed hn hU b).toMonoidHom.comp
    (QuotientGroup.mk' (center D.QH))

theorem coreCoordinates_surjective :
    Function.Surjective (coreCoordinates d h e hseed hn hU b) :=
  (coreQuotientCoordinates d h e hseed hn hU b).surjective.comp
    (QuotientGroup.mk'_surjective _)

theorem coreCoordinates_ker :
    (coreCoordinates d h e hseed hn hU b).ker = center D.QH := by
  ext x
  change coreQuotientCoordinates d h e hseed hn hU b
    (QuotientGroup.mk' (center D.QH) x) = 1 ↔ _
  rw [map_eq_one_iff _ (coreQuotientCoordinates d h e hseed hn hU b).injective,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem coreCoordinates_inclusion (u : D.UH) :
    coreCoordinates d h e hseed hn hU b (inclusion h.UH_le_QH u) =
      Multiplicative.ofAdd ((SourceOrthogonal.quaternion d h e hseed hn hU).squareCoordinates
        (Additive.ofMul (QuotientGroup.mk' (center D.UH) u))) := by
  change (SourceOrthogonal.quaternion d h e hseed hn hU).squareCoordinates.toAddEquiv.toMultiplicativeRight
    ((closureCoreEquiv d h e hseed hn hU b).symm
      (closureCoreEquiv d h e hseed hn hU b (QuotientGroup.mk' (center D.UH) u))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem coreCoordinates_conj (x : D.H) (v : D.QH) :
    (coreCoordinates d h e hseed hn hU b
      (seedConjugation D.H D.QH (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)) x v)).toAdd =
      (BinaryFourPlus.wreathToIsometry
        (SourceOrthogonal.starEmbedding d h e hseed hn hU
          (QuotientGroup.mk' (pCore 2 D.H) x))).val
        (coreCoordinates d h e hseed hn hU b v).toAdd := by
  let α := seedConjugation D.H D.QH (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)) x
  let β := seedConjugation D.H D.UH
    (le_normalizer_conjugateSpanBy D.Vplus D.H) x
  let c := coreCoordinates d h e hseed hn hU b
  have hz (z : center D.QH) : c z = 1 := by
    apply (coreCoordinates_ker d h e hseed hn hU b).ge
    exact z.property
  have haz (z : center D.QH) : c (α z) = 1 := by
    exact hz (centerCongr α z)
  obtain ⟨u,z,rfl⟩ := core_central_factorization d h e hseed hn hU b v
  change (c (α (inclusion h.UH_le_QH u * z))).toAdd = _
  rw [map_mul, map_mul, haz, mul_one]
  change _ = (BinaryFourPlus.wreathToIsometry
    (SourceOrthogonal.starEmbedding d h e hseed hn hU
      (QuotientGroup.mk' (pCore 2 D.H) x))).val
      (c (inclusion h.UH_le_QH u * z)).toAdd
  rw [map_mul, hz, mul_one]
  change (c (inclusion h.UH_le_QH (β u))).toAdd = _
  rw [coreCoordinates_inclusion, coreCoordinates_inclusion]
  have hh := (SourceOrthogonal.quaternion d h e hseed hn hU).square_action_intertwines
    β (QuotientGroup.mk' (center D.UH) u)
  rw [quotientAut_apply_mk] at hh
  exact hh.symm

theorem core_central_quotient_card : Nat.card (D.QH ⧸ center D.QH) = 16 := by
  have hQ : D.LT.pCoreIn 2 = D.V := by
    rw [← b.seven.1]
    exact b.seven.2.symm
  have hp := SourcePointCoreGeometry.point_core_central_quotient_card
    d h e hseed hn hU hQ
  rw [← b.six.1] at hp
  exact hp

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
