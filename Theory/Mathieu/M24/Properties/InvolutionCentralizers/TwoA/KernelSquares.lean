module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelSquareCosets
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.DisplacementConjugation
public import Theory.Representation.SL3.NaturalDualElementaryLift

/-!
# Squares of the actual Mathieu two-central kernel are central

The square of a kernel element lies in the octad translations. Modulo the
marked line it is fixed by the stabilizer of that element's nonzero dual
displacement. The genuine full quotient action supplies every such actor,
and the proved natural/dual stabilizer theorem forces the square onto the
marked line.
-/

public noncomputable section
open Subgroup Representation
open Sporadic.Mathieu.M24ChapterHStabilizers
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
private abbrev mark : centralizer2A := ⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩
private abbrev zA : translationKernel := ⟨mark,markedElement_mem_core⟩
private abbrev line := Theory.LinearAlgebra.BinaryFivePointStabilizer.line markedVector
private abbrev KD := Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacement (E := OctadAction.Space)

private def qv : translationKernel→*Multiplicative QuotientSpace :=
  line.mkQ.toAddMonoidHom.toMultiplicative.comp translationCoordinates.toMonoidHom

private theorem qv_zA : qv zA=1 := by
  change line.mkQ markedVector=0
  exact (Submodule.Quotient.mk_eq_zero line).mpr (Submodule.mem_span_singleton_self _)

private theorem qv_eq_one_iff (u : translationKernel) :
    qv u=1 ↔ u.val∈zpowers mark := by
  constructor
  · intro hu
    have hline : (translationCoordinates u).toAdd∈line :=
      (Submodule.Quotient.mk_eq_zero line).mp hu
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hline
    rcases (by decide : ∀c:ZMod 2,c=0∨c=1) c with rfl | rfl
    · have he : u=1 := translationCoordinates.injective (by
        rw [map_one]
        apply Multiplicative.toAdd.injective
        change (translationCoordinates u).toAdd=0
        simpa only [zero_smul] using hc.symm)
      rw [he]
      exact one_mem _
    · have he : u=zA := translationCoordinates.injective (by
        apply Multiplicative.toAdd.injective
        change (translationCoordinates u).toAdd=markedVector
        simpa only [one_smul] using hc.symm)
      rw [he]
      exact mem_zpowers _
  · intro hu
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hu
    have he : u=zA^n := Subtype.ext hn.symm
    rw [he,map_zpow,qv_zA,one_zpow]

private theorem qv_conjugation (g : centralizer2A) (u : translationKernel) :
    (qv (MulAut.conjNormal g u)).toAdd=quotientAction g (qv u).toAdd := by
  change line.mkQ (translationCoordinates (MulAut.conjNormal g u)).toAdd=
    Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction markedVector (pointAction g)
      (line.mkQ (translationCoordinates u).toAdd)
  rw [translationCoordinates_conjugation,
    Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction_mk]
  rfl

private def lineCoordinates : line≃ₗ[ZMod 2]ZMod 2 :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_span_singleton markedVector_ne_zero,Module.finrank_self])

private def covector (d : Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel markedVector) :
    Module.Dual (ZMod 2) (Fin 3→ZMod 2) :=
  lineCoordinates.toLinearMap.comp ((KD markedVector d).comp quotientCoordinates.symm.toLinearMap)

private theorem covector_ne_zero (d : Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel markedVector)
    (hd : d≠1) : covector d≠0 := by
  intro hf
  apply hd
  apply (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv markedVector).injective
  rw [map_one,Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv_apply]
  apply Multiplicative.toAdd.injective
  change KD markedVector d=0
  apply LinearMap.ext
  intro x
  apply lineCoordinates.injective
  have hh := LinearMap.congr_fun hf (quotientCoordinates x)
  change lineCoordinates (KD markedVector d (quotientCoordinates.symm (quotientCoordinates x)))=0 at hh
  simpa only [LinearEquiv.symm_apply_apply,LinearMap.zero_apply,map_zero] using hh

public theorem kernel_squares_mem_marked (q : kernel) :
    (q.val)^2∈zpowers (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A) := by
  have hq : pointAction q.val∈Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel markedVector :=
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff markedVector _).mpr q.property.2
  let d : Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel markedVector := ⟨pointAction q.val,hq⟩
  let sq : translationKernel := ⟨(q.val)^2,kernel_square_mem_translation q⟩
  apply (qv_eq_one_iff sq).mp
  apply Multiplicative.toAdd.injective
  change (qv sq).toAdd=0
  by_cases hd : d=1
  · have hqa : q.val∈translationKernel := by
      rw [←pointAction_ker,MonoidHom.mem_ker]
      exact congrArg Subtype.val hd
    have hs : (q.val)^2=1 := by
      have hh : (⟨q.val,hqa⟩:translationKernel)^2=1 := by
        apply translationCoordinates.injective
        rw [map_pow,map_one,pow_two]
        apply Multiplicative.toAdd.injective
        change (translationCoordinates ⟨q.val,hqa⟩).toAdd+
          (translationCoordinates ⟨q.val,hqa⟩).toAdd=0
        rw [←two_smul (ZMod 2),show (2:ZMod 2)=0 from rfl,zero_smul]
      exact congrArg Subtype.val hh
    have he : sq=1 := Subtype.ext hs
    rw [he,map_one]
    rfl
  have hv : quotientCoordinates (qv sq).toAdd=0 := by
    apply SL3ParabolicNatural.dual_stabilizer_fixed_zero (covector d) (covector_ne_zero d hd)
    intro g hg
    let b : QuotientSpace≃ₗ[ZMod 2]QuotientSpace :=
      (quotientCoordinates.trans (Matrix.SpecialLinearGroup.toLin' g)).trans quotientCoordinates.symm
    obtain ⟨c,hc⟩ := quotientAction_surjective b
    have hdisp (x : QuotientSpace) :
        KD markedVector d ((Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction
          markedVector (pointAction c))⁻¹ x)=KD markedVector d x := by
      apply lineCoordinates.injective
      have hh := LinearMap.congr_fun hg (quotientCoordinates x)
      change covector d (specialLinearNatural 3 g⁻¹ (quotientCoordinates x))=
        covector d (quotientCoordinates x) at hh
      change lineCoordinates (KD markedVector d ((quotientAction c)⁻¹ x))=
        lineCoordinates (KD markedVector d x)
      rw [hc]
      have hb : b⁻¹ x=quotientCoordinates.symm
          (specialLinearNatural 3 g⁻¹ (quotientCoordinates x)) := by
        change quotientCoordinates.symm
          ((Matrix.SpecialLinearGroup.toLin' g)⁻¹ (quotientCoordinates x))=_
        rw [←map_inv]
        rfl
      rw [hb]
      simpa only [covector,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using hh
    have hdc := Theory.LinearAlgebra.BinaryFivePointStabilizer.conjNormal_eq_self_of_displacement_fixed
      markedVector (pointAction c) d hdisp
    have hactor : pointAction (c*q.val*c⁻¹)=pointAction q.val := by
      have hh := congrArg Subtype.val hdc
      change pointAction c*pointAction q.val*(pointAction c)⁻¹=pointAction q.val at hh
      simpa only [map_mul,map_inv] using hh
    have hs := kernel_square_actor_stabilizer q c hactor
    let r : translationKernel := MulAut.conjNormal c sq*sq⁻¹
    have hr : qv r=1 := (qv_eq_one_iff r).mpr hs
    have he : qv (MulAut.conjNormal c sq)=qv sq := by
      change qv (MulAut.conjNormal c sq*sq⁻¹)=1 at hr
      rw [map_mul,map_inv,mul_inv_eq_one] at hr
      exact hr
    have hfix := qv_conjugation c sq
    rw [he,hc] at hfix
    have hcoord := congrArg quotientCoordinates hfix
    change quotientCoordinates (qv sq).toAdd=
      quotientCoordinates (quotientCoordinates.symm
        ((Matrix.SpecialLinearGroup.toLin' g) (quotientCoordinates (qv sq).toAdd))) at hcoord
    rw [LinearEquiv.apply_symm_apply] at hcoord
    exact hcoord.symm
  exact quotientCoordinates.injective (hv.trans quotientCoordinates.map_zero.symm)

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
