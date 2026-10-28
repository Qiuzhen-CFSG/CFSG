module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Matching.Quotient
public import Theory.Representation.AlternatingSevenFiveRestriction.PlaneQuotient
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.FieldAction
/-!
# Excluding a natural L₂(4) block inside an ordinary A₇ block

The literal inclusion and two-core kernel identify the smaller quotient with
its actual A₅ image. A full Sylow normalizer forces the five-letter embedding.
The vanishing fixed layer of the ordinary A₇ block identifies its full U with
the six-dimensional core. Its embedded five-point core survives in the natural
plane quotient of U(K), contradicting the cubic fixed-vector calculation.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation Matrix
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
open ExceptionalRestrictions
variable {K L : Type*} [Group K] [Group L] [Finite K] [Finite L]
theorem no_natural_two_in_alternating_seven
    (hK : IsL2EvenBlock K 2) (hL : IsAlternatingBlock L 7)
    (f : K →* L) (hf : Function.Injective f)
    (hU : (blockU K).map f ≤ blockU L)
    (hk : ((QuotientGroup.mk' (pCore 2 L)).comp f).ker = pCore 2 K)
    (P : Sylow 2 L) (hP : (P : Subgroup L) ≤ normalizer (f.range : Set L)) : False := by
  classical
  let := hK.2.1.elementary
  let := hL.2.1.elementary
  obtain ⟨F,_,_,hF,_,rK,⟨mK⟩,hmK⟩ := hK.2.2
  have hF4 : Nat.card F = 4 := by simpa using hF
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨rL,⟨mL⟩,hmL⟩ := hL.2.2
  let qK := QuotientGroup.mk' (pCore 2 K)
  let qL := QuotientGroup.mk' (pCore 2 L)
  let aL := mL.quotientIso.toMonoidHom.comp qL
  let a := aL.comp f
  let B := a.range
  have hka : a.ker = pCore 2 K := by
    ext k
    change mL.quotientIso (qL (f k)) = 1 ↔ k ∈ pCore 2 K
    rw [map_eq_one_iff _ mL.quotientIso.injective]
    exact show qL (f k) = 1 ↔ k ∈ pCore 2 K from by rw [← hk]; rfl
  let eKB : (K ⧸ pCore 2 K) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hka.symm).trans (QuotientGroup.quotientKerEquivRange a)
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
  let eK5 := mK.quotientIso.trans ((BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).trans e5)
  let S := P.mapSurjective (f := aL) (mL.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _))
  have hSB : (S : Subgroup _) ≤ normalizer (B : Set (alternatingGroup (Fin 7))) := by
    change (P : Subgroup L).map aL ≤ _
    have hh := (map_mono (f := aL) hP).trans (le_normalizer_map _)
    change (P : Subgroup L).map aL ≤ normalizer ((aL.comp f).range : Set (alternatingGroup (Fin 7)))
    rw [MonoidHom.range_comp]
    exact hh
  obtain ⟨eB,j,hj,hjact⟩ := BinaryPermutation.exists_five_core_embedding B (eKB.symm.trans eK5) S hSB
  let dK := eKB.trans eB
  let ρ := (BinaryPermutation.coreRepresentation (Fin 7)).comp
    ((alternatingGroup (Fin 7)).subtype.comp (B.subtype.comp eB.symm.toMonoidHom))
  let σ := (uRepresentation hK.2.1).comp dK.symm.toMonoidHom
  let pL : blockU L →* Multiplicative (BinaryPermutation.natural (Fin 7)) :=
    mL.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed L))
  have hpL : Function.Bijective pL := by
    refine ⟨?_,mL.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    apply pL.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro u hu
    have he : QuotientGroup.mk' (blockFixed L) u = 1 :=
      mL.moduleIso.injective (hu.trans mL.moduleIso.map_one.symm)
    have huf := (QuotientGroup.eq_one_iff _).mp he
    rwa [hL.seven_fixed_eq_bot] at huf
  let epL := MulEquiv.ofBijective pL hpL
  let E : Additive (blockU L) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7) :=
    { epL.toAdditiveLeft with map_smul' := fun c v => ZMod.map_smul epL.toAdditiveLeft c v }
  let c := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  let EL := E.trans c.symm
  have hE (l : L) (v : Additive (blockU L)) :
      E (uRepresentation hL.2.1 (qL l) v) =
        BinaryPermutation.naturalRepresentation (Fin 7) (aL l).val (E v) := by
    change (pL (blockConjugate L l v.toMul)).toAdd = _
    change (mL.moduleIso (QuotientGroup.mk' _ (blockConjugate L l v.toMul))).toAdd = _
    rw [mL.intertwining]
    exact hmL _ _
  have hEL (l : L) (v : Additive (blockU L)) :
      EL (uRepresentation hL.2.1 (qL l) v) =
        BinaryPermutation.coreRepresentation (Fin 7) (aL l).val (EL v) := by
    apply c.injective
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    change c (c.symm (E _)) = BinaryPermutation.naturalRepresentation (Fin 7) (aL l).val (c (c.symm (E v)))
    rw [c.apply_symm_apply,c.apply_symm_apply,hE]
  let fU : blockU K →* blockU L :=
    (f.comp (blockU K).subtype).codRestrict _ (fun u => hU ⟨u,u.property,rfl⟩)
  have hfU : Function.Injective fU := fun _ _ he => Subtype.ext (hf (congrArg Subtype.val he))
  let i := EL.toLinearMap.comp (fU.toAdditive.toZModLinearMap 2)
  have hi : Function.Injective i := EL.injective.comp hfU
  have hiact (b : alternatingGroup (Fin 5)) (v : Additive (blockU K)) : i (σ b v) = ρ b (i v) := by
    obtain ⟨a0,rfl⟩ := dK.surjective b
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a0
    have hb : eB.symm (dK (qK k)) = a.rangeRestrict k := by
      change eB.symm (eB (eKB (qK k))) = _
      exact eB.symm_apply_apply _
    change EL (fU.toAdditive (uRepresentation hK.2.1 (dK.symm (dK (qK k))) v)) = _
    rw [dK.symm_apply_apply]
    change EL (fU.toAdditive (uRepresentation hK.2.1 (qK k) v)) =
      BinaryPermutation.coreRepresentation (Fin 7) (eB.symm (dK (qK k))).val.val (i v)
    rw [hb]
    have he : fU.toAdditive (uRepresentation hK.2.1 (qK k) v) =
        uRepresentation hL.2.1 (qL (f k)) (fU.toAdditive v) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change f ((uRepresentation hK.2.1 (qK k) v).toMul : K) = _
      rw [uRepresentation_apply,uRepresentation_apply]
      simp only [map_mul,map_inv]
      rfl
    rw [he,hEL]
    rfl
  let f5 := mK.quotientIso.toMonoidHom.comp dK.symm.toMonoidHom
  let kU : Additive (blockU K) →ₗ[ZMod 2] (Fin 2 → F) :=
    (mK.moduleIso.toAdditiveLeft.toAddMonoidHom.comp (QuotientGroup.mk' (blockFixed K)).toAdditive).toZModLinearMap 2
  have hkU : Function.Surjective kU := by
    intro v
    obtain ⟨w,hw⟩ := mK.moduleIso.surjective (Multiplicative.ofAdd v)
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (blockFixed K) w
    exact ⟨Additive.ofMul u,congrArg Multiplicative.toAdd hw⟩
  have hkact (b : alternatingGroup (Fin 5)) (v : Additive (blockU K)) :
      kU (σ b v) = (f5 b).val *ᵥ kU v := by
    obtain ⟨a0,rfl⟩ := dK.surjective b
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a0
    change kU (uRepresentation hK.2.1 (dK.symm (dK (qK k))) v) = _
    rw [dK.symm_apply_apply]
    change (mK.moduleIso (QuotientGroup.mk' _ (blockConjugate K k v.toMul))).toAdd = _
    rw [mK.intertwining,hmK]
    change (mK.quotientIso (qK k)).val *ᵥ _ =
      (mK.quotientIso (dK.symm (dK (qK k)))).val *ᵥ _
    rw [dK.symm_apply_apply]
    rfl
  exact BinaryPermutation.SevenPointChiefFactor.no_natural_plane_quotient hF4 ρ σ j hj
    (fun b v => by
      change j (BinaryPermutation.coreRepresentation (Fin 5) b.val v) =
        BinaryPermutation.coreRepresentation (Fin 7) (eB.symm b).val.val (j v)
      simpa only [eB.apply_symm_apply] using hjact (eB.symm b) v)
    (by simpa using BinaryPermutation.finrank_core (Fin 7)) i hi hiact f5
    (mK.quotientIso.injective.comp dK.symm.injective) kU hkU hkact
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
