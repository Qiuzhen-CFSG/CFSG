module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.Concrete
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.IntrinsicFactors

/-!
# Individual invariance of the intrinsic cubic factors

A non-swapping isometry conjugates an independent plane rotation with nonzero
fixed space to itself or its inverse. Faithful coordinates transport this
calculation to every actor subgroup with a nonzero fixed vector. In particular
it fixes each of the two intrinsic factors of the nine-on-sixteen action.

Source: Aschbacher--Smith, 15.4.12(6)(ii), printed pp.1160--1161, and the
Baumann preservation of the two factors in 15.3.67, printed p.1153.
-/

@[expose] public section

open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
set_option synthInstance.maxSize 10000

private def rotationEval (r : RotationCode) (v : Space) : Space :=
  (planeEval (⟨r.toAdd.1.val, ZMod.val_lt _⟩,0) v.1,
   planeEval (⟨r.toAdd.2.val, ZMod.val_lt _⟩,0) v.2)

private theorem rotation_eval : ∀ r : RotationCode, ∀ v : Space,
    rotation r v = rotationEval r v := by decide +kernel

set_option maxRecDepth 10000 in
private theorem noninterchanging_rotation_conjugation :
    ∀ k : Code, k.2.2 = false → ∀ r : RotationCode,
      (∃ v : Space, v ≠ 0 ∧ rotationEval r v = v) → ∀ t : RotationCode,
      (∀ v : Space, eval k (rotationEval r v) = rotationEval t (eval k v)) →
      t = r ∨ t = r⁻¹ := by decide +kernel

/-- An isometry preserving the two definite planes fixes every actor subgroup
having a nonidentity fixed vector in the faithful rotation representation. -/
theorem subgroup_map_eq_of_noninterchanging_coordinates
    {A W : Type*} [Group A] [Group W] [Finite A]
    (ρ : A →* MulAut W) (hfaith : Function.Injective ρ)
    (c : W ≃* ModelSpace)
    (hc : ρ.range.map (MulAut.congr c).toMonoidHom = modelRotations)
    (f : MulAut A) (e : MulAut W)
    (he : ∀ a w, e (ρ a w) = ρ (f a) (e w))
    (g : OrthogonalFourBinary.IsometryGroup)
    (hg : ∀ w, c (e w) = vectorAction g (c w))
    (hbase : (codeEquiv.symm g).2.2 = false)
    (K : Subgroup A)
    (hfixed : ∃ w : W, w ≠ 1 ∧ ∀ a ∈ K, ρ a w = w) :
    K.map f.toMonoidHom = K := by
  obtain ⟨w,hw,hfix⟩ := hfixed
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  rw [show codeEquiv.symm (codeMap k) = k from codeEquiv.symm_apply_apply k] at hbase
  have hrot (a : A) : ∃ r : RotationCode, rotationAction r = MulAut.congr c (ρ a) := by
    have hm : MulAut.congr c (ρ a) ∈ modelRotations := by
      rw [← hc]
      exact mem_map.mpr ⟨ρ a,⟨a,rfl⟩,rfl⟩
    exact hm
  have hcinj : Function.Injective (fun a : A => MulAut.congr c (ρ a)) :=
    (MulAut.congr c).injective.comp hfaith
  have hmov (a : A) (ha : a ∈ K) : f a = a ∨ f a = a⁻¹ := by
    obtain ⟨r,hr⟩ := hrot a
    obtain ⟨t,ht⟩ := hrot (f a)
    have hfixedr : ∃ v : Space, v ≠ 0 ∧ rotationEval r v = v := by
      refine ⟨(c w).toAdd, ?_, ?_⟩
      · intro hv
        apply hw
        apply c.injective
        exact hv.trans (map_one c).symm
      · rw [← rotation_eval]
        change rotationAction r (c w) = c w
        rw [hr]
        change c (ρ a (c.symm (c w))) = c w
        rw [c.symm_apply_apply,hfix a ha]
    have hinter : ∀ v : Space, eval k (rotationEval r v) = rotationEval t (eval k v) := by
      intro v
      have hh := congrArg c (he a (c.symm (Multiplicative.ofAdd v)))
      rw [hg] at hh
      have hrval (u : ModelSpace) : c (ρ a (c.symm u)) = rotationAction r u :=
        (DFunLike.congr_fun hr u).symm
      have htval (u : ModelSpace) : c (ρ (f a) (c.symm u)) = rotationAction t u :=
        (DFunLike.congr_fun ht u).symm
      have hev : e (c.symm (Multiplicative.ofAdd v)) =
          c.symm (vectorAction (codeMap k) (Multiplicative.ofAdd v)) := by
        apply c.injective
        rw [hg,c.apply_symm_apply,c.apply_symm_apply]
      rw [hev,hrval,htval] at hh
      change candidate k (rotation r v) = rotation t (candidate k v) at hh
      simpa only [candidate_eval,rotation_eval] using hh
    rcases noninterchanging_rotation_conjugation k hbase r hfixedr t hinter with hh | hh
    · left
      apply hcinj
      change MulAut.congr c (ρ (f a)) = MulAut.congr c (ρ a)
      rw [←hr,←ht,hh]
    · right
      apply hcinj
      change MulAut.congr c (ρ (f a)) = MulAut.congr c (ρ a⁻¹)
      rw [map_inv,map_inv,←hr,←ht,hh,map_inv]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a,ha,rfl⟩
    change f a ∈ K
    rcases hmov a ha with hh | hh
    · rw [hh]
      exact ha
    · rw [hh]
      exact K.inv_mem ha
  · rw [card_map_of_injective f.injective]

/-- A compatible isometry which does not interchange the definite planes fixes
each member of the intrinsic pair on the original actor, in its original action. -/
theorem factorPair_map_eq_of_noninterchanging_coordinates
    {A W : Type*} [Group A] [Group W] [Finite A] [Finite W]
    (ρ : A →* MulAut W) (hfaith : Function.Injective ρ)
    (c : W ≃* ModelSpace)
    (hc : ρ.range.map (MulAut.congr c).toMonoidHom = modelRotations)
    (f : MulAut A) (e : MulAut W)
    (he : ∀ a w, e (ρ a w) = ρ (f a) (e w))
    (g : OrthogonalFourBinary.IsometryGroup)
    (hg : ∀ w, c (e w) = vectorAction g (c w))
    (hbase : (codeEquiv.symm g).2.2 = false) :
    letI := MulDistribMulAction.compHom W ρ
    ∀ (P : FactorPair (A := A) (W := W)) i,
      (P.line i).map f.toMonoidHom = P.line i := by
  let _ := MulDistribMulAction.compHom W ρ
  intro P i
  apply subgroup_map_eq_of_noninterchanging_coordinates ρ hfaith c hc f e he g hg hbase
  have hne : FixedPoints.subgroup (P.line i) W ≠ ⊥ := by
    intro hh
    have hcard := P.fixed_card i
    rw [hh,card_bot] at hcard
    omega
  obtain ⟨w,hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨w, (fun hh => hw (Subtype.ext hh)), ?_⟩
  intro a ha
  exact w.property ⟨a,ha⟩

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
