module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverBounds
/-!
# Marked coordinates for the two extremal natural covers

Transport the original U/C_U(L) model to the same SL₂ field. A trivial
central kernel identifies U with the natural plane. A kernel of full
field order attains the binary H¹ bound, so the universal-cover comparison
identifies U with the orthogonal three-space, equivariantly under the
original quotient map. The center itself is the additive field.
Source: Aschbacher–Smith, I.1.6 and Lemma 2.4.8(4), printed pp.408, 530.
-/
public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L F : Type*} [Group L] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable (h : IsShort L)
variable [Finite L] [IsElementaryAbelian 2 (blockU L)] [IsElementaryAbelian 2 (BlockModule L)]
include h
variable {r : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F))}
variable (m : BlockModuleModel L r)
variable (hm : ∀ g v, (r g v).toAdd = specialLinearNatural 2 g v.toAdd)

abbrev modelCoverAction : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) (Additive (blockU L)) := (uRepresentation h).comp m.quotientIso.symm.toMonoidHom

def modelModuleCoordinates : Additive (BlockModule L) ≃ₗ[ZMod 2] (Fin 2 → F) :=
  { m.moduleIso.toAdditiveLeft with map_smul' := fun a v => ZMod.map_smul m.moduleIso.toAdditiveLeft a v }

def modelCoverMap : Additive (blockU L) →ₗ[ZMod 2] (Fin 2 → F) :=
  (modelModuleCoordinates m).toLinearMap.comp moduleProjection

omit [Finite F] [CharP F 2] [Finite L] in
include hm in
lemma modelCoverMap_intertwining (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Additive (blockU L)) :
    modelCoverMap m (modelCoverAction h m g v) =
      SL2OrthogonalCover.binaryNatural g (modelCoverMap m v) := by
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (m.quotientIso.symm g)
  have hq : m.quotientIso (QuotientGroup.mk' (pCore 2 L) l) = g := by rw [hl,m.quotientIso.apply_symm_apply]
  change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _
    ((uRepresentation h (m.quotientIso.symm g) v).toMul))) = _
  rw [←hl]
  change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _ (blockConjugate L l v.toMul))) = _
  rw [m.intertwining,hm,hq]
  rfl

def modelCoverProjection : (modelCoverAction h m).IntertwiningMap (SL2OrthogonalCover.binaryNatural (F := F)) :=
  (modelCoverMap m).intertwiningMap_of_isIntertwiningMap _ _ (modelCoverMap_intertwining h m hm)

omit [Finite F] [CharP F 2] h [Finite L] in
lemma modelCoverMap_surjective : Function.Surjective (modelCoverMap m) :=
  (modelModuleCoordinates m).surjective.comp moduleProjection_surjective

omit [Finite F] [CharP F 2] h [Finite L] in
lemma modelCoverMap_ker (v : Additive (blockU L)) :
    v ∈ (modelCoverMap m).ker ↔ v.toMul ∈ blockFixed L := by
  change m.moduleIso (QuotientGroup.mk' (blockFixed L) v.toMul) = 1 ↔ _
  rw [m.moduleIso.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff _

omit [Finite F] [CharP F 2] [Finite L] in
lemma modelCoverProjection_isCover : IsCover (modelCoverProjection h m hm) := by
  refine ⟨modelCoverMap_surjective m, ?_, ?_⟩
  · intro v hv g
    exact (uRepresentation_fixed h v).mpr ((modelCoverMap_ker m v).mp hv) _
  · apply top_unique
    rw [←uRepresentation_moved h]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    have he : modelCoverAction h m (m.quotientIso g) v = uRepresentation h g v := by
      change uRepresentation h (m.quotientIso.symm (m.quotientIso g)) v = _
      rw [m.quotientIso.symm_apply_apply]
    change uRepresentation h g v - v ∈ Coinvariants.ker (modelCoverAction h m)
    rw [←he]
    exact Coinvariants.sub_mem_ker _ _

omit [Finite F] [CharP F 2] h [Finite L] in
lemma modelCoverMap_kernel_card : Nat.card (modelCoverMap m).ker = Nat.card (blockFixed L) := by
  let e : (modelCoverMap m).ker ≃ blockFixed L :=
    { toFun := fun v => ⟨v.val.toMul,(modelCoverMap_ker m v).mp v.property⟩
      invFun := fun v => ⟨Additive.ofMul v.val,(modelCoverMap_ker m _).mpr v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] [Finite L] [IsElementaryAbelian 2 (BlockModule L)] in
lemma modelCoverAction_apply (l : L) (v : Additive (blockU L)) :
    modelCoverAction h m (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) v =
      Additive.ofMul (blockConjugate L l v.toMul) := by
  change uRepresentation h (m.quotientIso.symm (m.quotientIso _)) v = _
  rw [m.quotientIso.symm_apply_apply]
  rfl

omit [Finite F] [CharP F 2] [Finite L] in
include hm in
lemma modelCover_natural_equiv (hz : blockFixed L = ⊥) :
    ∃ e : blockU L ≃* Multiplicative (Fin 2 → F),
      ∀ l u, (e (blockConjugate L l u)).toAdd =
        SL2OrthogonalCover.binaryNatural (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (e u).toAdd := by
  have hi : Function.Injective (modelCoverMap m) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hh := (modelCoverMap_ker m v).mp hv
    rw [hz] at hh
    exact hh
  let e := LinearEquiv.ofBijective (modelCoverMap m) ⟨hi,modelCoverMap_surjective m⟩
  refine ⟨e.toAddEquiv.toMultiplicativeRight,?_⟩
  intro l u
  have hh := modelCoverMap_intertwining h m hm (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (Additive.ofMul u)
  rw [modelCoverAction_apply] at hh
  exact hh

include hm in
lemma modelCover_orthogonal_equiv {n : ℕ} (hn : 1<n) (hF : Nat.card F = 2^n)
    (hz : Nat.card (blockFixed L) = 2^n) :
    ∃ e : blockU L ≃* Multiplicative (SL2OrthogonalCover.Space F),
      ∀ l u, (e (blockConjugate L l u)).toAdd =
        SL2OrthogonalCover.binaryAction (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (e u).toAdd := by
  have hd : Module.finrank (ZMod 2) (modelCoverMap m).ker = n := by
    apply Nat.pow_right_injective (by decide : 1<2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (modelCoverMap m).ker)
    rw [Nat.card_zmod,modelCoverMap_kernel_card m,hz] at hc
    exact hc.symm
  have hd' : Module.finrank (ZMod 2) (modelCoverProjection h m hm).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (SL2OrthogonalCover.binaryNatural (F:=F)).dual) := by
    rw [SL2OrthogonalCover.binary_dual_H1_finrank n hn hF]
    exact hd
  obtain ⟨a,ha,hpa⟩ := exists_equiv_universalCover_of_finrank_ker_eq
    (modelCoverProjection h m hm) (modelCoverProjection_isCover h m hm) hd'
  obtain ⟨b,hb,hpb⟩ := SL2OrthogonalCover.universal_equiv n hn hF
  let e := a.symm.trans b
  have he (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Additive (blockU L)) :
      e (modelCoverAction h m g v) = SL2OrthogonalCover.binaryAction g (e v) := by
    have hai : a.symm (modelCoverAction h m g v) =
        (universalAction (SL2OrthogonalCover.binaryNatural (F:=F)).dual).dual g (a.symm v) := by
      apply a.injective
      rw [a.apply_symm_apply,ha,a.apply_symm_apply]
    change b (a.symm (modelCoverAction h m g v)) = _
    rw [hai,hb]
    rfl
  refine ⟨e.toAddEquiv.toMultiplicativeRight,?_⟩
  intro l u
  have hh := he (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (Additive.ofMul u)
  rw [modelCoverAction_apply] at hh
  exact hh

omit [Finite F] [CharP F 2] [Finite L] h [IsElementaryAbelian 2 (blockU L)] [IsElementaryAbelian 2 (BlockModule L)] in
lemma center_equiv_additive_field {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hc : Nat.card (center L) = Nat.card F)
    [Finite F] : Nonempty (center L ≃* Multiplicative F) := by
  let := hL.2.1.finite
  let := hL.2.1.elementary
  let : IsElementaryAbelian 2 (center L) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun z =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z.val (hL.center_le_module hcore z.property))) }
  have hd : Module.finrank (ZMod 2) (Additive (center L)) = Module.finrank (ZMod 2) F := by
    apply Nat.pow_right_injective (by decide : 1<2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive (center L)) = Nat.card (Additive (center L)) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = Nat.card (center L) := Nat.card_congr Additive.toMul
      _ = Nat.card F := hc
      _ = 2 ^ Module.finrank (ZMod 2) F := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact ⟨(LinearEquiv.ofFinrankEq _ _ hd).toAddEquiv.toMultiplicativeRight⟩
end CFSG.Quasithin.ChapterC
