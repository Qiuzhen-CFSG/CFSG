module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CenterFourExclusion
public import Theory.Representation.SL3.DoubledAbelianTorus

/-!
# The whole center in the doubled central-omega branch

For the actual MS core Q, restrict the original component action to
Ω₂(Z(Q)). Its square map has kernel Ω₁(Z(Q)), with the supplied doubled
natural coordinates. The quotient kernel acts centrally on this whole
center, so the doubled torus obstruction kills every square in Ω₂(Z(Q)).
A finite two-group argument then kills every square in Z(Q).

Thus doubled natural central omega is the entire doubled natural center,
at the same full SL₃ marking, over every nonbinary field. Together with
the natural-center result, the field-four recognition with C_Q(K)=1 now
gives models of the whole center in both branches. Neither abelianity of
Q nor its upper or Frattini sections follows from this result; those
remain needed for the full C.1.34 alternatives.

NonblockDoubledCenter supplies the literal original source application.
Source: Aschbacher–Smith C.1.34, printed pp.136–137, and original 4.3.8–10,
pp.616–617. The proof uses the original center action, not a replacement group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.DoubledCenter
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "Q" => msQ K R
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
local notation "O" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn Q

include h hn in
/-- Doubled natural central omega forces the whole center to have exponent
two at every nonbinary degree, retaining the original quotient kernel. -/
theorem center_exponent_two
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    ∀ z : Z, z^2=1 := by
  let : IsMulCommutative Z := map_isMulCommutative (center Q) (Q).subtype
  let : IsElementaryAbelian 2 O := by
    change IsElementaryAbelian 2 (Subgroup.omegaCenterIn Q)
    infer_instance
  have hp : IsPGroup 2 Z := (isPGroup_pCoreIn 2 (K ⊔ R)).to_le
    ((map_subtype_le _).trans msQ_le_joinCore)
  have he : O = (omega₁ Z (p := 2)).map (Z).subtype :=
    Subgroup.omegaCenterIn_eq_omegaOneAmbient Q
  have hnZ := CentralSections.join_normalizes_center h hn
  let Y := (omega Z (p := 2) 2).map (Z).subtype
  have hYZ : Y ≤ Z := map_subtype_le _
  have hOY : O ≤ Y := by
    rw [he]
    apply map_mono
    intro x hx
    apply Subgroup.subset_closure
    have hx2 : x^2=1 := (OmegaAction.omega_eq_pow_ker (G := Z) 2 1).le hx
    change x^4=1
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,hx2,one_pow]
  have hfour : ∀ x ∈ Y, x^4=1 := by
    rintro x ⟨z,hz,rfl⟩
    exact congrArg (Z).subtype ((OmegaAction.omega_eq_pow_ker (G := Z) 2 2).le hz)
  let : (omega Z (p := 2) 2).Characteristic := omega_characteristic Z 2
  have hKY : K ≤ normalizer (Y : Set G) :=
    (le_sup_left : K ≤ K ⊔ R).trans (hnZ.trans
      (normalizer_le_normalizer_characteristic_image Z (omega Z (p := 2) 2)))
  let : IsMulCommutative Y := by dsimp [Y]; infer_instance
  let α : K →* MulAut Y := Y.normalizerMonoidHom.comp (inclusion hKY)
  let ρ : Representation ℤ K (Additive Y) := {
    toFun k := (α k).toMonoidHom.toAdditive.toIntLinearMap
    map_one' := by
      apply LinearMap.ext
      intro x
      change Additive.ofMul (α 1 x.toMul)=x
      rw [map_one]
      rfl
    map_mul' k l := by
      apply LinearMap.ext
      intro x
      change Additive.ofMul (α (k*l) x.toMul)=Additive.ofMul (α k (α l x.toMul))
      rw [map_mul,MulAut.mul_apply] }
  let sq : Y →* O := {
    toFun x := ⟨(x:G)^2,by
      rw [he]
      refine ⟨(⟨(x:G)^2,(Z).pow_mem (hYZ x.property) 2⟩ : Z),subset_closure ?_,rfl⟩
      apply Subtype.ext
      change ((x:G)^2)^2=1
      rw [←pow_mul]
      exact hfour x x.property⟩
    map_one' := Subtype.ext (one_pow 2)
    map_mul' x y := Subtype.ext (congrArg Y.subtype (mul_pow x y 2)) }
  have hsqker (x : Y) : sq x=1 ↔ (x:G) ∈ O := by
    constructor
    · intro hx
      rw [he]
      exact ⟨⟨x,hYZ x.property⟩,subset_closure (Subtype.ext (congrArg (O).subtype hx)),rfl⟩
    · intro hx
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ hx)
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKO,_,hi,b0,hb0⟩ := hm
  let := hi
  let b : O ≃* Multiplicative ((Fin 3 → F) × (Fin 3 → F)) := QuotientGroup.quotientBot.symm.trans b0
  let β : K →* MulAut O := (O).normalizerMonoidHom.comp (inclusion hKO)
  have hb (k : K) (v : O) : (b (β k v)).toAdd =
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))
        (linearThreeActor e k) (b v).toAdd :=
    hb0 k v (β k v) rfl
  have hsqα (k : K) (x : Y) : sq (α k x)=β k (sq x) := by
    apply Subtype.ext
    change ((k:G)*(x:G)*(k:G)⁻¹)^2=(k:G)*(x:G)^2*(k:G)⁻¹
    exact (map_pow (MulAut.conj (k:G)) (x:G) 2).symm
  let i : ((Fin 3 → F) × (Fin 3 → F)) →+ Additive Y := {
    toFun v := Additive.ofMul (inclusion hOY (b.symm (Multiplicative.ofAdd v)))
    map_zero' := by
      change Additive.ofMul (inclusion hOY (b.symm 1))=0
      rw [map_one,map_one]
      rfl
    map_add' v w := by
      change Additive.ofMul (inclusion hOY (b.symm
        (Multiplicative.ofAdd v*Multiplicative.ofAdd w)))=_
      rw [map_mul,map_mul]
      rfl }
  let q : Additive Y →+ ((Fin 3 → F) × (Fin 3 → F)) := {
    toFun x := (b (sq x.toMul)).toAdd
    map_zero' := by change (b (sq 1)).toAdd=0; rw [map_one,map_one]; rfl
    map_add' x y := by
      change (b (sq (x.toMul*y.toMul))).toAdd=_
      rw [map_mul,map_mul]
      rfl }
  have hii : Function.Injective i := fun v w hv => Multiplicative.ofAdd.injective
    (b.symm.injective ((inclusion_injective hOY) (Additive.toMul.injective hv)))
  have hqi (v : (Fin 3 → F) × (Fin 3 → F)) : q (i v)=0 := by
    change (b (sq (inclusion hOY (b.symm (Multiplicative.ofAdd v))))).toAdd=0
    rw [(hsqker _).mpr (b.symm (Multiplicative.ofAdd v)).property,map_one]
    rfl
  have hiex (x : Additive Y) : q x=0 ↔ ∃ v,i v=x := by
    constructor
    · intro hx
      have hxs : sq x.toMul=1 := b.map_eq_one_iff.mp (Multiplicative.toAdd.injective hx)
      let v : O := ⟨x.toMul,(hsqker _).mp hxs⟩
      refine ⟨(b v).toAdd,?_⟩
      apply Additive.toMul.injective
      change inclusion hOY (b.symm (b v))=x.toMul
      rw [b.symm_apply_apply]
      rfl
    · rintro ⟨v,rfl⟩
      exact hqi v
  have hiα (k : K) (v : (Fin 3 → F) × (Fin 3 → F)) : ρ k (i v)=
      i (((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) (linearThreeActor e k) v) := by
    have ht : β k (b.symm (Multiplicative.ofAdd v)) =
        b.symm (Multiplicative.ofAdd (((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) (linearThreeActor e k) v)) := by
      apply b.injective
      apply Multiplicative.toAdd.injective
      rw [hb,b.apply_symm_apply,b.apply_symm_apply]
      rfl
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (O).subtype ht
  have hqα (k : K) (x : Additive Y) : q (ρ k x)=
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) (linearThreeActor e k) (q x) := by
    change (b (sq (α k x.toMul))).toAdd=_
    rw [hsqα]
    exact hb k _
  have hc (k : K) (hk : linearThreeActor e k ∈ center SL(3,F)) :
      ∀ l, Commute (ρ k) (ρ l) := by
    intro l
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    let z : Z := ⟨x.toMul,hYZ x.toMul.property⟩
    have hh := InitialDetection.scalar_centerAction_commutes h hn e k hk l
    have ht := congrArg (fun f : MulAut Z => (f z : G)) hh.eq
    simp only [MulAut.mul_apply,CentralSections.sectionAction_apply] at ht
    exact ht
  let d : DoubledAbelianTorus.Data (linearThreeActor e) ρ := {
    incl := i
    sq := q
    incl_injective := hii
    exact := hiex
    double := by
      intro x
      apply Additive.toMul.injective
      change x.toMul*x.toMul=inclusion hOY (b.symm (b (sq x.toMul)))
      rw [b.symm_apply_apply]
      apply Subtype.ext
      exact (pow_two (x.toMul:G)).symm
    incl_equivariant := hiα
    sq_equivariant := hqα }
  have hzero := DoubledAbelianTorus.square_eq_zero d
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun z hz => hc z (hz ▸ (center SL(3,F)).one_mem)) (by
      rw [h.field_card]
      exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hn)
  have hYtwo (y : Y) : (y:G)^2=1 := by
    have hz := hzero (Additive.ofMul y)
    change (b (sq y)).toAdd=0 at hz
    exact congrArg (O).subtype (b.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz))
  have hroot (z : Z) (hz : z^4=1) : z^2=1 := by
    have hy : (z:G) ∈ Y := mem_map_of_mem (Z).subtype (subset_closure hz)
    exact Subtype.ext (hYtwo ⟨z,hy⟩)
  have hpow (m : ℕ) : ∀ z : Z, z^(2^m)=1 → z^2=1 := by
    induction m with
    | zero =>
      intro z hz
      have hz' : z=1 := by simpa only [pow_zero,pow_one] using hz
      rw [hz',one_pow]
    | succ m ih =>
      intro z hz
      apply hroot
      have hh : (z^2)^(2^m)=1 := by
        rw [←pow_mul,Nat.mul_comm 2,←pow_succ]
        exact hz
      simpa only [←pow_mul] using ih (z^2) hh
  intro z
  obtain ⟨m,hm⟩ := hp.exists_pow_pow_eq_one z
  exact hpow m z hm

include h hn in
/-- The entire center equals its doubled natural central omega. -/
theorem center_eq_omega
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) : Z=O := by
  have hsq := center_exponent_two h hn e hm
  apply Eq.symm
  change Subgroup.omegaCenterIn Q=Z
  rw [Subgroup.omegaCenterIn_eq_omegaOneAmbient Q]
  apply le_antisymm (map_subtype_le _)
  intro x hx
  exact ⟨⟨x,hx⟩,subset_closure (hsq ⟨x,hx⟩),rfl⟩

include h hn in
/-- Reconstruct the whole doubled center at the original common marking. -/
theorem center_doubled
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    HasSectionModel K Z ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) :=
  (center_eq_omega h hn e hm).symm ▸ hm

include h hn in
/-- Both field-four alternatives now model the entire center. The genuine
fixed-factor hypothesis is used only in the prior omega recognition. -/
theorem center_models_field_four
    (hfixed : Q ⊓ centralizer (K : Set G)=⊥) (hfour : Nat.card F=4) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K Z ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  obtain ⟨e,hm | hm⟩ := CenterFourExclusion.center_alternatives_field_four h hn hfixed hfour
  · exact ⟨e,Or.inl hm⟩
  · exact ⟨e,Or.inr (center_doubled h hn e hm)⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.DoubledCenter
