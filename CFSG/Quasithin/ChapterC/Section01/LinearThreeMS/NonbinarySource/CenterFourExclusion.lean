module
public import Theory.Representation.SL3.NaturalAbelianTorus
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CenterPowerSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.InitialDetection

/-!
# Excluding the canonical exponent-four center lift

Suppose Ω₁(Z(Q)) is natural at the supplied full SL₃ marking. A higher
exponent would give the canonical Ω₂(Z(Q)), with its natural bottom and
square quotient. The literal square map constructs an exact abelian
extension of these two natural modules; it is not an arbitrary isomorphism
between their abstract carriers.

The action of the original component on the whole center is a perfect
central cover, so every element of the quotient kernel acts centrally.
The diagonal-torus obstruction to a natural abelian lift excludes the
canonical four-layer at every nonbinary degree. Thus the entire center
has exponent two and is natural with the same marking. No central scalar,
trivial fixed-factor hypothesis or injectivity of the cover is needed.

At field four, with the genuine fixed-factor exclusion used by the
whole-omega recognition, the original reconstruction has just natural
whole center or doubled whole omega. The nonabelian
upper sections and the doubled-omega branch remain required for C.1.34.
NonblockCenterFourExclusion applies this to the original chosen module.
Source: Aschbacher–Smith C.1.34, printed pp.136–137, and original 4.3.8–10,
pp.616–617; the torus obstruction is elementary endomorphism algebra.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CenterFourExclusion
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "Q" => msQ K R
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
local notation "O" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn Q

include h hn in
/-- A natural whole central omega forces the actual center to have exponent
two at every nonbinary degree. No scalar or C_Q(K)=1 premise is used. -/
theorem center_exponent_two
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
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
  by_contra hnot
  obtain ⟨hfour,hmodel,_,hroot⟩ := CenterPowerSections.natural_four_layer_of_not_elementary
    hp ((le_sup_left : K ≤ K ⊔ R).trans hnZ) e (he ▸ hm) hnot
  let Y := (omega Z (p := 2) 2).map (Z).subtype
  have hYZ : Y ≤ Z := map_subtype_le _
  have hOY : O ≤ Y := by rw [he]; exact hmodel.1
  have hKY : K ≤ normalizer (Y : Set G) := hmodel.2.1
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
  have hsqs : Function.Surjective sq := by
    intro v
    let x : Y := ⟨v,hOY v.property⟩
    have hx : x^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ v.property)
    obtain ⟨y,hy⟩ := hroot x hx
    exact ⟨y,Subtype.ext (congrArg Y.subtype hy)⟩
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKO,_,hi,b0,hb0⟩ := hm
  let := hi
  let b : O ≃* Multiplicative (Fin 3 → F) := QuotientGroup.quotientBot.symm.trans b0
  let β : K →* MulAut O := (O).normalizerMonoidHom.comp (inclusion hKO)
  have hb (k : K) (v : O) : (b (β k v)).toAdd =
      specialLinearNatural 3 (linearThreeActor e k) (b v).toAdd :=
    hb0 k v (β k v) rfl
  have hsqα (k : K) (x : Y) : sq (α k x)=β k (sq x) := by
    apply Subtype.ext
    change ((k:G)*(x:G)*(k:G)⁻¹)^2=(k:G)*(x:G)^2*(k:G)⁻¹
    exact (map_pow (MulAut.conj (k:G)) (x:G) 2).symm
  let i : (Fin 3 → F) →+ Additive Y := {
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
  let q : Additive Y →+ (Fin 3 → F) := {
    toFun x := (b (sq x.toMul)).toAdd
    map_zero' := by change (b (sq 1)).toAdd=0; rw [map_one,map_one]; rfl
    map_add' x y := by
      change (b (sq (x.toMul*y.toMul))).toAdd=_
      rw [map_mul,map_mul]
      rfl }
  have hii : Function.Injective i := fun v w hv => Multiplicative.ofAdd.injective
    (b.symm.injective ((inclusion_injective hOY) (Additive.toMul.injective hv)))
  have hqs : Function.Surjective q := by
    intro v
    obtain ⟨x,hx⟩ := hsqs (b.symm (Multiplicative.ofAdd v))
    exact ⟨Additive.ofMul x,by change (b (sq x)).toAdd=v; rw [hx,b.apply_symm_apply]; rfl⟩
  have hqi (v : Fin 3 → F) : q (i v)=0 := by
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
  have hiα (k : K) (v : Fin 3 → F) : ρ k (i v)=
      i (specialLinearNatural 3 (linearThreeActor e k) v) := by
    have ht : β k (b.symm (Multiplicative.ofAdd v)) =
        b.symm (Multiplicative.ofAdd (specialLinearNatural 3 (linearThreeActor e k) v)) := by
      apply b.injective
      apply Multiplicative.toAdd.injective
      rw [hb,b.apply_symm_apply,b.apply_symm_apply]
      rfl
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (O).subtype ht
  have hqα (k : K) (x : Additive Y) : q (ρ k x)=
      specialLinearNatural 3 (linearThreeActor e k) (q x) := by
    change (b (sq (α k x.toMul))).toAdd=_
    rw [hsqα]
    exact hb k _
  let d : NaturalAbelianExtension.Data (linearThreeActor e) ρ :=
    ⟨i,q,hii,hqs,hiex,hiα,hqα⟩
  have hd (x : Additive Y) : x+x=d.incl (d.proj x) := by
    apply Additive.toMul.injective
    change x.toMul*x.toMul=inclusion hOY (b.symm (b (sq x.toMul)))
    rw [b.symm_apply_apply]
    apply Subtype.ext
    exact (pow_two (x.toMul:G)).symm
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
  apply NaturalAbelianTorus.no_square_extension d
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun z hz => hc z (hz ▸ (center SL(3,F)).one_mem)) hd
  rw [h.field_card]
  exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hn

include h hn in
-- Retain the original named hypothesis arguments for compatibility.
set_option linter.unusedVariables false in
/-- Compatibility with the earlier scalar formulation. The scalar is now
unnecessary: the torus proof works at every nonbinary degree. -/
theorem center_exponent_two_of_scalar
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (s : SL(3,F)) (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1) :
    ∀ z : Z, z^2=1 := by
  exact center_exponent_two h hn e hm

include h hn in
/-- The whole center equals its natural central omega at every nonbinary
degree, with the original full quotient marking unchanged. -/
theorem center_eq_omega
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    Z=O := by
  have hsq := center_exponent_two h hn e hm
  apply Eq.symm
  change Subgroup.omegaCenterIn Q=Z
  rw [Subgroup.omegaCenterIn_eq_omegaOneAmbient Q]
  apply le_antisymm (map_subtype_le _)
  intro x hx
  exact ⟨⟨x,hx⟩,subset_closure (hsq ⟨x,hx⟩),rfl⟩

include h hn in
/-- A natural whole central omega is the entire natural center for every
nonbinary field, including odd degree, at the same marking. -/
theorem center_natural
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) := by
  exact (center_eq_omega h hn e hm).symm ▸ hm

include h hn in
-- Retain the original named hypothesis arguments for compatibility.
set_option linter.unusedVariables false in
/-- Compatibility with the earlier central-scalar formulation. -/
theorem center_natural_of_scalar
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (s : SL(3,F)) (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1) :
    HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) := by
  exact center_natural h hn e hm

include h hn in
-- Retain the original named hypothesis arguments for compatibility.
set_option linter.unusedVariables false in
/-- The field-four instance of the natural whole-center theorem, with the
supplied marking preserved. -/
theorem center_natural_field_four
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (hfour : Nat.card F=4) :
    HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) := by
  exact center_natural h hn e hm

include h hn in
/-- The original field-four center reconstruction has only the natural
whole center and doubled-omega alternatives. The homocyclic lift is excluded. -/
theorem center_alternatives_field_four
    (hfixed : Q ⊓ centralizer (K : Set G)=⊥) (hfour : Nat.card F=4) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K O ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  obtain ⟨e,hm | hm⟩ := OmegaSplitFour.omega_section_models h hn hfixed hfour
  · exact ⟨e,Or.inl (center_natural_field_four h hn e hm hfour)⟩
  · exact ⟨e,Or.inr hm⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CenterFourExclusion
