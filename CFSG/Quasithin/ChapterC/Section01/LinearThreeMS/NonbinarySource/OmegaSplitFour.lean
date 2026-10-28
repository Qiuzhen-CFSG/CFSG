module
public import Theory.Representation.SL3.NaturalSelfExtensionFour
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.OmegaCoverFaithful
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.DoubledRadical

/-!
# Whole central-omega recognition at field four

Assume the genuine nonbinary linear-three MS hypotheses and C_Q(K)=1.
If the comparison with the initial action has trivial kernel, the whole
central omega is the initial moved subgroup. Otherwise saturation gives a
natural self-extension with one common full SL₃ marking. The faithful-cover
theorem identifies the component with that full quotient, and the intrinsic
four-field extension calculation splits the whole module.

This gives actual natural or doubled-natural section models for Ω₁(Z(Q))
in the original group. For abelian Q, MS3 supplies exponent two, so this is
Q itself; the block construction and doubled radical calculation then give
complete C.1.34 alternatives for every original eligible Sylow subgroup.
The possible comparison kernels are retained. This does not identify Z(Q)
or the upper/Frattini sections in the nonabelian case.

NonblockOmegaSplitFour discharges C_Q(K)=1 from the original chosen module
and applies these results without Hypothesis1223 or a classification callback.
Source: Aschbacher–Smith C.1.34, pp.136–137, and original 4.3.8–10,
pp.616–617; the splitting uses the SL₃(4) calculation cited at H.12.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.OmegaSplitFour
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E := CentralSections.coreOmegaLayer_elementary
local instance binaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* H)
local notation "rho" => CentralSections.coreOmegaRepresentation h hn
local notation "f" => NoncoreOffenders.toInitial h hn E
  (CentralSections.coreOmegaLayer_centralizer_le h hn)
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R)
include h hn

/-- At field four, the saturated whole central omega is doubled natural at
one marking of the original full quotient. -/
theorem kernel_nontrivial_split
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hfour : Nat.card F = 4)
    (hk : (f).ker ≠ ⊥) :
    ∃ α : SL(3,F) ≃* SL(3,F), Nonempty (Representation.Equiv ((rho).comp (B).subtype)
      ((((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)).restrictScalars
        (k := ZMod 2)).comp
        (α.toMonoidHom.comp (KernelOffenders.omegaCover h hn e).toMonoidHom))) := by
  have hz : center SL(3,F) ≠ ⊥ := by
    intro he
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he
    exact hh (by rw [hfour])
  obtain ⟨s,hs,hne⟩ := (center SL(3,F)).bot_or_exists_ne_one.resolve_left hz
  obtain ⟨A,hA,D,hDA,hD,hquad,hw,hm,hd,_⟩ :=
    KernelSaturation.exists_exact_or_saturated_offender h hn hfixed (R.subgroupOf J) le_rfl
  obtain ⟨α,I,⟨en⟩,⟨eq⟩⟩ := KernelSaturation.kernel_nontrivial_common_marking
    h hn hfixed e s hs hne D hD hm hd hk
  let b : B ≃* SL(3,F) := MulEquiv.ofBijective
    (KernelOffenders.omegaCover h hn e).toMonoidHom
    ⟨OmegaCoverFaithful.cover_injective h hn hfixed e,
      (KernelOffenders.omegaCover h hn e).surjective⟩
  exact ⟨α,SL3NaturalSelfExtensionFour.split hfour ((rho).comp (B).subtype)
    (b.trans α) I en eq⟩

omit [CharP F 2] in
private theorem omega_section_of_coordinates
    {V : Type*} [AddCommGroup V] [Module F V] [Module (ZMod 2) V]
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (v : Representation F SL(3,F) V)
    (l : Additive E ≃ₗ[ZMod 2] V)
    (hl : ∀ (k : L) (x : Additive E), l (rho (q k.val) x) =
      v (linearThreeActor e ⟨k,k.property⟩) (l x)) :
    HasSectionModel K Z ⊥ (linearThreeActor e) v := by
  have hZJ : Z ≤ J := (map_subtype_le _).trans (msQ_le_joinCore.trans (pCoreIn_le 2 _))
  let d : E ≃* Z := {
    toFun x := ⟨x.val.val,(CentralSections.coreOmegaLayer_eq (K := K) (R := R)).le x.property⟩
    invFun x := ⟨⟨x,hZJ x.property⟩,(CentralSections.coreOmegaLayer_eq (K := K) (R := R)).ge x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let a : Z ≃* Multiplicative V := d.symm.trans l.toAddEquiv.toMultiplicative
  rw [HasSectionModel,bot_subgroupOf]
  have hZN : J ≤ normalizer Z := (normal_subgroupOf_iff_le_normalizer hZJ).mp (by
    rw [← CentralSections.coreOmegaLayer_eq]
    infer_instance)
  refine ⟨bot_le,(show K ≤ J from le_sup_left).trans hZN,
    le_normalizer_of_normal,inferInstance,QuotientGroup.quotientBot.trans a,?_⟩
  intro k x y hxy
  let kL : L := ⟨⟨k,mem_sup_left k.property⟩,k.property⟩
  have he : Additive.ofMul (d.symm y) = rho (q kL.val) (Additive.ofMul (d.symm x)) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [CentralSections.coreOmegaRepresentation_eq,
      NormalElementaryQuotient.representation_apply]
    exact hxy
  change l (Additive.ofMul (d.symm y)) =
    v (linearThreeActor e k) (l (Additive.ofMul (d.symm x)))
  rw [he]
  exact hl kL _

/-- The saturated branch gives a model of the entire ambient central omega,
with bottom denominator and the original quotient marking reframed once. -/
theorem kernel_nontrivial_section
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hfour : Nat.card F = 4)
    (hk : (f).ker ≠ ⊥) :
    ∃ α : SL(3,F) ≃* SL(3,F),
      HasSectionModel K Z ⊥ (linearThreeActor (e.trans α))
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  obtain ⟨α,⟨a⟩⟩ := kernel_nontrivial_split h hn hfixed e hfour hk
  refine ⟨α,omega_section_of_coordinates h hn (e.trans α) _ a.toLinearEquiv ?_⟩
  intro k x
  have hh := LinearMap.congr_fun (a.isIntertwining' (((q).comp (L).subtype).rangeRestrict k)) x
  change a (rho (q k.val) x) =
    (specialLinearNatural 3 (α ((KernelOffenders.omegaCover h hn e).toMonoidHom
      (((q).comp (L).subtype).rangeRestrict k))) (a x).1,
     specialLinearNatural 3 (α ((KernelOffenders.omegaCover h hn e).toMonoidHom
      (((q).comp (L).subtype).rangeRestrict k))) (a x).2) at hh
  rw [KernelOffenders.omegaCover_apply] at hh
  exact hh

omit hEN in
/-- With C_Q(K)=1 at field four, the whole central omega is natural or doubled
natural. This recognizes the full subgroup, not only its chief sections. -/
theorem omega_section_models
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥) (hfour : Nat.card F = 4) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K Z ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  let := CentralSections.coreOmegaLayer_normal h hn
  by_cases hk : (f).ker = ⊥
  · rw [SmallOmega.omega_eq_initial_of_kernel_bot h hn hfixed hk]
    exact initialMoved_section_models h hn
  · let e := Classical.choice h.model
    obtain ⟨α,hm⟩ := kernel_nontrivial_section h hn hfixed e hfour hk
    exact ⟨e.trans α,Or.inr hm⟩

omit hEN in
/-- Abelianity identifies the recognized central omega with the entire core. -/
theorem abelian_section_models
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥) (hfour : Nat.card F = 4)
    (hc : IsMulCommutative (msQ K R)) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K (msQ K R) ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  let := abelian_msQ_elementary h hn hc
  have hZ : Z = msQ K R := by
    apply le_antisymm (map_subtype_le _)
    intro x hx
    apply (Subgroup.mem_omegaCenterIn_iff _ _).mpr
    exact ⟨hx,(le_centralizer_iff_isMulCommutative.mpr hc) hx,
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  simpa only [hZ] using omega_section_models h hn hfixed hfour

omit hEN in
/-- The abelian whole-core branch of C.1.34 is complete at field four when
C_Q(K)=1, for every original eligible Sylow overgroup and its radical. -/
theorem moduleAlternatives_of_abelian
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥) (hfour : Nat.card F = 4)
    (hc : IsMulCommutative (msQ K R)) {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F), MSModuleAlternatives K R S n F e := by
  obtain ⟨e,hm | hm⟩ := abelian_section_models h hn hfixed hfour hc
  · obtain ⟨hb,hl⟩ := block_of_natural_msQ h hn e hm
    exact ⟨e,Or.inl ⟨hb,hl,hm⟩⟩
  · exact ⟨e,DoubledRadical.moduleAlternatives_of_doubled_all_degrees h hn e hm hS hRS⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.OmegaSplitFour
