module
public import Theory.Representation.SL3.NaturalSelfExtensionCover
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.KernelSaturation

/-!
# Faithful whole central-omega component at every nonbinary field

Let Q = [O₂(KR),K], E = Ω₁(Z(Q)), and assume C_Q(K)=1. The actual
component image on E was already a perfect central cover of the supplied
full SL₃. Outside field four, the ordinary multiplier calculation makes
that cover faithful. At field four, if the comparison with the initial
action has trivial kernel, faithfulness follows directly. Otherwise the
saturation theorem makes E a natural self-extension at one marking.
Scalar-weighted traces eliminate the central covering kernel on that
self-extension, without assuming a complement.

Thus intrinsic O₂(K) centralizes the whole E, and the original full SL₃
quotient marks the actual component image faithfully, with compatibility
on every original representative. The original nonblock application is
in NonblockOmegaCoverFaithful. This removes the exceptional component
kernel on E; the whole-actor kernel, splitting of the saturated module,
and the whole center and upper/Frattini sections remain separate issues.
Source: Aschbacher–Smith C.1.34 and I.1.3(6), printed pp.136–137,407.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.OmegaCoverFaithful
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
include h hn

private theorem cover_injective_of_initial_kernel_bot
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hk : (f).ker = ⊥) :
    Function.Injective (KernelOffenders.omegaCover h hn e).toMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  rw [KernelOffenders.omegaCover_kernel] at hz
  obtain ⟨k,hkcore,rfl⟩ := hz
  change ((q).comp (L).subtype).rangeRestrict k = 1
  apply Subtype.ext
  apply (MonoidHom.ker_eq_bot_iff _).mp hk
  change (f) (q (k : J)) = (f) 1
  rw [map_one,NoncoreOffenders.toInitial_apply]
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [centralOmega_kernel_eq_core h hn]
  rw [pCore_subnormal_eq_comap 2 h.component.2.subnormal] at hkcore
  exact hkcore

/-- The scalar saturation alternative eliminates the entire even kernel of
the component's action, without splitting the natural self-extension. -/
theorem cover_injective_of_scalar
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1) :
    Function.Injective (KernelOffenders.omegaCover h hn e).toMonoidHom := by
  by_cases hk : (f).ker = ⊥
  · exact cover_injective_of_initial_kernel_bot h hn e hk
  obtain ⟨A,hA,D,hDA,hD,hq,hw,hm,hd,_⟩ :=
    KernelSaturation.exists_exact_or_saturated_offender h hn hfixed (R.subgroupOf J) le_rfl
  obtain ⟨α,I,⟨en⟩,⟨eq⟩⟩ := KernelSaturation.kernel_nontrivial_common_marking
    h hn hfixed e s hs hsne D hD hm hd hk
  let c := KernelOffenders.omegaCover h hn e
  let := c.isPerfect
  have hi := PerfectSelfExtension.natural_cover_injective ((rho).comp (B).subtype)
    ((CentralSections.coreOmegaRepresentation_injective h hn).comp (B).subtype_injective)
    (α.toMonoidHom.comp c.toMonoidHom) (α.surjective.comp c.surjective)
    (by
      intro z hz
      apply c.ker_le_center
      exact α.injective (hz.trans (map_one α).symm)) I en eq
  exact fun x y he => hi (congrArg α he)

/-- With trivial C_Q(K), the whole central-omega component is faithfully
marked by the original full SL₃ quotient in every nonbinary field. -/
theorem cover_injective
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    Function.Injective (KernelOffenders.omegaCover h hn e).toMonoidHom := by
  by_cases hfour : Nat.card F = 4
  · have hz : center SL(3,F) ≠ ⊥ := by
      intro he
      have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he
      exact hh (by rw [hfour])
    obtain ⟨s,hs,hne⟩ := (center SL(3,F)).bot_or_exists_ne_one.resolve_left hz
    exact cover_injective_of_scalar h hn hfixed e s hs hne
  · let c := KernelOffenders.omegaCover h hn e
    let := c.isPerfect
    have htwo : Nat.card F ≠ 2 := by
      rw [h.field_card]
      have hh : 2^1 < 2^n := Nat.pow_lt_pow_right (by decide) hn
      omega
    obtain ⟨a,ha,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift
      htwo hfour c.quotientCenterEquiv
    exact (c.surjective.bijective_of_nat_card_le (Nat.card_le_card_of_surjective a ha)).1

omit hEN in
/-- Intrinsic O₂(K) centralizes the whole Ω₁(Z(Q)), including field four.
This does not identify Ω₁(Z(Q)) with Z(Q) or eliminate the whole-actor kernel. -/
theorem componentCore_centralizes_omega
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥) :
    K.pCoreIn 2 ≤ centralizer
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (msQ K R) : Set G) := by
  let := CentralSections.coreOmegaLayer_normal h hn
  let e := Classical.choice h.model
  have hz := (MonoidHom.ker_eq_bot_iff _).mpr (cover_injective h hn hfixed e)
  rw [KernelOffenders.omegaCover_kernel] at hz
  rintro x ⟨k,hk,rfl⟩ y hy
  let kJ : J := ⟨k,mem_sup_left k.property⟩
  let kL : L := ⟨kJ,k.property⟩
  have hkL : kL ∈ pCore 2 L := by
    let eL : L ≃* K := subgroupOfEquivOfLe le_sup_left
    rw [←pCore_map_iso 2 eL.symm]
    exact mem_map_of_mem eL.symm.toMonoidHom hk
  have hqk : q kJ = 1 := congrArg Subtype.val (hz.le (mem_map_of_mem _ hkL))
  have hkc : kJ ∈ centralizer (E : Set J) := (QuotientGroup.eq_one_iff _).mp hqk
  have hyJ : y ∈ J := (msQ_le_joinCore.trans (pCoreIn_le 2 _)) (map_subtype_le _ hy)
  have hyE : (⟨y,hyJ⟩ : J) ∈ E := by
    rw [CentralSections.coreOmegaLayer_eq]
    exact hy
  exact congrArg (J).subtype (hkc ⟨y,hyJ⟩ hyE)

/-- The actual whole central-omega component, marked by the original quotient.
This is a group isomorphism; it does not assert a splitting of its module. -/
def omegaEquiv
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) : B ≃* SL(3,F) :=
  MulEquiv.ofBijective (KernelOffenders.omegaCover h hn e).toMonoidHom
    ⟨cover_injective h hn hfixed e,(KernelOffenders.omegaCover h hn e).surjective⟩

/-- The faithful marking commutes with the literal original component map. -/
theorem omegaEquiv_apply
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : L) :
    omegaEquiv h hn hfixed e (((q).comp (L).subtype).rangeRestrict k) =
      linearThreeActor e ⟨k,k.property⟩ :=
  KernelOffenders.omegaCover_apply h hn e k

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.OmegaCoverFaithful
