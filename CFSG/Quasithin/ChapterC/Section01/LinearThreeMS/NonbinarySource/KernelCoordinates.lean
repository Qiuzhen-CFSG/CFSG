module
public import Theory.Representation.SL3.NaturalFlagCentralizer
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.KernelSaturation
public import Theory.Representation.BinaryGroupAction

/-!
# Additive-field coordinates for the whole central-omega kernel

Let E = Ω₁(Z([O₂(KR),K])), and assume C_Q(K)=1. The kernel of the
faithful E-action's projection to the initial action centralizes the full
covering component. When the full SL₃ quotient has a nonidentity scalar,
saturation supplies a natural self-extension at one common marking.
Choose its defining involution central in the entire kernel; this retains
invariance of the natural flag under every kernel element.

The natural-flag centralizer theorem embeds that whole kernel in the
additive original field. Thus it is elementary abelian of order dividing
2ⁿ, including at field four, where the exact possible orders are 1, 2, 4.
The kernel is retained. Neither a complement of the natural flag nor an
identification of the whole center or upper/Frattini sections is assumed.
NonblockKernelCoordinates applies the result to the original nonblock input.
Source: Aschbacher–Smith C.1.34, printed pp.136–137, the saturated
central-omega branch; the scalar-commutant calculation is elementary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.KernelCoordinates
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

/-- The entire surviving comparison kernel embeds in the additive original
field, without a splitting premise on the whole central omega. -/
theorem kernel_embeds_field_of_scalar
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1) :
    ∃ a : (f).ker →* Multiplicative F, Function.Injective a := by
  by_cases hk : (f).ker = ⊥
  · refine ⟨1,fun x y _ => Subtype.ext ?_⟩
    have hx : (x : H) = 1 := mem_bot.mp (hk ▸ x.property)
    have hy : (y : H) = 1 := mem_bot.mp (hk ▸ y.property)
    exact hx.trans hy.symm
  obtain ⟨A,hA,D,hDA,hD,hq,hw,hm,hd,_⟩ :=
    KernelSaturation.exists_exact_or_saturated_offender h hn hfixed (R.subgroupOf J) le_rfl
  obtain ⟨x,_,_,hxc,hxp,I,hI,hr,hker,_,_⟩ :=
    KernelSaturation.kernel_nontrivial_natural_flag h hn hfixed e s hs hsne D hD hm hd hk
  obtain ⟨α,l,hl⟩ := ConstituentSections.irrPlus_marked_coordinates h hn hfixed e I hI
  let t : Additive E →ₗ[ZMod 2] Additive E := rho x - 1
  let U := invariantSubspace rho B I hI.choose
  have hc (b : B) (v : Additive E) : t (rho b v) = rho b (t v) := by
    change rho x (rho b.val v) - rho b.val v = rho b.val (rho x v-v)
    rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      mem_centralizer_iff.mp hxc b (mem_sup_left b.property)]
  obtain ⟨c,_,he⟩ := quotient_equiv_of_range_ker_eq ((rho).comp (B).subtype) t hc U hr hker
  let π := α.toMonoidHom.comp (KernelOffenders.omegaCover h hn e).toMonoidHom
  let σ := ((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp π
  have en : U.toRepresentation.Equiv σ := .mk l (by
    intro b
    apply LinearMap.ext
    exact hl b)
  have eq : U.quotientRepresentation.Equiv σ := .mk (c.trans l) (by
    intro b
    apply LinearMap.ext
    intro v
    change l (c (U.quotientRepresentation b v)) = _
    rw [he,hl]
    rfl)
  have hp : IsPGroup 2 (f).ker := by
    rw [NoncoreOffenders.toInitial_kernel]
    exact pCore_isPGroup
  apply SL3NaturalFlag.two_group_embedding rho
    (CentralSections.coreOmegaRepresentation_injective h hn) B (f).ker hp
    (MovingBounds.initial_kernel_le_centralizer h hn) π
    (α.surjective.comp (KernelOffenders.omegaCover h hn e).surjective) U en eq
  intro p v hv
  change v ∈ I at hv
  obtain ⟨w,rfl⟩ := hr.symm ▸ hv
  change rho p.val (t w) ∈ I
  rw [←hr]
  refine ⟨rho p.val w,?_⟩
  change rho x (rho p.val w)-rho p.val w = rho p.val (rho x w-w)
  rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
    mem_centralizer_iff.mp hxp p p.property]

/-- The full comparison kernel is elementary abelian of order dividing q.
This is a bound on the actual kernel, rather than on a selected subgroup. -/
theorem kernel_elementary_card_of_scalar
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1) :
    IsElementaryAbelian 2 (f).ker ∧ Nat.card (f).ker ∣ 2^n := by
  obtain ⟨a,ha⟩ := kernel_embeds_field_of_scalar h hn hfixed e s hs hsne
  let : IsElementaryAbelian 2 (Multiplicative F) := BinaryGroupAction.elementary
  refine ⟨IsElementaryAbelian.of_injective a ha,?_⟩
  have hd : Nat.card (f).ker ∣ Nat.card (Multiplicative F) := card_dvd_of_injective a ha
  change Nat.card (f).ker ∣ Nat.card F at hd
  rwa [h.field_card] at hd

/-- At field four, the literal whole-action kernel has order one, two or four.
It is not discarded, and splitting of the module is not assumed. -/
theorem kernel_elementary_field_four
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hfour : Nat.card F = 4) :
    IsElementaryAbelian 2 (f).ker ∧
      (Nat.card (f).ker = 1 ∨ Nat.card (f).ker = 2 ∨ Nat.card (f).ker = 4) := by
  have hz : center SL(3,F) ≠ ⊥ := by
    intro he
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he
    exact hh (by rw [hfour])
  obtain ⟨s,hs,hne⟩ := (center SL(3,F)).bot_or_exists_ne_one.resolve_left hz
  obtain ⟨hE,hc⟩ := kernel_elementary_card_of_scalar h hn hfixed e s hs hne
  have hc4 : Nat.card (f).ker ∣ 4 := by rwa [←h.field_card,hfour] at hc
  refine ⟨hE,?_⟩
  have hpos : 0 < Nat.card (f).ker := Nat.card_pos
  have hle : Nat.card (f).ker ≤ 4 := Nat.le_of_dvd (by decide) hc4
  interval_cases hh : Nat.card (f).ker <;> simp_all

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.KernelCoordinates
