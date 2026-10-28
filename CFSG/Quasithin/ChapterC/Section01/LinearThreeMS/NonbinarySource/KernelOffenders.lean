module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NoncoreOffenders
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ExceptionalKernel
public import Theory.Representation.BinaryOffender.SmallCentralKernel

/-!
# Offenders in the whole central-omega covering component

For a nonbinary linear-three MS pair, the image of the original component
on E = Ω₁(Z([O₂(KR),K])) is a perfect central cover of the supplied full SL₃
quotient. We identify its complete kernel as the image of the component's
two-core and retain the given marking on every original representative.

If C_Q(K)=1, this component has zero fixed space on E. At field four the
exceptional covering kernel is an abelian two-group on at most two generators.
Its elementary subgroups have order at most four, whereas every nontrivial
actor commuting with the fixed-free perfect component moves at least three
binary dimensions. Thus no offender lies in that kernel. Every offender in
the component has a nontrivial image on the original initial action.

The companion `NonblockKernelOffenders` supplies the fixed-factor premise
from the original nonblock configuration. This excludes kernel offenders;
it does not assert that the covering kernel itself is trivial or recognize
the whole central and Frattini sections required by C.1.34.
Source: Aschbacher--Smith C.1.34, pp.136--137, and I.1.3(6), p.407.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.KernelOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "N" => pCore 2 (K ⊔ R : Subgroup G)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E :=
  CentralSections.coreOmegaLayer_elementary
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* (J ⧸ centralizer (E : Set J)))
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* (J ⧸ centralizer (E : Set J)))
local notation "rho" => CentralSections.coreOmegaRepresentation h hn

omit [Finite G] hEN in
private theorem core_centralizes_omega : ⁅N,L⁆ ≤ centralizer (E : Set J) := by
  intro x hx z hz
  apply Subtype.ext
  have hx' : (x : G) ∈ msQ K R :=
    (commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem (J).subtype hx
  have hz' : (z : G) ∈ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R) := by
    change z ∈ E at hz
    rw [CentralSections.coreOmegaLayer_eq] at hz
    exact hz
  exact (((mem_omegaCenterIn_iff (msQ K R) (z : G)).mp hz').2.1 (x : G) hx').symm

include h hn

/-- The actual central-omega component, with its full kernel, covers the marked SL₃. -/
def omegaCover (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    PerfectCentralCovering.Cover B SL(3,F) := by
  let := h.component.2.perfect
  exact Matrix.SL3.CommutatorCentralCover.cover L N
    (joinQuotientEquiv (R := R) e) q
    (pCore_subnormal_eq_comap 2 h.component.2.subnormal).symm
    (by rw [QuotientGroup.ker_mk']; exact CentralSections.coreOmegaLayer_centralizer_le h hn)
    (by rw [QuotientGroup.ker_mk']; exact core_centralizes_omega)

/-- The covering projection agrees with the supplied quotient marking. -/
theorem omegaCover_apply (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : L) :
    (omegaCover h hn e).toMonoidHom (((q).comp (L).subtype).rangeRestrict k) =
      linearThreeActor e ⟨k,k.property⟩ := by
  unfold omegaCover
  rw [Matrix.SL3.CommutatorCentralCover.cover_apply]
  rfl

/-- The entire covering kernel is the image of the intrinsic component two-core. -/
theorem omegaCover_kernel (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    (omegaCover h hn e).toMonoidHom.ker =
      (pCore 2 L).map ((q).comp (L).subtype).rangeRestrict := by
  ext b
  obtain ⟨k,rfl⟩ := ((q).comp (L).subtype).rangeRestrict_surjective b
  have hk : (omegaCover h hn e).toMonoidHom (((q).comp (L).subtype).rangeRestrict k) =
      joinQuotientEquiv (R := R) e (QuotientGroup.mk' (pCore 2 L) k) :=
    omegaCover_apply h hn e k
  constructor
  · intro he
    apply mem_map_of_mem
    change (omegaCover h hn e).toMonoidHom _ = 1 at he
    rw [hk,MulEquiv.map_eq_one_iff] at he
    exact (QuotientGroup.eq_one_iff k).mp he
  · rintro ⟨l,hl,he⟩
    change (omegaCover h hn e).toMonoidHom _ = 1
    rw [←he,omegaCover_apply]
    change joinQuotientEquiv (R := R) e (QuotientGroup.mk' (pCore 2 L) l) = 1
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff l).mpr hl

omit [CharP F 2] in
/-- Triviality of the whole core fixed factor removes every fixed vector on its central omega. -/
theorem omega_fixedSpace_eq_bot
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥) :
    fixedSpace rho B = ⊥ := by
  apply bot_unique
  intro v hv
  have hvc : (v.toMul : J) ∈ centralizer (L : Set J) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) L v).mp
    simpa only [CentralSections.coreOmegaRepresentation_eq,
      MonoidHom.range_comp,range_subtype] using hv
  have he : ((v.toMul : J) : G) = 1 := by
    apply hfixed.le
    refine ⟨?_,?_⟩
    · have hvE := (CentralSections.coreOmegaLayer_eq (K := K) (R := R)).le v.toMul.property
      exact map_subtype_le _ hvE
    · intro k hk
      exact congrArg (J).subtype (hvc ⟨k,mem_sup_left hk⟩ hk)
  exact Additive.toMul.injective (Subtype.ext (Subtype.ext he))

/-- The field-four central covering kernel contains no offender on the whole central omega. -/
theorem field_four_no_kernel_offender
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hA : A ≤ (omegaCover h hn e).toMonoidHom.ker.map (B).subtype) :
    ¬ IsOffender rho A := by
  let f := omegaCover h hn e
  let C := f.toMonoidHom.ker.map (B).subtype
  let := f.isPerfect
  let : IsMulCommutative f.toMonoidHom.ker := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (f.ker_le_center x.property) y).symm⟩⟩
  let : IsMulCommutative C := inferInstance
  have hb := Matrix.SL3.ExceptionalFourKernel.kernel_bounds hfour f
  have hp : IsPGroup 2 f.toMonoidHom.ker :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 4) hb.1
  have hr : Group.rank C ≤ 2 := by
    rw [Group.rank_congr (f.toMonoidHom.ker.equivMapOfInjective
      (B).subtype (B).subtype_injective).symm]
    exact hb.2.1
  have hc : ⁅B,C⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro x ⟨z,hz,rfl⟩ b hb
    exact congrArg (B).subtype (mem_center_iff.mp (f.ker_le_center hz) ⟨b,hb⟩)
  exact SmallCentralKernel.not_isOffender rho B
    (CentralSections.coreOmegaRepresentation_injective h hn)
    (omega_fixedSpace_eq_bot h hn hfixed) C hc (hp.map _) hr A hA

/-- The same exclusion on the literal image of the original component two-core. -/
theorem field_four_no_core_offender
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hA : A ≤ ((K.subgroupOf (K ⊔ R)).pCoreIn 2).map q) :
    ¬ IsOffender rho A := by
  apply field_four_no_kernel_offender h hn hfour hfixed e A
  rw [omegaCover_kernel, map_map]
  change A ≤ ((pCore 2 L).map (L).subtype).map q at hA
  rwa [map_map] at hA

/-- Every component offender survives the literal comparison with the initial action. -/
theorem field_four_component_offender_initial_ne_bot
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A) :
    A.map (NoncoreOffenders.toInitial h hn E
      (CentralSections.coreOmegaLayer_centralizer_le h hn)) ≠ ⊥ := by
  intro hz
  apply field_four_no_core_offender h hn hfour hfixed e A ?_ hA
  intro a ha
  have haB : a ∈ (L).map q := by
    simpa only [MonoidHom.range_comp,range_subtype] using hAB ha
  obtain ⟨k,hk,rfl⟩ := haB
  have he := (map_eq_bot_iff A).mp hz ha
  change NoncoreOffenders.toInitial h hn E
    (CentralSections.coreOmegaLayer_centralizer_le h hn) (q k) = 1 at he
  rw [NoncoreOffenders.toInitial_apply] at he
  have hkN : k ∈ N := (centralOmega_kernel_eq_core h hn).le
    ((QuotientGroup.eq_one_iff k).mp he)
  have hkL : (⟨k,hk⟩ : L) ∈ pCore 2 L := by
    rw [pCore_subnormal_eq_comap 2 h.component.2.subnormal]
    exact hkN
  exact mem_map_of_mem q (mem_map_of_mem (L).subtype hkL)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.KernelOffenders
