module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.OmegaOrbit
public import Theory.Representation.G2BinaryNaturalOffenders
public import Theory.Representation.BinaryOffender.QuadraticQuotient
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.WholeQuotient

/-!
# Equality of the G₂ central-omega layer and its original seed

A best offender on the central-omega layer projects to an offender on its
literal natural quotient. It therefore contains a conjugate of the short
root outside G₂(2)′. The offender subgroup already contains that derived
component, so its image is all of G₂(2), and injectivity makes it the whole
original actor. The FF supplement is consequently the moving part plus
vectors fixed by the whole actor. Both lie in the original omega orbit.
Conjugation transports their equality to every original-color vertex.

This supplies the X = Z clause of MS93 (3.2)(vii) needed in the nonfixed
branch of (3.8); it does not identify either group with its moving subgroup
or with its residual-fixed kernel. The private import reuses the checked
order exclusion for the four exceptional FF supplement rows.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.2)(vii), printed p.863, and (3.8), printed p.879; AS B.5.1(5).
The octonion action retains the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction
open ChapterB.QuasisimpleSource ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "H" => (L ⊔ R : Subgroup G)
local notation "C" => quotientComponent (L := L) (R := R)
local notation "X" => omegaCenterIn (pCore 2 H)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h e

/-- The actual central-omega offenders generate the entire original actor,
including its nontrivial coset outside the derived G₂ component. -/
theorem centralOmega_offenderSubgroup_top : offenderSubgroup (centralOmegaAction h e) = ⊤ := by
  let := (quotientComponent_structure h e).1
  let := (quotientComponent_structure h e).2.1
  let := (quotientComponent_structure h e).2.2.1
  let ρ := centralOmegaAction h e
  obtain ⟨hCJ,_⟩ := SourceCompletion.ff_socle_source_conclusion ρ C
    (quotientComponent_structure h e).2.2.2 (quotientComponent_sqtk h)
    (centralOmegaAction_faithful h e) (central_omega_FF h e)
  obtain ⟨f,hf,hfC,p,hp,_,he⟩ := centralOmega_natural_coordinates h e
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp (central_omega_FF h e)
  let τ := Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2)
  have hbound := fixedCodim_le_of_equivariant_surjection ρ (τ.comp f) p hp he A
  have hoff : IsOffender (τ.comp f) A := ⟨hA.1,hbound.trans (hA.isOffender ρ).2⟩
  have hAf := hoff.map_equivariant (τ.comp f) τ f hf
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl)
  have hnat := hAf.map_equivariant τ (Atlas.G2.Natural.action (ZMod 2))
    (MonoidHom.id _) Function.injective_id
    (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).symm
    (fun g v => (Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).symm.isIntertwining g v)
  rw [map_id] at hnat
  obtain ⟨g,_,hg⟩ := Atlas.G2.NaturalOffenders.natural_offender_rootPair
    (n := 1) (by norm_num) (by decide) _ hnat
  have hout : g * Atlas.G2.rootC 1 * g⁻¹ ∉ commutator (Atlas.G2.Model (ZMod 2)) := by
    intro hgD
    have hc := (inferInstance : (commutator (Atlas.G2.Model (ZMod 2))).Normal).conj_mem' _ hgD g
    apply Atlas.G2.Natural.BinaryNormalizer.rootC_not_mem_derived
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hc
  have htop : (offenderSubgroup ρ).map f = ⊤ :=
    Atlas.G2.Natural.BinaryNormalizer.eq_top_of_derived_le
      (by
        change commutator (Atlas.G2.Model (ZMod 2)) ≤ _
        rw [←hfC]
        exact map_mono hCJ)
      (map_mono (hA.le_offenderSubgroup ρ) hg) hout
  apply top_unique
  intro x _
  obtain ⟨y,hy,hyx⟩ := (show f x ∈ (offenderSubgroup ρ).map f from htop.symm ▸ mem_top _)
  exact hf hyx ▸ hy

/-- The FF supplement is fixed by the whole original actor, rather than
only by the distinguished derived component. -/
theorem centralOmega_moved_sup_invariants :
    moved (centralOmegaAction h e) C ⊔ invariants (centralOmegaAction h e) = ⊤ := by
  let := (quotientComponent_structure h e).1
  let := (quotientComponent_structure h e).2.1
  let := (quotientComponent_structure h e).2.2.1
  let ρ := centralOmegaAction h e
  obtain ⟨hCJ,⟨c⟩⟩ := SourceCompletion.ff_socle_source_conclusion ρ C
    (quotientComponent_structure h e).2.2.2 (quotientComponent_sqtk h)
    (centralOmegaAction_faithful h e) (central_omega_FF h e)
  have hc' : Nat.card ((C).subgroupOf (offenderSubgroup ρ)) = 6048 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCJ).toEquiv).trans (quotientComponent_card h e)
  have hs : c.sectionData.space.toSubmodule ⊔
      invariants (ρ.comp (offenderSubgroup ρ).subtype) = ⊤ := by
    rcases c.clause_five with hs | hs
    · exact hs
    · exact (supplement_card_ne _ hc' hs.2.1).elim
  have hm := c.sectionData.space_eq
  rw [moved_comp_map,map_subgroupOf_eq_of_le hCJ] at hm
  have hi : invariants (ρ.comp (offenderSubgroup ρ).subtype) = invariants ρ := by
    ext v
    constructor
    · intro hv g
      exact hv ⟨g, (centralOmega_offenderSubgroup_top h e).symm ▸ mem_top g⟩
    · intro hv g
      exact hv g
  rwa [hm,hi] at hs

/-- The original orbit of the edge center exhausts the whole central-omega
layer; the equality uses the literal subgroups of L joined with R. -/
theorem omegaOrbit_eq_centralOmega : MSCentralOrbit.omegaOrbit T = X := by
  apply le_antisymm (MSCentralOrbit.omegaOrbit_le_centralOmega T
    (core_le_edge h) (core_self_centralizing h))
  intro x hx
  let ρ := centralOmegaAction h e
  obtain ⟨w,hw,z,hz,heq⟩ := Submodule.mem_sup.mp
    ((centralOmega_moved_sup_invariants h e).symm ▸
      (Submodule.mem_top : Additive.ofMul (⟨x,hx⟩ : X) ∈ (⊤ : Submodule (ZMod 2) (Additive X))))
  have hwK : (w.toMul : H) ∈ ⁅X,K⁆ := by
    have hw0 : w ∈ NormalElementaryQuotient.commutatorSpace X K := by
      rw [NormalElementaryQuotient.commutatorSpace_eq X
        (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
        ((QuotientGroup.ker_mk' _).trans (central_omega_centralizer h e).symm) K]
      exact hw
    exact hw0
  have hwW : (w.toMul : H) ∈ MSCentralOrbit.omegaOrbit T := by
    rw [←initialCore_eq h e] at hwK
    exact commutator_le_left _ _ hwK
  have hzT : (z.toMul : H) ∈ omegaCenterIn T := by
    obtain ⟨hzQ,_,hz2⟩ := (mem_omegaCenterIn_iff _ _).mp z.toMul.property
    refine (mem_omegaCenterIn_iff _ _).mpr ⟨core_le_edge h hzQ,?_,hz2⟩
    intro t ht
    have hh := congrArg (fun v : Additive X => (v.toMul : H))
      (hz (QuotientGroup.mk' (pCore 2 H) t))
    rw [centralOmegaAction_apply h e] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have heq' : (w.toMul : H) * (z.toMul : H) = x :=
    congrArg (fun v : Additive X => (v.toMul : H)) heq
  exact heq' ▸ (MSCentralOrbit.omegaOrbit T).mul_mem hwW (subset_normalClosure hzT)

open Stellmacher.PushingUp.AmalgamGraph BinaryMS.MS93

/-- The X = Z clause of the G₂ source row at every original-color vertex. -/
theorem omegaCenter_eq_seed (a : Vertex T) (ha : color T a = false) :
    BinaryMS.MS93.X T a = Z T a := by
  have hbase : BinaryMS.MS93.X T (alpha T) = Z T (alpha T) := by
    rw [BinaryMS.MS93.X, Q_alpha T (edge_two_group h) (core_le_edge h),
      omegaCenter_map _ _ (embedM_injective T), MSCentralOrbit.Z_alpha_eq_omegaOrbit,
      omegaOrbit_eq_centralOmega h e]
    rfl
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  have hx := X_act T g (alpha T)
  have hz := Z_act T g (alpha T)
  simp only [alpha,act_mVertex,one_mul] at hx hz hbase
  rw [hx,hz,hbase]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction
