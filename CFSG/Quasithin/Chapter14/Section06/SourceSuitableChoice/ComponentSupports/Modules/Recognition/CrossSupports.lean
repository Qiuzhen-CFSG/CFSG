module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LiftedSeeds
public import Theory.Representation.BinaryConjugationSection.EmbeddedCommutant
public import Theory.Representation.BinaryConjugationSection.FixedKernel
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.IrreducibleFixedPoints

/-!
# Cross-centralization and separation of full terminal natural supports

A relative component normalizes every other component's full commutator
support. Their images commute in the literal H/O2(H). Embed a marked
natural--dual support in the original U_H/Z; its invertible commutant is
trivial, so the other component fixes it modulo Z. Perfectness lifts this
to pointwise fixation of the whole original support. The absence of fixed
vectors in the natural--dual sum then makes distinct supports meet exactly
in Z.

The input is a marking of the full support [U_H,K]/Z, not a constituent
seed. The following PairedSupportConsumer applies these results to the
literal waiting critical-pair theorem. Full-support recognition remains
with qt-e-suitable-component-supports, including the normal field-four
exclusion; original14.6.18 remains hsolv for qt-e-14625-source.

Source: Aschbacher--Smith14.6.22(2),14.6.23(3), printed p.1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
universe u
variable {G : Type u} [Group G] [Finite G]
/-- Distinct original components normalize one another. -/
private theorem relative_component_normalizes {H K C : Subgroup G}
    (hKH : K ≤ H) (hCH : C ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent) :
    C ≤ normalizer (K : Set G) := by
  have hh := (map_mono ((le_cComponentLayer hC).trans (cComponentLayer_le_normalizer hK))
    (f := H.subtype)).trans (le_normalizer_map H.subtype)
  simpa only [map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hKH] using hh

private theorem natural_dual_fixed_zero
    (v : BinaryLinearThree.NaturalDual.Space)
    (hv : ∀ g, BinaryLinearThree.NaturalDual.action g v = v) : v = 0 := by
  let : IsIrreducible BinaryLinearThree.W := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible BinaryLinearThree.W.dual := BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  have hn := OneCohomology.fixed_eq_bot_of_irreducible_finrank BinaryLinearThree.W
    (by simp only [Module.finrank_fin_fun]; decide)
  have hd := OneCohomology.fixed_eq_bot_of_irreducible_finrank BinaryLinearThree.W.dual
    (by rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun]; decide)
  have hn' : v.1 ∈ OneCohomology.fixed BinaryLinearThree.W := fun g => congrArg Prod.fst (hv g)
  have hd' : v.2 ∈ OneCohomology.fixed BinaryLinearThree.W.dual := fun g => congrArg Prod.snd (hv g)
  rw [hn,Submodule.mem_bot] at hn'
  rw [hd,Submodule.mem_bot] at hd'
  exact Prod.ext hn' hd'

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- A full marked natural--dual support is centralized by every other
original component. Commutation is used only after the actual two-core quotient. -/
theorem source_cross_of_natural_dual_support
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent)
    (hne : K ≠ C)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (d : BinaryConjugationSection K ⁅conjugateSpanBy (localModule T M) H,K⁆
      (centralInvolutions T) (BinaryLinearThree.NaturalDual.action.comp
        (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) :
    ⁅⁅conjugateSpanBy (localModule T M) H,K⁆,C⁆ = ⊥ := by
  obtain ⟨hU,a,_⟩ := source_rankTwo_bounded_placed_action
    hG T hempty hM hunique hmany hcard e hab H hH
  let := hU
  let U := conjugateSpanBy (localModule T M) H
  let W := ⁅U,K⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le
    (le_normalizer_iff_commutator_le_left.mp (hKH.trans a.normalizes))
  let : Group.IsPerfect (C.subgroupOf H) := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hCH).toMonoidHom) (subgroupOfEquivOfLe hCH).surjective
  have hp := source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  have hCZ : C ≤ centralizer (centralInvolutions T : Set G) := hCH.trans
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes
  apply (originalSection a).centralizes_of_embedded_trivial_commutant d hKH hCH
    (hp.2.1.trans inf_le_left) ((le_inf hCH (relative_component_normalizes hKH hCH hK hC)).trans hp.2.2) hCZ
  · intro c k
    let q := QuotientGroup.mk' (pCore 2 H)
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    have hne' : actorImage H C ≠ actorImage H K := by
      intro he
      have hh := congrArg (Subgroup.map H.subtype) (hC.eq_of_map_quotient_eq hK (pCore 2 H) he)
      rw [map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hKH] at hh
      exact hne hh.symm
    have hc := (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
      H hH C hCH hC).commutator_eq_bot_of_ne
        (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
          H hH K hKH hK) hne'
    have he := (commutator_eq_bot_iff_le_centralizer.mp hc)
      (show q (inclusion hCH c) ∈ actorImage H C from ⟨inclusion hCH c,c.property,rfl⟩)
      (q (inclusion hKH k))
      (show q (inclusion hKH k) ∈ actorImage H K from ⟨inclusion hKH k,k.property,rfl⟩)
    change a.representation (q (inclusion hCH c)) * a.representation (q (inclusion hKH k)) =
      a.representation (q (inclusion hKH k)) * a.representation (q (inclusion hCH c))
    rw [←a.representation.map_mul,←a.representation.map_mul,he]
  · intro f hf
    apply BinaryLinearThree.NaturalDual.centralizer_eq_one f
    intro g v
    obtain ⟨k,hk⟩ := (eK.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) g
    change eK ((QuotientGroup.mk' (pCore 2 K)) k) = g at hk
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,hk] using hf k v
/-- Two fully marked original supports have both cross-centralizations and
intersection exactly the original central subgroup. -/
theorem source_pair_geometry_of_natural_dual_supports
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent)
    (hne : K ≠ C)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (d : BinaryConjugationSection K ⁅conjugateSpanBy (localModule T M) H,K⁆
      (centralInvolutions T) (BinaryLinearThree.NaturalDual.action.comp
        (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (dC : BinaryConjugationSection C ⁅conjugateSpanBy (localModule T M) H,C⁆
      (centralInvolutions T) (BinaryLinearThree.NaturalDual.action.comp
        (eC.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))))) :
    ⁅⁅conjugateSpanBy (localModule T M) H,K⁆,C⁆ = ⊥ ∧
      ⁅⁅conjugateSpanBy (localModule T M) H,C⁆,K⁆ = ⊥ ∧
      ⁅conjugateSpanBy (localModule T M) H,K⁆ ⊓
        ⁅conjugateSpanBy (localModule T M) H,C⁆ = centralInvolutions T := by
  have hc := source_cross_of_natural_dual_support
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K C hKH hCH hK hC hne eK d
  have hc' := source_cross_of_natural_dual_support
    hG T hempty hM hunique hmany hcard e hab hsolv H hH C K hCH hKH hC hK hne.symm eC dC
  refine ⟨hc,hc',le_antisymm ?_ (le_inf d.kernel_le dC.kernel_le)⟩
  apply (inf_le_inf_left _ (commutator_eq_bot_iff_le_centralizer.mp hc')).trans
  apply d.centralizer_le_kernel_of_fixed_eq_zero
  intro v hv
  apply natural_dual_fixed_zero v
  intro k
  obtain ⟨l,rfl⟩ := (eK.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) k
  exact hv l

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
