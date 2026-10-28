module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.QuadraticActors
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Residuals
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Decomposition
public import Theory.Representation.AlternatingSixPairedCovers.SectionMarking
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.GroupTheory.CComponent.ResidualMarking
public import Theory.GroupTheory.SubgroupConjugation.PairPermutation
public import Theory.Representation.BinaryConjugationSection.SupportSpan

/-!
# Excluding A₆ from the original paired component sections

The actual isomorphism K/O₂(K) ≃ A₆ embeds that same component into
Mc/O₂(Mc). The residual identity gives normality, and the radical-free layer
proves its centralizer trivial. The A₆ outer action supplies Mc = KT.
Gaschütz then gives the fixed supplement to the actual support
[U,K] = A ∨ B. The original Sylow orbit and its exchanging element give the
whole group's simultaneous permutation of A and B.

Both original coordinate quotients embed into the same literal U/Z, so the
paired-cover actor theorem applies without a marking, whole-module action,
fixed-span, critical-endpoint or quadratic-actor callback. No directness of
the two covering supports or their central kernels is required.

The full natural-or-cover sections and their support identity are the genuine
14.6.22 inputs still owned by qt-e-suitable-component-supports. The existing
component alternative supplies K = Mc∞; original 14.6.18 remains explicit for
qt-e-14625-source. The two-component markings and final 14.6.24 assembly remain
with qt-e-suitable-component-marking, and final suitable choice remains with
qt-e-suitable-existence. This theorem does not claim unconditional 14.6.24.

Source: Aschbacher--Smith, 14.6.21--24, printed pp.1037--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G V V' : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V'] [Module (ZMod 2) V']

/-- Exclude the single A₆ alternative from the literal paired source covers.
All quotient-action and marking premises of the critical obstruction are proved
from the original component, support identity and Sylow orbit. -/
theorem source_no_alternatingSix_of_original_sections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (K : Subgroup G) (hKres : (solvableResidual Mc).map Mc.subtype = K)
    (hK : (K.subgroupOf Mc).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (A B : Subgroup G)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (σ' : Representation (ZMod 2) (alternatingGroup (Fin 6)) V')
    (d : BinaryConjugationSection K A (centralInvolutions T)
      (σ.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (d' : BinaryConjugationSection K B (centralInvolutions T)
      (σ'.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (hm : BinaryPermutation.SixCover.IsNaturalOrCore σ (alternatingGroup (Fin 6)).subtype)
    (hm' : BinaryPermutation.SixCover.IsNaturalOrCore σ'
      (BinaryAlternatingSix.diagramAut.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype))
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hsupport : ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B)
    (hpair : ∀ x ∈ (T : Subgroup G), A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B)
    (s : G) (hs : s ∈ (T : Subgroup G)) (hsB : A.map (MulAut.conj s).toMonoidHom = B) :
    False := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let Z := centralInvolutions T
  let π := QuotientGroup.mk' (pCore 2 Mc)
  have hKM : K ≤ Mc := hKres ▸ map_subtype_le _
  have hres : solvableResidual Mc = K.subgroupOf Mc := by
    rw [←hKres]
    exact (comap_map_eq_self_of_injective Mc.subtype_injective _).symm
  let j := subgroupOfEquivOfLe hKM
  let ej := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let eJ := ej.trans eK
  obtain ⟨κ,hκ,hr,hmark⟩ := exists_twoCore_component_marking (K.subgroupOf Mc) hK eJ
  have hrad := ComponentSupports.Classification.source_radical_eq_core
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  obtain ⟨hn,hcent⟩ := residual_component_marking_properties hrad (K.subgroupOf Mc) hres κ hr
  let f := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hκf (k : K) : π (inclusion hKM k) = κ (f k) := by
    exact (hmark (j.symm k)).symm
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  let : (Z.subgroupOf U).Normal := inferInstance
  obtain ⟨ρ,c,_⟩ := BinaryConjugationSection.exists_descended_actor Mc U Z h.UH_le_H
    (h.point_lt.le.trans (le_conjugateSpanBy _ _)) (le_normalizer_conjugateSpanBy _ _)
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) π
    (QuotientGroup.mk'_surjective _) (by
      intro a ha b hb
      have hcore : (a:G) ∈ Mc.pCoreIn 2 :=
        mem_map_of_mem Mc.subtype ((QuotientGroup.eq_one_iff a).mp ha)
      have hc := h.commutator_UH_QH_le_point (commutator_mem_commutator hb hcore)
      simpa only [commutatorElement_inv] using Z.inv_mem hc)
  have hUZ : U ≤ normalizer (Z : Set G) :=
    h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have heR : (K.subgroupOf Mc).map π = solvableResidual (Mc ⧸ pCore 2 Mc) := by
    rw [←hres,map_solvableResidual_eq π (QuotientGroup.mk'_surjective _)]
  let eR := (MulEquiv.subgroupCongr heR.symm).trans
    ((cComponentTwoCoreQuotientEquiv hK).symm.trans eJ)
  have hmodels : ComponentSupports.Classification.ResidualQuotientModels
      (solvableResidual (Mc ⧸ pCore 2 Mc)) := Or.inr (Or.inl ⟨eR⟩)
  obtain ⟨_,hprod⟩ := ComponentSupports.Classification.terminal_residual_structure_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv hmodels
  rw [hKres] at hprod
  have hsum := ComponentSupports.source_component_sum_sup_fixed
    hG T hempty hM hunique hmany hcard e hab (ρ.comp π) c
    (fun (_ : Unit) => K) (fun _ => hKM) (by
      intro m
      have hmprod : (m:G) ∈ (K:Set G) * ((T:Subgroup G):Set G) := hprod ▸ m.property
      obtain ⟨k,hk,t,ht,he⟩ := hmprod
      refine ⟨⟨k,hKM hk⟩,?_,⟨t,h.T_le_H ht⟩,ht,Subtype.ext he⟩
      simpa only [iSup_const] using
        (show (⟨k,hKM hk⟩ : Mc) ∈ K.subgroupOf Mc from hk))
  simp only [iSup_const] at hsum
  rw [hsupport] at hsum
  have hcover := c.le_sup_fixed_preimage_of_spanning_image (A ⊔ B)
    (d.kernel_le.trans le_sup_left) hUZ hsum
  have hpairH (x : G) (hx : x ∈ Mc) :
      A.map (MulAut.conj x).toMonoidHom = A ∨ A.map (MulAut.conj x).toMonoidHom = B := by
    have hxprod : x ∈ (K:Set G) * ((T:Subgroup G):Set G) := hprod ▸ hx
    obtain ⟨k,hk,t,ht,rfl⟩ := hxprod
    have hmap : (MulAut.conj k).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (k*t)).toMonoidHom := by ext a; simp [MulAut.conj_apply,mul_assoc]
    rw [←hmap,←Subgroup.map_map]
    rcases hpair t ht with ha | hb
    · rw [ha]
      exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (d.normalized hk))
    · rw [hb]
      exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (d'.normalized hk))
  have hperm := pair_permutation_of_conjugate_orbit Mc A B hpairH s (h.T_le_H hs) hsB
  obtain ⟨C,_,_,_⟩ := AlternatingSixPairedCovers.exists_data_of_sections
    π (QuotientGroup.mk'_surjective _) κ hκ hn hcent f hf c σ σ' d d' hKM hAU hBU
    hκf hm hm' hUZ hcover hperm
  let s : ConjugationSection Mc U Z ρ := {
    le := c.section_le
    line_le := c.kernel_le
    normalizes := c.normalized
    centralizes := h.H_centralizes
    quotient := c.coordinates
    surjective := c.onto
    kernel := c.kernel_eq
    conjugates := fun a u => (c.equivariant a u).symm }
  exact terminal_obstruction_of_paired_covers hG T hempty hM hunique hmany hcard e hab s C
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
