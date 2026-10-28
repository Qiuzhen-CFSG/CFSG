module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Pair
public import CFSG.Quasithin.ChapterA.Section05To06.Ordering
/-!
# Actual maximal-local ordering and the exclusion of the distinguished maximum

Characteristic two makes each original V(M) elementary and nontrivial, so
maximality of M identifies M with N_G(V(M)). Thus the source A.5 relation
is a genuine finite partial order on the actual maximal local overgroups,
and every member lies below an ordering maximum. If its only maximum
were Mc, the actual factorizations and C_G(Z) ≤ Mc would put every maximal
local inside Mc, contradicting the original multiplicity hypothesis.

The last theorem applies the centralizing 14.1.11 factorization to the
literal A.5 ordering, retaining the same characteristic subgroup of Baum(T)
and its full normalizer. No ordering-maximality certificate is an input.
Source: Aschbacher–Smith A.5.2–5 and 14.1.9–12, printed pp.61–63,977–979.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_local_eq_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalLocals T) :
    M = normalizer (sourceModule T M : Set G) := by
  let : IsElementaryAbelian 2 (localModule T M) :=
    localModule_elementary_from_source hG T ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  have hne : sourceModule T M ≠ ⊥ := by
    intro he
    have hZ : centralOmega T = ⊥ := bot_unique (he ▸ le_conjugateSpanBy (centralOmega T) M)
    let : Nontrivial (T : Subgroup G) := (nontrivial_iff_ne_bot _).mpr (MainForward.sylow_ne_bot hG T)
    exact omega_center_ne_bot T.isPGroup'
      ((((omega₁ (center (T : Subgroup G)) (p := 2)).map (center (T : Subgroup G)).subtype).map_eq_bot_iff_of_injective
        (T : Subgroup G).subtype_injective).mp hZ)
  have hp : IsPGroup 2 (sourceModule T M) := IsElementaryAbelian.isPGroup 2 (localModule T M)
  exact hM.1.eq_of_le ⟨_,hne,hp,rfl⟩ (le_normalizer_conjugateSpanBy _ _)

theorem source_exists_ordering_maximal_above
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalLocals T) :
    ∃ N : Subgroup G, IsOrderingMaximal T N ∧ OrderingLE T M N := by
  let A := {N : Subgroup G // N ∈ maximalLocals T}
  let order : PartialOrder A :=
    { le := fun H K => OrderingLE T H.1 K.1
      lt := fun H K => OrderingLE T H.1 K.1 ∧ ¬ OrderingLE T K.1 H.1
      le_refl := fun _ => conjugateSpanLE_refl _ _
      le_trans := fun H _ _ => conjugateSpanLE_trans (source_local_eq_normalizer hG T H.2)
      le_antisymm := fun H K hHK hKH => Subtype.ext (conjugateSpanLE_antisymm
        (source_local_eq_normalizer hG T H.2) (source_local_eq_normalizer hG T K.2) hHK hKH) }
  obtain ⟨N,hMN,hN⟩ := @Finite.exists_le_maximal A order.toPreorder inferInstance
    (fun _ => True) (⟨M,hM⟩ : A) trivial
  refine ⟨N.1,⟨N.2,?_⟩,hMN⟩
  intro K hK hNK
  have hh := hN.2
  have hKN : OrderingLE T K N.1 := @hh (⟨K,hK⟩ : A) trivial hNK
  exact conjugateSpanLE_antisymm (source_local_eq_normalizer hG T hK)
    (source_local_eq_normalizer hG T N.2) hKN hNK

theorem source_lemma_14_1_9
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hunique : ∀ N : Subgroup G, IsOrderingMaximal T N → N = M) : M ≠ Mc := by
  intro he
  have hC : centralizer (centralInvolutions T : Set G) ≤ Mc := centralizer_le_partner T hu
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  have hall (N : Subgroup G) (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) : N = Mc := by
    obtain ⟨K,hK,hNK⟩ := source_exists_ordering_maximal_above hG T hN
    have heK : K = Mc := (hunique K hK).trans he
    rw [heK] at hNK
    apply hN.1.eq_of_le hMc.1
    intro n hn
    obtain ⟨a,ha,c,hc,rfl⟩ := hNK n hn
    apply Mc.mul_mem ha.2
    apply hC
    exact centralizer_le (le_conjugateSpanBy (centralOmega T) N) hc.2
  obtain ⟨N,hN,K,hK,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
  exact hne ((hall N hN).trans (hall K hK).symm)

/-- The actual centralizing factorization covers M in the A.5 ordering
whenever the chosen characteristic normalizer lies in the comparison group. -/
theorem source_centralizing_ordering
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M P : Subgroup G} (hM : M ∈ maximalLocals T)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (C : Subgroup (ChapterB.baumann (T : Subgroup G))) [C.Characteristic]
    (hNP : normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ≤ P) :
    OrderingLE T M P := by
  let V := localModule T M
  let N := M ⊓ centralizer (V : Set G)
  let A := M ⊓ normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G)
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  let := (localModule_reduced_from_source hG T hH).normal
  have hVM : V ≤ M := conjugateSpanBy_le_self
    (fun z hz => hM.2 ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  have hN : N.subgroupOf M = centralizer (V.subgroupOf M : Set M) := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show N ≤ M from inf_le_left),map_centralizer_subtype,
      map_subgroupOf_eq_of_le hVM]
  let : (N.subgroupOf M).Normal := hN ▸ inferInstance
  have hgen : A.subgroupOf M ⊔ N.subgroupOf M = ⊤ := by
    rw [←subgroupOf_sup (show A ≤ M from inf_le_left) (show N ≤ M from inf_le_left),sup_comm]
    rw [←source_centralizing_factorization hG T hM hJ C,subgroupOf_self]
  intro m hm
  have hmem : (⟨m,hm⟩ : M) ∈ A.subgroupOf M ⊔ N.subgroupOf M := by
    rw [hgen]; exact mem_top _
  obtain ⟨a,ha,c,hc,he⟩ := mem_sup_of_normal_right.mp hmem
  exact ⟨a,⟨a.property,hNP ha.2⟩,c,hc,congrArg M.subtype he⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
