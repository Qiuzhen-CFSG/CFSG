module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.Contracts
public import Theory.GroupTheory.PrimeOrderCentralizerEscape
public import Theory.GroupTheory.MaximalTwoLocalCore
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup

/-!
# Constructing the second normalizer and its C.2.3 setup

The two prime-order centralizer identities from the quintic module argument
force the original critical-pair element to normalize K₂. Its escape from
Mc therefore proves N_G(K₂) is not contained in Mc. The actual intersection
core equality makes O₂(Mc) radical in N_G(K₂). Maximal two-locality controls
all its characteristic normalizers, and its normal closure in the
intersection is itself, supplying the literal Sylow clause of C.2.3.

The module geometry is still an explicit intermediate premise. The
escaping-component construction and the C.2.4/C.2.7 contradictions are
separate obligations, not consequences asserted by this file.

Source: Aschbacher--Smith 14.6.15, printed p.1034.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open Chapter1.RadicalExclusions
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem pushingUp_of_core_intersection {κ : GroupClass}
    (Mc N : Subgroup G) (hmax : IsMaximalTwoLocal Mc) (hsq : IsSQTK κ N)
    (hcore : (Mc ⊓ N).pCoreIn 2 = Mc.pCoreIn 2) :
    PushingUpSetup κ N (Mc.pCoreIn 2) (Mc ⊓ N) := by
  let R := Mc.pCoreIn 2
  let B := Mc ⊓ N
  have hRB : R ≤ B := by
    change Mc.pCoreIn 2 ≤ Mc ⊓ N
    rw [←hcore]
    exact pCoreIn_le 2 _
  have hRN : R ≤ N := hRB.trans inf_le_right
  have hne : R ≠ ⊥ := maximalTwoLocal_core_ne_bot hmax
  have hnorm : normalizer (R : Set G) = Mc := maximalTwoLocal_normalizer_core hmax
  have hcontrol : R.characteristicNormalizerClosure ≤ Mc :=
    (maximalTwoLocal_characteristicNormalizer_core hmax).le
  refine ⟨hsq,hRN,inf_le_right,?_,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro hb
      apply hne
      change R.subgroupOf N = ⊥ at hb
      have hh := congrArg (map N.subtype) hb
      rwa [map_subgroupOf_eq_of_le hRN,Subgroup.map_bot] at hh
    · apply map_injective N.subtype_injective
      change ((normalizer (R.subgroupOf N : Set N)).pCoreIn 2).map N.subtype = _
      rw [map_pCoreIn_of_injective 2 _ N.subtype N.subtype_injective,
        ←subgroupOf_normalizer_eq hRN,subgroupOf_map_subtype,
        hnorm,hcore,map_subgroupOf_eq_of_le hRN]
  · have hc := characteristicNormalizerClosure_subgroupOf_le hRN hcontrol
    intro x hx
    exact ⟨hc hx,x.property⟩
  · have hn : (R.subgroupOf B).Normal := by
      change ((Mc.pCoreIn 2).subgroupOf B).Normal
      rw [←hcore]
      change ((pCore 2 B).map B.subtype |>.comap B.subtype).Normal
      rw [comap_map_eq_self_of_injective B.subtype_injective]
      infer_instance
    let := hn
    rw [normalClosure_eq_self,map_subgroupOf_eq_of_le hRB]
    exact Chapter1.isSylowIn_iff.mpr
      ⟨isPGroup_pCoreIn 2 Mc,le_rfl,fun _ _ hlo hhi => le_antisymm hhi hlo⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (H1 H2 : Subgroup G)

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (c : CriticalPair
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH)
      a Mc H1)
    (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) c.endpoint.representative)

/-- The actual G₂=N_G(K₂) escapes Mc and satisfies the original C.2.3,
conditional only on the preceding module/centralizer geometry. The
conjugator is precisely the one in the supplied original critical pair. -/
theorem source_secondNormalizer_setup :
    c.endpoint.representative ∈ normalizer (d.K2 : Set G) ∧
      ¬ normalizer (d.K2 : Set G) ≤ Mc ∧
      PushingUpSetup KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G))
        (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G)) := by
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hg := mem_normalizer_of_primeOrder_centralizers 5 (centralInvolutions T)
    (residualClosure H Mc) d.K2 d.U1 c.endpoint.representative d.second_generated
    (d.second_le.trans_eq hMc) (c.point_le.trans d.first_support_le)
    d.first_centralizes d.point_closure d.conjugate_point_closure
  refine ⟨hg,fun hn => c.outside (hn hg),?_⟩
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  let N := normalizer (d.K2 : Set G)
  have hcore_le : d.K2.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 d.K2)
      ((pCoreIn_le 2 d.K2).trans d.K2.le_normalizer)
      (normalizer_le_normalizer_characteristic_image d.K2 (pCore 2 d.K2))
  have hN : N ∈ Chapter1.H G := by
    intro hb
    have hz : centralInvolutions T = ⊥ := bot_unique (hb ▸ d.point_core.trans hcore_le)
    have hc := plane_centralInvolutions_card T M hM.1.2 hcard e
    have hc0 : Nat.card (centralInvolutions T) = 1 := (eq_bot_iff_card _).mp hz
    omega
  exact pushingUp_of_core_intersection Mc N hmax (sqtk_of_mem_H hG hN) d.intersection_core

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
