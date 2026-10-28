module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.CoreGeometry
public import Theory.GroupTheory.MaximalTwoLocalCore
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.PCoreCentralizerOvergroup

/-!
# The literal no-index second normalizer at an index-two intersection

The residual-closure branch already makes O₂(Mc) normalize each literal
factor residual. If its normalizer has index two in Mc, the intersection
has the same two-core. This constructs the exact C.2.3 setup and proves
characteristic two in the actual N_G(Kk), using its proved proper-local
SQTK property. No factor-join index or equality with the permutation kernel
is used. The ambient intersection index remains an explicit hypothesis;
these statements do not establish it or exclude the quintic branch.

Source: Aschbacher--Smith 14.6.15, printed p.1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

open Chapter1.RadicalExclusions ChapterA.Section04

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

private theorem characteristicTwo_of_core_intersection (Mc N Z : Subgroup G)
    (hMc : Mc ∈ Chapter1.He G)
    (hcore : (Mc ⊓ N).pCoreIn 2 = Mc.pCoreIn 2)
    (hZ : Z ≤ N.pCoreIn 2) (hcentral : centralizer (Z : Set G) = Mc) :
    generalizedFitting N = pCore 2 N := by
  let B := Mc ⊓ N
  have hB : B ∈ Chapter1.He G := by
    change B ⊓ centralizer (B.pCoreIn 2 : Set G) ≤ B.pCoreIn 2
    change Mc ⊓ centralizer (Mc.pCoreIn 2 : Set G) ≤ Mc.pCoreIn 2 at hMc
    change (Mc ⊓ N) ⊓ centralizer ((Mc ⊓ N).pCoreIn 2 : Set G) ≤ (Mc ⊓ N).pCoreIn 2
    rw [hcore]
    exact (inf_le_inf_right _ inf_le_left).trans hMc
  have hcB : centralizer (pCore 2 (B.subgroupOf N) : Set (B.subgroupOf N)) ≤
      pCore 2 (B.subgroupOf N) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe
      (show B ≤ N from inf_le_right))).mpr (Chapter1.mem_He_iff.mp hB)
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply centralizer_pCore_le_of_overgroup 2 (B.subgroupOf N) hcB
  intro x hx
  refine ⟨?_,x.property⟩
  rw [←hcentral]
  intro z hz
  obtain ⟨q,hq,hqz⟩ := hZ hz
  have he := congrArg Subtype.val (hx q hq)
  change (q : G) * (x : G) = (x : G) * (q : G) at he
  change (q : G) = z at hqz
  rwa [hqz] at he

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs hp w

/-- The residual-normalizer intersection has the same core as Mc once its
ambient index two is proved. No index of the actor join occurs. -/
theorem source_quintic_intersection_core
    (hc : residualClosure J Mc = residual J) (k : d.Index)
    (hi : (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 2) :
    (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).pCoreIn 2 = Mc.pCoreIn 2 := by
  let B := Mc ⊓ normalizer (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)
  let : (B.subgroupOf Mc).Normal := normal_of_index_eq_two hi
  have hQB : Mc.pCoreIn 2 ≤ B := le_inf (pCoreIn_le 2 Mc)
    (source_quintic_core_normalizes_factor hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w hc k)
  exact le_antisymm (pCoreIn_mono_of_normalizes inf_le_left
    (le_normalizer_of_normal_subgroupOf (show B ≤ Mc from inf_le_left)))
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Mc) hQB
      (inf_le_left.trans (Mc.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))))

/-- The actual C.2.3 and characteristic-two consumers use the proved local
core geometry. The remaining hypothesis is the index in Mc, not the index
of the original factor join in J. -/
theorem source_quintic_secondNormalizer_setup_of_index
    (hc : residualClosure J Mc = residual J) (k : d.Index)
    (hi : (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 2) :
    let N := normalizer (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)
    PushingUpSetup KnownSimple.IsKnownSimple N (Mc.pCoreIn 2) (Mc ⊓ N) ∧
      generalizedFitting N = pCore 2 N := by
  let N := normalizer (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)
  have hcore : (Mc ⊓ N).pCoreIn 2 = Mc.pCoreIn 2 :=
    source_quintic_intersection_core hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w hc k hi
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hHe : Mc ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (hG.evenCharacteristic T Mc hmax hTMc)
  exact ⟨pushingUp_of_core_intersection Mc N hmax
    (source_quintic_secondNormalizer_sqtk hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d k) hcore,
    characteristicTwo_of_core_intersection Mc N (centralInvolutions T) hHe hcore
      (source_quintic_secondNormalizer_point_core hG T hempty hM hu hmany hcard e hab
        J hJ hs a f d k) hMc.symm⟩

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
