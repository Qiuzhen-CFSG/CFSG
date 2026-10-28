module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsCentralizer
public import Stellmacher.Recognition.Parrott.DerivedNormalizerSolvable

/-!
# Solvability of the Sylow overgroups in the original Tits branch

The empty faithful local family makes the solvable residual of every member
of H(T) centralize the central omega subgroup of its two-core. Characteristic
two puts the original central involution in that omega subgroup. If its full
centralizer is solvable, so is the residual, and therefore the local group.

In the original Tits branch the full centralizer is the first Tits parabolic.
This supplies local solvability from the actual source hypotheses, without
assuming that the ambient group is an N₂-group.

Source: Aschbacher--Smith 14.1.3 and 14.2.21--22, printed pp.976 and 988--989;
Parrott (1972), the normalizers in Lemmas 2 and 6, pp.673 and 677.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- A solvable central-involution centralizer forces solvability of every
original local Sylow overgroup when the faithful component family is empty. -/
theorem local_solvable_of_empty_faithful_of_solvable_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (z : G) (hz : z ∈ centralInvolutions T)
    (hC : Group.IsSolvable (centralizer ({z} : Set G)))
    (K : Subgroup G) (hK : K ∈ Chapter1.HOver G (T : Set G)) :
    Group.IsSolvable K := by
  let : Group.IsSolvable (centralizer ({z} : Set G)) := hC
  obtain ⟨hzT,hz2,hzcentral⟩ :=
    (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
  let zK : K := ⟨z,hK.2 hzT⟩
  have hcoreT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow K (T.subtype hK.2)
    change K.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf K).map K.subtype at hh
    rwa [map_subgroupOf_eq_of_le hK.2] at hh
  have hzQ : z ∈ K.pCoreIn 2 :=
    Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hK
      ⟨hK.2 hzT,fun q hq => hzcentral q (hcoreT hq)⟩
  have hzQ' : zK ∈ pCore 2 K := by
    obtain ⟨w,hw,he⟩ := hzQ
    exact (show w = zK from Subtype.ext he) ▸ hw
  have hzOmega : zK ∈ omegaOneCenterAmbient (pCore 2 K) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hzQ',Subtype.ext hz2,?_⟩
    intro q hq
    exact Subtype.ext (hzcentral q (hcoreT (mem_map_of_mem K.subtype hq)))
  have hres := InitialSource.residual_le_centralizer_omegaCore
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hK
  let f : solvableResidual K →* centralizer ({z} : Set G) :=
    (K.subtype.comp (solvableResidual K).subtype).codRestrict _ (by
      intro x
      exact mem_centralizer_singleton_iff.mpr
        (congrArg K.subtype ((hres x.property) zK hzOmega)).symm)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun a : centralizer ({z} : Set G) => (a : G)) hxy))
  let : Group.IsSolvable (solvableResidual K) :=
    Group.isSolvable_of_isSolvable_injective hf
  exact (Group.isSolvable_iff_subgroup_quotient (solvableResidual K)).mpr
    ⟨inferInstance,inferInstance⟩

/-- Conjugacy of Sylow subgroups transports the preceding conclusion to
every two-local containing any ambient Sylow subgroup. -/
theorem sylow_local_solvable_of_empty_faithful_of_solvable_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (z : G) (hz : z ∈ centralInvolutions T)
    (hC : Group.IsSolvable (centralizer ({z} : Set G)))
    (K : Subgroup G) (hK : IsTwoLocal K) (S : Sylow 2 G)
    (hSK : (S : Subgroup G) ≤ K) : Group.IsSolvable K := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  let e := MulAut.conj g
  let K' := K.map e.toMonoidHom
  have hST : (S : Subgroup G).map e.toMonoidHom = (T : Subgroup G) := by
    exact congrArg (fun R : Sylow 2 G => (R : Subgroup G)) hg
  have hTK : (T : Subgroup G) ≤ K' := hST ▸ map_mono (f := e.toMonoidHom) hSK
  let : Group.IsSolvable K' := local_solvable_of_empty_faithful_of_solvable_centralizer
    hG T hempty z hz hC K'
    ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_map e hK),hTK⟩
  exact Group.isSolvable_of_isSolvable_injective
    (f := (equivMapOfInjective K e.toMonoidHom e.injective).toMonoidHom)
    (equivMapOfInjective K e.toMonoidHom e.injective).injective

/-- The original Tits marking supplies solvability for all actual two-locals
containing an ambient Sylow, retaining the original central involution. -/
theorem source_tits_sylow_local_solvability
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    ∃ z : G, zpowers z = centralInvolutions T ∧ Recognition.ParrottCentralizerHypotheses z ∧
      ∀ K : Subgroup G, IsTwoLocal K → ∀ S : Sylow 2 G,
        (S : Subgroup G) ≤ K → Group.IsSolvable K := by
  obtain ⟨z,hz,hp⟩ := source_tits_parrott_hypotheses
    hG T hempty hM hu hmany hcard e H hH hmodel
  exact ⟨z,hz,hp,sylow_local_solvable_of_empty_faithful_of_solvable_centralizer
    hG T hempty z (hz ▸ mem_zpowers z) (hp.card_and_solvable z).2⟩

/-- Parrott's first normalizer is the original centralizer once solvability
of actual Sylow-containing two-locals has been established. -/
theorem parrott_derived_normalizer_of_sylow_local_solvability
    (z : G) (h : Recognition.ParrottCentralizerHypotheses z)
    (hlocal : ∀ K : Subgroup G, IsTwoLocal K → ∀ S : Sylow 2 G,
      (S : Subgroup G) ≤ K → Group.IsSolvable K) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    normalizer (E : Set G) = H := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  obtain ⟨_,_,_,_,_,hElem,hDcard,hSylow⟩ := Recognition.parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hEne : E ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hEcard
    omega
  have hHN : H ≤ normalizer (E : Set G) := by
    let DH := (commutator J).map J.subtype
    let : DH.Characteristic := inferInstance
    have hh := le_normalizer_map (H := DH) H.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map,range_subtype,DH,map_map] using hh
  obtain ⟨S,hS⟩ := hSylow (Classical.choice inferInstance)
  have hSN : (S : Subgroup G) ≤ normalizer (E : Set G) := by
    rw [hS]
    exact (map_subtype_le _).trans hHN
  exact Recognition.parrott_derived_normalizer_of_solvable z h
    (hlocal _ ⟨E,hEne,IsElementaryAbelian.isPGroup 2 E,rfl⟩ S hSN)

omit [Finite G] in
/-- The second elementary normalizer is solvable from the same source-local
condition, for every supplied second-elementary witness. -/
theorem parrott_second_normalizer_solvable_of_sylow_local_solvability
    (z : G) (d : Recognition.ParrottSecondElementaryData z)
    (hlocal : ∀ K : Subgroup G, IsTwoLocal K → ∀ S : Sylow 2 G,
      (S : Subgroup G) ≤ K → Group.IsSolvable K) :
    Group.IsSolvable (normalizer (d.F : Set G)) := by
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hFne : d.F ≠ ⊥ := by
    intro he
    have hc := d.card
    rw [he,card_bot] at hc
    omega
  exact hlocal _ ⟨d.F,hFne,IsElementaryAbelian.isPGroup 2 d.F,rfl⟩
    d.sylow d.sylow_le_normalizer

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
