module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.PairedNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Construction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient.Inclusion

/-!
The original end-node action and quotient maps in [AS, 15.3.25]. The normalized
star marking gives the first parabolic image; ambient conjugation identifies
the second image with it. The intrinsic core maps to the concrete block core
in both actions, and the kernel of XS → XT/O₂(XT) is exactly O₂(XS).
The even permutations pull back to the source's literal S₀ = S ∩ LO₂(LS).
-/

public noncomputable section
set_option linter.unusedSectionVars false
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration EightGeometry PairedQuotient PairedOffenders
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}
namespace EndNodeData
variable (e : EndNodeData d I c)
  (hn : ∀ i : I, e.marking.equiv (d.starMap I i) = e.action.actor i)
include hn

theorem normalized_actor_image (A : Subgroup G) :
    (A.subgroupOf I).map e.action.actor = (d.starImage I A).map e.marking.equiv.toMonoidHom := by
  change (A.subgroupOf I).map e.action.actor = ((A.subgroupOf I).map (d.starMap I)).map _
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro i
  exact (hn i).symm

omit hn in
theorem actor_kernel_eq_core : e.action.actor.ker = pCore 2 I := by
  apply map_injective I.subtype_injective
  rw [NaturalModule.naturalActor_ker,subgroupOf_map_subtype,inf_comm,e.core_centralizer]
  rfl

theorem mem_S0_iff_even (i : I) (hi : (i : G) ∈ d.S) :
    (i : G) ∈ d.S0 c.L ↔ e.action.actor i ∈ alternatingGroup (Fin 8) := by
  have hmap : ((alternatingGroup (Fin 8)).comap e.action.actor).map I.subtype =
      c.L ⊔ I.pCoreIn 2 := by
    rw [←e.component_image,←e.normalized_actor_image hn c.L,comap_map_eq,
      e.actor_kernel_eq_core,Subgroup.map_sup,map_subgroupOf_eq_of_le (component_le c)]
    rfl
  change (i : G) ∈ d.S ⊓ (c.L ⊔ (c.L ⊔ d.S).pCoreIn 2) ↔ _
  rw [←e.source.generated]
  constructor
  · intro h
    have hh : (i : G) ∈ ((alternatingGroup (Fin 8)).comap e.action.actor).map I.subtype := hmap.symm ▸ h.2
    obtain ⟨j,hj,hji⟩ := hh
    exact (Subtype.ext hji : j=i) ▸ hj
  · intro h
    exact ⟨hi,hmap ▸ mem_map_of_mem I.subtype h⟩

variable (hL : c.L = RankOne.threeResidualIn
    (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S)
local notation "b" => e.pairedConfiguration hL t ht htS

omit hn in
@[simp] theorem pairedConfiguration_action : (b).action = e.action := by
  unfold pairedConfiguration
  rcases e.source_core_generation hL t ht htS with ⟨hCU,hCV,hgen⟩
  rcases e.source_conjugate_product hL t ht htS with ⟨hdis,hnorm,hcomm,hprod⟩
  rfl

omit hn in
@[simp] theorem pairedConfiguration_conjugateAction : (b).conjugateAction = e.action.conjugate t := by
  unfold pairedConfiguration
  rcases e.source_core_generation hL t ht htS with ⟨hCU,hCV,hgen⟩
  rcases e.source_conjugate_product hL t ht htS with ⟨hdis,hnorm,hcomm,hprod⟩
  rfl

theorem paired_first_range : (b).f.range = parabolic := by
  simp only [PairedMinimality.Configuration.f,pairedConfiguration_action]
  change (e.action.actor.comp (inclusion (b).local_le)).range = _
  rw [MonoidHom.range_comp,inclusion_range,e.normalized_actor_image hn]
  exact e.residual_join_marking hL

theorem paired_first_sylow
    (hS : (d.S.subgroupOf I).map e.action.actor = canonicalSylow) :
    (b).S.map (b).f = canonicalSylow := by
  simp only [PairedMinimality.Configuration.f,pairedConfiguration_action]
  change (d.S.subgroupOf (b).J).map (e.action.actor.comp (inclusion (b).local_le)) = _
  rw [←map_map]
  have he : (d.S.subgroupOf (b).J).map (inclusion (b).local_le) = d.S.subgroupOf I := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x,(show d.S ≤ (b).J from le_sup_right) hx⟩,hx,Subtype.ext rfl⟩
  rw [he,hS]

omit hn in
theorem paired_core_kernel :
    (PairedOffenders.Configuration.q b (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).ker = (b).P := by
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTJ := residual_join_normalized_by_sylow d hi
  have hJK : (b).J ≤ XT d (RankOne.threeResidualIn (centralizer (d.ZS : Set G))) :=
    sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hnJ : XT d (RankOne.threeResidualIn (centralizer (d.ZS : Set G))) ≤ normalizer ((b).J : Set G) :=
    sup_le (le_sup_left.trans le_normalizer) hTJ
  let : ((b).J.subgroupOf (XT d (RankOne.threeResidualIn (centralizer (d.ZS : Set G))))).Normal :=
    normal_subgroupOf_of_le_normalizer hnJ
  exact ker_coreQuotient_inclusion 2 hJK

omit hn in
theorem paired_first_kernel_isTwo : IsPGroup 2 (b).f.ker := by
  have hh : (b).f.ker = (e.action.actor.ker).comap (inclusion (b).local_le) := by
    simp only [PairedMinimality.Configuration.f,pairedConfiguration_action]
    change (e.action.actor.comp (inclusion (b).local_le)).ker = _
    rw [MonoidHom.comap_ker]
  rw [hh,e.actor_kernel_eq_core]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

theorem paired_first_core : (b).P.map (b).f = blockCore :=
  map_core_eq_blockCore (b).f (e.paired_first_range hn hL t ht htS)
    (e.paired_first_kernel_isTwo hL t ht htS)

omit hn in
def pairedConjugation : MulAut (b).J :=
  (b).J.normalizerMonoidHom ⟨t,mem_normalizer_iff_map_conj_eq.mpr (b).preserves_J⟩

omit hn in
@[simp] theorem pairedConjugation_apply (j : (b).J) :
    (e.pairedConjugation hL t ht htS j : G) = t * (j : G) * t⁻¹ := by rfl

omit hn in
theorem paired_conjugate_action (j : (b).J) :
    (b).g (e.pairedConjugation hL t ht htS j) = (b).f j := by
  let a := e.pairedConjugation hL t ht htS
  let v := (MulAut.conj t).subgroupMap I
  simp only [PairedMinimality.Configuration.f,PairedMinimality.Configuration.g,
    pairedConfiguration_action,pairedConfiguration_conjugateAction]
  change (e.action.conjugate t).actor (inclusion (b).local_le_conjugate (a j)) =
    e.action.actor (inclusion (b).local_le j)
  have he : inclusion (b).local_le_conjugate (a j) = v (inclusion (b).local_le j) :=
    Subtype.ext (e.pairedConjugation_apply hL t ht htS j)
  rw [he]
  change e.action.actor (v.symm (v (inclusion (b).local_le j))) = _
  rw [v.symm_apply_apply]

omit hn in
theorem pairedConjugation_mapS :
    (b).S.map (e.pairedConjugation hL t ht htS).toMonoidHom = (b).S := by
  let a := e.pairedConjugation hL t ht htS
  have hm (j : (b).J) : j ∈ (b).S ↔ a j ∈ (b).S :=
    mem_normalizer_iff.mp (mem_normalizer_iff_map_conj_eq.mpr (b).preserves_S) (j : G)
  apply le_antisymm
  · rintro _ ⟨j,hj,rfl⟩
    exact (hm j).mp hj
  · intro j hj
    obtain ⟨k,rfl⟩ := a.surjective j
    exact ⟨k,(hm k).mpr hj,rfl⟩

theorem paired_second_core : (b).P.map (b).g = blockCore := by
  let a := e.pairedConjugation hL t ht htS
  have hf : (b).g.comp a.toMonoidHom = (b).f := by
    apply MonoidHom.ext
    exact e.paired_conjugate_action hL t ht htS
  have hP : (b).P.map a.toMonoidHom = (b).P := pCore_map_iso 2 a
  calc
    _ = ((b).P.map a.toMonoidHom).map (b).g := by rw [hP]
    _ = (b).P.map (b).f := by rw [map_map,hf]
    _ = blockCore := e.paired_first_core hn hL t ht htS

theorem paired_second_sylow
    (hS : (d.S.subgroupOf I).map e.action.actor = canonicalSylow) :
    (b).S.map (b).g = canonicalSylow := by
  let a := e.pairedConjugation hL t ht htS
  have hf : (b).g.comp a.toMonoidHom = (b).f := by
    apply MonoidHom.ext
    exact e.paired_conjugate_action hL t ht htS
  calc
    _ = ((b).S.map a.toMonoidHom).map (b).g := by rw [e.pairedConjugation_mapS]
    _ = (b).S.map (b).f := by rw [map_map,hf]
    _ = canonicalSylow := e.paired_first_sylow hn hL t ht htS hS

end EndNodeData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
