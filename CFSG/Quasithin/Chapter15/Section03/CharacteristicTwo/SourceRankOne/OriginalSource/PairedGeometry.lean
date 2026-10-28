module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.PairedExtension
public import Theory.GroupAction.MaximalCosetOrbit

/-!
The source-facing paired end-node geometry for the genuine 15.3.25 branch.

The proof normalizes the literal eight-point action, constructs the two
quotient Sylow coordinate systems and the quotient conjugation, and records
the even preimage as the intersection with the original S. The latter is
essential: equality of quotient images does not imply equality with the full
preimage when the quotient kernel is not contained in S.

Source: Aschbacher-Smith, 15.3.25, printed pp. 1133-1134
(PDF pp. 1150-1151).
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration EightGeometry PairedQuotient PairedOffenders PairedQuotient.Conjugation
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}
namespace EndNodeData
variable (e : EndNodeData d I c)
  (hn : ∀ i : I, e.marking.equiv (d.starMap I i) = e.action.actor i)
  (hL : c.L = RankOne.threeResidualIn
    (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S)
local notation "b" => e.pairedConfiguration hL t ht htS
include hn
local notation "Q" => PairedOffenders.Configuration.q b inf_le_left

theorem paired_geometry_of_extension
    (hS : (d.S.subgroupOf I).map e.action.actor = canonicalSylow)
    (hExt : ∀ _first : SylowCoordinates (b).S (b).f Q,
      (b).S.map Q ≠ PairedOffenders.Configuration.Timage b →
      ∃ P : Sylow 2 (GL (Fin 2) (ZMod 3)),
        Nonempty (PairedOffenders.Configuration.Timage b ≃* P)) :
    Nonempty (SourceGeometry b) := by
  have hST : d.S ≤ (d.T : Subgroup G) := inf_le_left
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp (normal_of_index_eq_two hi)
  let a := e.pairedConjugation hL t ht htS
  have haS : (b).S.map a.toMonoidHom = (b).S := e.pairedConjugation_mapS hL t ht htS
  have haP : (b).P.map a.toMonoidHom = (b).P := pCore_map_iso 2 a
  have hfker : (b).f.ker ≤ (b).P :=
    le_sSup ⟨inferInstance,e.paired_first_kernel_isTwo hL t ht htS⟩
  have hgker : (b).g.ker ≤ (b).P := by
    intro y hy
    obtain ⟨x,rfl⟩ := a.surjective y
    have hx : x ∈ (b).f.ker := (e.paired_conjugate_action hL t ht htS x).symm.trans hy
    exact haP ▸ mem_map_of_mem a.toMonoidHom (hfker hx)
  have hcore := e.paired_core_kernel hL t ht htS
  obtain ⟨first⟩ := exists_sylowCoordinates (b).S (b).f Q
    (e.paired_first_sylow hn hL t ht htS hS)
    (hcore ▸ e.paired_first_core hn hL t ht htS) (hcore.symm ▸ hfker)
  obtain ⟨second⟩ := exists_sylowCoordinates (b).S (b).g Q
    (e.paired_second_sylow hn hL t ht htS hS)
    (hcore ▸ e.paired_second_core hn hL t ht htS) (hcore.symm ▸ hgker)
  let β : MulAut (b).S := (a.subgroupMap (b).S).trans (MulEquiv.subgroupCongr haS)
  let Y := XT d (RankOne.threeResidualIn (centralizer (d.ZS : Set G)))
  let π := PairedOffenders.quotientMap d (RankOne.threeResidualIn (centralizer (d.ZS : Set G)))
  let tx : Y := ⟨t,(le_sup_right : (d.T : Subgroup G) ≤ Y) ht⟩
  have himage : (d.S.subgroupOf Y).map π = (b).S.map Q := by
    change _ = (b).S.map (π.comp (inclusion (sup_le le_sup_left (hST.trans le_sup_right))))
    rw [←map_map]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨⟨x,(show d.S ≤ (b).J from le_sup_right) hx⟩,hx,Subtype.ext rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact hx
  have htN : tx ∈ normalizer (d.S.subgroupOf Y : Set Y) :=
    d.S.le_normalizer_comap Y.subtype (hTS ht)
  have htR : PairedOffenders.Configuration.tq b ∈ normalizer ((b).S.map Q : Set (Y ⧸ pCore 2 Y)) := by
    rw [←himage]
    exact (d.S.subgroupOf Y).le_normalizer_map π (mem_map_of_mem π htN)
  let δ := ((b).S.map Q).normalizerMonoidHom ⟨PairedOffenders.Configuration.tq b,htR⟩
  refine ⟨{
    s_le_t := hST
    s_normalized := hTS
    first := first
    second := second
    core := hcore
    first_core := e.paired_first_core hn hL t ht htS
    second_core := e.paired_second_core hn hL t ht htS
    actorConj := β
    actorConj_eq := ?_
    quotientConj := δ
    quotientConj_eq := ?_
    relabel := 1
    actionConj := ?_
    generation := ?_
    extension := hExt first
    even_preimage := ?_ }⟩
  · intro s
    exact e.pairedConjugation_apply hL t ht htS s
  · intro x
    rfl
  · intro s
    have hb : (β s : (b).J) = a s := Subtype.ext rfl
    rw [hb]
    simpa only [one_mul,inv_one,mul_one] using e.paired_conjugate_action hL t ht htS (s : (b).J)
  · exact (sup_zpowers_eq_of_relIndex_prime hST Nat.prime_two hi ht htS).symm
  · have hff (j : (b).J) : (b).f j = e.action.actor (inclusion (b).local_le j) := by
      simp only [PairedMinimality.Configuration.f,e.pairedConfiguration_action]
      rfl
    apply le_antisymm
    · intro x hx
      let j : (b).J := ⟨x,(show d.S ≤ (b).J from le_sup_right) hx.1⟩
      have hp : (b).f j ∈ alternatingGroup (Fin 8) := by
        rw [hff]
        exact (e.mem_S0_iff_even hn (inclusion (b).local_le j) hx.1).mp hx
      have hm := ((localCoordinates first).mem_marked ⟨j,hx.1⟩).mpr hp
      exact ⟨hx.1,PairedOffenders.Configuration.toXT b hST j,
        ⟨(Q).subgroupMap (b).S ⟨j,hx.1⟩,hm,rfl⟩,rfl⟩
    · rintro x ⟨hx,y,hy,hyx⟩
      let j : (b).J := ⟨x,(show d.S ≤ (b).J from le_sup_right) hx⟩
      have hey : y = PairedOffenders.Configuration.toXT b hST j := Subtype.ext hyx
      rw [hey] at hy
      obtain ⟨z,hz,hez⟩ := hy
      have hez' : z = (Q).subgroupMap (b).S ⟨j,hx⟩ := Subtype.ext hez
      have hp := ((localCoordinates first).mem_marked ⟨j,hx⟩).mp (hez' ▸ hz)
      change (b).f j ∈ alternatingGroup (Fin 8) at hp
      rw [hff] at hp
      exact (e.mem_S0_iff_even hn (inclusion (b).local_le j) hx).mpr hp

/-- Construct every field of the terminal geometry on the normalized actual action. -/
theorem paired_geometry
    (hS : (d.S.subgroupOf I).map e.action.actor = canonicalSylow) :
    Nonempty (SourceGeometry b) :=
  e.paired_geometry_of_extension hn hL t ht htS hS (e.paired_extension hn hL t ht htS)

omit hn in
/-- The restricted action kernel is the full original component-module centralizer. -/
theorem paired_ambient_kernel :
    (b).f.ker.map (b).J.subtype = I ⊓ centralizer (d.componentModule I c.L : Set G) := by
  have hCJ : I ⊓ centralizer (d.componentModule I c.L : Set G) ≤ (b).J := by
    rw [e.core_centralizer]
    exact (e.source.sylow_eq ▸ pCoreIn_le_sylow I e.source.sylow).trans le_sup_right
  rw [(b).first_kernel,NaturalEightAction.restricted_centralizer (b).J
    ((b).first_le.trans le_sup_right),subgroupOf_map_subtype]
  exact le_antisymm (fun x hx => ⟨(b).local_le hx.2,hx.1⟩)
    (fun x hx => ⟨hx.2,hCJ hx⟩)

/-- Noncentrality follows from the original alternating component image. -/
theorem component_module_noncentral :
    ¬ c.L ≤ centralizer (d.componentModule I c.L : Set G) := by
  intro h
  have hk : c.L.subgroupOf I ≤ e.action.actor.ker := by
    rw [NaturalModule.naturalActor_ker]
    exact fun _ hi => h hi
  have hb : (c.L.subgroupOf I).map e.action.actor = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hk
  rw [e.normalized_actor_image hn,e.component_image] at hb
  exact ((alternatingGroup (Fin 8)).nontrivial_iff_ne_bot.mp inferInstance) hb

omit hn t ht htS in
include e hL in
/-- The genuine paired end-node branch is impossible. All model markings,
quotient coordinates, larger Sylow alternatives, and terminal source inputs
are constructed internally. Only the independent residual identity remains. -/
theorem false_of_fixedLineResidual : False := by
  obtain ⟨e',hS,hn'⟩ := e.exists_normalized
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro h
    have he : d.S = (d.T : Subgroup G) := le_antisymm inf_le_left h
    change (d.S.subgroupOf (d.T : Subgroup G)).index = 2 at hi
    rw [he,subgroupOf_self,index_top] at hi
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨geometry⟩ := e'.paired_geometry hn' hL t ht htS hS
  have hR : (e'.source.sylow : Subgroup I) = d.S.subgroupOf I := by
    rw [←e'.source.sylow_eq]
    exact (comap_map_eq_self_of_injective I.subtype_injective _).symm
  exact geometry.outside_contradiction e'.source.sylow hR c.le_thompson
    (e'.component_module_noncentral hn') (e'.paired_ambient_kernel hL t ht htS)
    e'.source.contains c.outside e'.unique

end EndNodeData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
