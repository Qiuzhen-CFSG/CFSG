module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationSetup
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionCubic
public import Theory.SpecificGroups.PSL3Two.Parabolics.IndexSevenRadical
public import Theory.GroupTheory.PCoreCoverEquiv

/-!
# The original MS odd-index radical witness

For the original escaping-normalizer configuration, take A = N_{LT}(E).
The fourteen-point orbit gives |LT:C_{LT}(E)| = 14. The plane normalizer
contains T and is proper, so |LT:A| = 7. Its actual image under the
core quotient LT → SL₃(2) is an S₄ parabolic. The covered-parabolic core
calculation identifies O₂(A) with the literal R = C_T(E).

Thus A supplies MS2(a) in LR = LT. The final theorem applies the existing
MS setup to produce SmallMSPair under the original source inputs. The
structural and marked-module implications of 12.2.2 remain explicit;
there is no MS-classification or additional radical premise.

Source: Aschbacher–Smith, proof of 12.4.6, printed pp.813–814, and
C.1.31(MS2)(a), printed p.135.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- Extend the original component quotient across the actual two-core. -/
private theorem radical_quotient_map (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ∃ q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Matrix.PSL3Two.SL,
      Function.Surjective q ∧ q.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  have hcover : (H : Set G) ⊆ (L : Set G) * (H.pCoreIn 2 : Set G) := by
    intro g hg
    let : ((H.pCoreIn 2).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
    have hm : (⟨g,hg⟩ : H) ∈ L.subgroupOf H ⊔ (H.pCoreIn 2).subgroupOf H := by
      rw [← subgroupOf_sup le_sup_left (pCoreIn_le 2 H),
        ← join_eq_component_sup_core D ext hTV, subgroupOf_self]
      trivial
    obtain ⟨l,hl,k,hk,he⟩ := mem_sup_of_normal_right.mp hm
    exact ⟨l,hl,k,hk,congrArg Subtype.val he⟩
  obtain ⟨e,_⟩ := exists_pCoreQuotientEquiv_of_cover (p := 2)
    (show L ≤ H from le_sup_left) hcover
  let a := e.symm.trans ext.quotientEquiv
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  refine ⟨q,a.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']

/-- The point orbit computes the index of the literal plane centralizer in LT. -/
theorem radical_centralizer_index (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hFE : fixedSubgroup L V ≤ d.E) :
    (centralizer (d.E : Set G)).relIndex (L ⊔ (T : Subgroup G)) = 14 := by
  let H := L ⊔ (T : Subgroup G)
  let : MulAction H G := {
    smul := fun g v => MulAut.conj (g : G) v
    one_smul := by intro v; change (1 : G) * v * 1⁻¹ = v; group
    mul_smul := by
      intro g k v
      change ((g : G) * (k : G)) * v * ((g : G) * (k : G))⁻¹ =
        (g : G) * ((k : G) * v * (k : G)⁻¹) * (g : G)⁻¹
      group }
  have hHV : H ≤ normalizer (V : Set G) := sup_le D.normalizes hTV
  have hHL : H ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hHF : H ≤ normalizer (fixedSubgroup L V : Set G) :=
    (le_inf hHV (hHL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have ho : MulAction.orbit H d.v = (V : Set G) \ (fixedSubgroup L V : Set G) := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨(mem_normalizer_iff.mp (hHV g.property) d.v).mp
        (d.le_module d.mem_plane), fun hw =>
          d.nonfixed ((mem_normalizer_iff.mp (hHF g.property) d.v).mpr hw)⟩
    · intro hw
      obtain ⟨l,hl,he⟩ := ext.transitive_nonfixed hne d.v w
        (d.le_module d.mem_plane) hw.1 d.nonfixed hw.2
      exact ⟨⟨l,mem_sup_left hl⟩,he⟩
  have hs : MulAction.stabilizer H d.v = (centralizer (d.E : Set G)).subgroupOf H := by
    ext g
    change MulAut.conj (g : G) d.v = d.v ↔ (g : G) ∈ centralizer (d.E : Set G)
    have hcentral : (g : G) ∈ centralizer (fixedSubgroup L V : Set G) := by
      obtain ⟨l,hl,he⟩ := SLThreeCommutatorSource.same_action_of_common_normalizer
        ext g (hHV g.property) (hHL g.property)
      intro x hx
      have hh := he x hx.1
      have hfix : MulAut.conj l x = x :=
        mul_inv_eq_iff_eq_mul.mpr (hx.2 l hl)
      exact (mul_inv_eq_iff_eq_mul.mp (hh.trans hfix)).symm
    constructor
    · intro hg
      have hz : zpowers d.v ≤ centralizer ({(g : G)} : Set G) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mul_inv_eq_iff_eq_mul.mp hg).symm)
      rw [d.plane_eq_fixed_sup_point ext hne hFE,sup_eq_closure,centralizer_closure]
      intro x hx
      rcases hx with hx | hx
      · exact hcentral x hx
      · exact mem_centralizer_singleton_iff.mp (hz hx)
    · intro hg
      exact mul_inv_eq_iff_eq_mul.mpr (hg d.v d.mem_plane).symm
  change ((centralizer (d.E : Set G)).subgroupOf H).index = 14
  rw [← hs,MulAction.index_stabilizer,ho,
    Set.ncard_sdiff (show (fixedSubgroup L V : Set G) ⊆ V from inf_le_left)]
  change Nat.card V - Nat.card (fixedSubgroup L V) = 14
  rw [module_card_sixteen ext hne,ext.fixed_card_eq_two hne]

/-- The proper plane normalizer contains T, so its index is the odd divisor seven. -/
theorem radical_normalizer_index (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hFE : fixedSubgroup L V ≤ d.E)
    (hTE : (T : Subgroup G) ≤ normalizer (d.E : Set G)) :
    (normalizer (d.E : Set G)).relIndex (L ⊔ (T : Subgroup G)) = 7 := by
  let H := L ⊔ (T : Subgroup G)
  let A := (normalizer (d.E : Set G)).subgroupOf H
  have hc := d.radical_centralizer_index ext hne hTV hFE
  have hd : A.index ∣ 14 := hc ▸ index_dvd_of_le
    (show (centralizer (d.E : Set G)).subgroupOf H ≤ A from
      fun _ hx => Subgroup.centralizer_le_normalizer _ hx)
  have hodd : ¬ 2 ∣ A.index := fun hh => (T.subtype (show T ≤ H from le_sup_right)).not_dvd_index
    (hh.trans (index_dvd_of_le (show (T : Subgroup G).subgroupOf H ≤ A from
      fun _ ht => hTE ht)))
  have hneone : A.index ≠ 1 := by
    intro hi
    have hHA : H ≤ normalizer (d.E : Set G) := relIndex_eq_one.mp hi
    have hVE : V ≤ d.E := by
      intro w hw
      by_cases hf : w ∈ fixedSubgroup L V
      · exact hFE hf
      obtain ⟨l,hl,he⟩ := ext.transitive_nonfixed hne d.v w
        (d.le_module d.mem_plane) hw d.nonfixed hf
      rw [← he]
      exact (mem_normalizer_iff.mp (hHA (mem_sup_left hl)) d.v).mp d.mem_plane
    have hh := card_le_of_le hVE
    rw [module_card_sixteen ext hne,d.card_plane] at hh
    omega
  have hcop : Nat.Coprime A.index 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm
  have hseven : A.index ∣ 7 := hcop.dvd_of_dvd_mul_left hd
  exact ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hseven).resolve_left hneone

/-- The plane normalizer has exactly C_T(E) as its embedded two-core. -/
theorem radical_normalizer_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ((L ⊔ (T : Subgroup G)) ⊓ normalizer (d.E : Set G)).pCoreIn 2 = d.R := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hFE := d.fixed_le_plane h structural marked hmodel hne hescape
  have hTE := d.sylow_normalizes.trans
    (d.escape_geometry h structural marked hmodel hne hescape).2.2.2.1
  let H := L ⊔ (T : Subgroup G)
  let A := (normalizer (d.E : Set G)).subgroupOf H
  let C := (centralizer (d.E : Set G)).subgroupOf H
  obtain ⟨q,hq,hk⟩ := radical_quotient_map ext hTV
  have hkC : q.ker ≤ C := by
    intro x hx
    rw [hk] at hx
    have hxQ : (x : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype hx
    exact centralizer_le d.le_module (D.core_centralizes hxQ)
  have hcalc := Matrix.PSL3Two.core_of_index_seven_cover q hq (by rw [hk]; exact pCore_isPGroup)
    (T.subtype (show T ≤ H from le_sup_right)) A C (d.R.subgroupOf H)
    hkC (fun _ hx => Subgroup.centralizer_le_normalizer _ hx) (fun _ hx => hTE hx)
    (d.radical_normalizer_index ext hne hTV hFE hTE)
    (d.radical_centralizer_index ext hne hTV hFE)
    (by ext x; rfl)
    (by
      rw [Sylow.coe_subtype,
        relIndex_subgroupOf (show (T : Subgroup G) ≤ H from le_sup_right)]
      exact d.index)
  have hm := congrArg (fun B : Subgroup H => B.map H.subtype) hcalc
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le (show d.R ≤ H from inf_le_left.trans le_sup_right)] at hm
  simpa only [A,subgroupOf_map_subtype,inf_comm] using hm

/-- The original plane normalizer supplies the literal existential MS2(a). -/
theorem ms_oddIndex
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    MSOddIndex L d.R := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hFE := d.fixed_le_plane h structural marked hmodel hne hescape
  have hTE := d.sylow_normalizes.trans
    (d.escape_geometry h structural marked hmodel hne hescape).2.2.2.1
  have hi := d.radical_normalizer_index ext hne hTV hFE hTE
  let A := (L ⊔ (T : Subgroup G)) ⊓ normalizer (d.E : Set G)
  have hAi : A.relIndex (L ⊔ (T : Subgroup G)) = 7 := by
    rw [inf_relIndex_left]
    exact hi
  refine ⟨A,?_,?_,d.radical_normalizer_core h structural marked hmodel hne hescape⟩
  · rw [d.ms_join_eq ext h hTV]
    apply lt_iff_le_not_ge.mpr
    refine ⟨inf_le_left,?_⟩
    intro hle
    have hi1 : A.relIndex (L ⊔ (T : Subgroup G)) = 1 := relIndex_eq_one.mpr hle
    omega
  · change Odd (A.relIndex (L ⊔ d.R))
    rw [d.ms_join_eq ext h hTV,hAi]
    decide

/-- Apply the proved radical witness to the existing original-source MS consumer. -/
theorem smallMSPair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.SmallMSPair
      KnownSimple.IsKnownSimple L d.R := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  exact smallMSPair_of_oddIndex h structural ext d hescape
    (d.ms_oddIndex h structural marked hmodel hne hescape)

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
