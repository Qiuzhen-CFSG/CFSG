module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl
public import Theory.GroupTheory.PResidual.SimpleQuotientNormalGeneration
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Conjugate generation of the original commutator core

The original Y₊ normally generates L once L/O₂(L) is simple. The core
Q=[O₂(L),L] lies in M∩I, which normalizes Y₊, so [Q,Y₊] lies in Q∩Y₊.
Normal generation and commutator idempotence show that the L-conjugates
of this intersection generate Q. In the abelian-core branch this gives
the centralization step of15.3.31 without choosing natural summands.

Source: Aschbacher–Smith15.3.31, printed p.1132.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open EightGeometry
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

namespace SourceData
variable {κ : GroupClass} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData κ d c)
include s

/-- The actual residual normally generates the component. -/
theorem yplus_normalClosure_eq_top [IsSimpleGroup (c.L ⧸ pCore 2 c.L)] :
    normalClosure (d.Yplus.subgroupOf c.L : Set c.L) = ⊤ := by
  let := component_isPerfect_of_containment d c s.contains
  let q := QuotientGroup.mk' (pCore 2 c.L)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hY : IsPPerfect 2 (d.Yplus.subgroupOf c.L) :=
    (yplus_isPPerfect d).of_surjective (subgroupOfEquivOfLe s.contains).symm.toMonoidHom
      (subgroupOfEquivOfLe s.contains).symm.surjective
  apply normalClosure_eq_top_of_pPerfect_simple_image perfect_twoPerfect q
    (QuotientGroup.mk'_surjective _) hk
  intro he
  have hb : d.Yplus.subgroupOf c.L ≤ ⊥ :=
    isPPerfect_le_of_map_le_of_kernel_normalizes q _ ⊥ hY hk
      (by rw [normalizer_eq_top]; exact le_top) (by rw [he]; exact bot_le)
  have hybot : d.Yplus = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro y hy
    exact congrArg Subtype.val (show (⟨y,s.contains hy⟩:c.L) = 1 from
      hb (show (⟨y,s.contains hy⟩:c.L) ∈ d.Yplus.subgroupOf c.L from hy))
  have hp := s.line.plane_full
  rw [hybot,commutator_bot_right] at hp
  have hc := d.action.card_plane (Multiplicative.ofAdd (1 : ZMod 2))
  change Nat.card d.V₂ = 4 at hc
  rw [←hp,Subgroup.card_bot] at hc
  omega

/-- The actual intersection with Y₊ generates Q; no decomposition of Q
into natural summands is needed. -/
theorem core_le_span_intersection [IsSimpleGroup (c.L ⧸ pCore 2 c.L)] :
    extensionCore c.L ≤ localSpan (extensionCore c.L ⊓ d.Yplus) c.L := by
  let Q := extensionCore c.L
  let N := localSpan (Q ⊓ d.Yplus) c.L
  have hLQ : c.L ≤ normalizer (Q : Set G) := normalizes_extensionCore c.L.le_normalizer
  have hQL : Q ≤ c.L := le_normalizer_iff_commutator_le_right.mp
    ((pCoreIn_le 2 c.L).trans c.L.le_normalizer)
  have hQI : Q ≤ I.pCoreIn 2 := by
    change extensionCore c.L ≤ I.pCoreIn 2
    rw [extensionCore_eq_overgroup d c s.contains s.normal]
    exact le_normalizer_iff_commutator_le_left.mp ((component_le c).trans
      (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
  have hQS : Q ≤ d.S := hQI.trans (s.sylow_eq ▸ pCoreIn_le_sylow I s.sylow)
  have hQM : Q ≤ d.MI I := le_inf (hQS.trans (inf_le_left.trans d.sylow_le))
    (hQL.trans (component_le c))
  have hQY : Q ≤ normalizer (d.Yplus : Set G) :=
    hQM.trans (s.line.normalizer_eq.symm ▸ inf_le_right)
  let : (Q.subgroupOf c.L).Normal := normal_subgroupOf_of_le_normalizer hLQ
  let : (N.subgroupOf c.L).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy (Q ⊓ d.Yplus) c.L)
  have hcomm : ⁅Q.subgroupOf c.L,d.Yplus.subgroupOf c.L⁆ ≤ N.subgroupOf c.L := by
    apply commutator_le.mpr
    intro q hq y hy
    apply le_conjugateSpanBy (Q ⊓ d.Yplus) c.L
    exact ⟨(le_normalizer_iff_commutator_le_left.mp (s.contains.trans hLQ))
        (commutator_mem_commutator hq hy),
      (le_normalizer_iff_commutator_le_right.mp hQY) (commutator_mem_commutator hq hy)⟩
  have hh := commutator_normalClosure_le_of_normal (Q.subgroupOf c.L)
    (d.Yplus.subgroupOf c.L) (N.subgroupOf c.L) hcomm
  rw [s.yplus_normalClosure_eq_top] at hh
  have hm := map_mono (f := c.L.subtype) hh
  rw [map_commutator,map_subgroupOf_eq_of_le hQL,←MonoidHom.range_eq_map,range_subtype,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self (inf_le_left.trans hQL))] at hm
  let := component_isPerfect_of_containment d c s.contains
  have hid := commutator_isPPerfect_idempotent c.L (c.L.pCoreIn 2)
    (perfect_twoPerfect (A := c.L)) (isPGroup_pCoreIn 2 c.L)
    (c.L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L)))
  exact hid.symm.le.trans hm

/-- Literal source31 application: in the abelian-core branch the already
proved star-centralizer calculation forces D=C_I(Y₊) to centralize Q. -/
theorem centralizes_abelian_core [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hstar : centralizer (d.starImage I d.Yplus : Set (d.Star I)) = ⊥)
    (hQ : IsMulCommutative (extensionCore c.L)) :
    yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) :=
  s.centralizes_core_of_star_centralizer_and_generation hstar hQ s.core_le_span_intersection

end SourceData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
