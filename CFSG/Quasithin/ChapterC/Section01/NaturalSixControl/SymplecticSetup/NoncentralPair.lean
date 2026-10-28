module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.RadiusImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.NoncentralPair
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# A large critical image from a noncentral radius commutator

A kernel normalizes each radius generator and the opposite kernel. An
endpoint image of order two therefore has trivial induced action, which
would make the mixed triple commutator vanish. In the actual binary source,
a nontrivial mixed triple consequently forces an image of order at least
four. Combined with the geometric selection, this supplies exactly the
large-image critical pair used in the second paragraph of MS93 (5.2).

The final application uses the original characteristic replacement.
Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed p.914.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

theorem noncentral_generator_image_four_le (hb : 2 < s.geometry.b R)
    (a d e : Vertex R) (ha : color R a = false)
    (hd : color R d = false) (he : color R e = false)
    (hda : (cosetGraph R).dist d a ≤ 2) (hea : (cosetGraph R).dist e a ≤ 2)
    (hne : ⁅⁅Z R d,Q R a⁆,Z R e⁆ ≠ ⊥) :
    4 ≤ (Q R e).relIndex (Z R d) := by
  have hnZd : Q R a ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (Q_le_stabilizer_of_dist_le_two a d ha hd
      (by rwa [SimpleGraph.dist_comm])).trans (Z_normalized R d)
  have hnQe : Q R a ≤ normalizer (Q R e : Set (FreeAmalgam R)) :=
    (Q_le_stabilizer_of_dist_le_two a e ha he
      (by rwa [SimpleGraph.dist_comm])).trans (Q_normalized R e)
  have hout := SectionFive.noncentral_generator_not_le R s.geometry a d e ha he hea hne
  have hone : (Q R e).relIndex (Z R d) ≠ 1 := fun hh => hout (relIndex_eq_one.mp hh)
  have htwo : (Q R e).relIndex (Z R d) ≠ 2 := by
    intro hh
    have hnint : Q R a ≤ normalizer ((Z R d ⊓ Q R e : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
      intro q hq
      rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_inf _ _ _ (MulAut.conj q).injective,
        mem_normalizer_iff_map_conj_eq.mp (hnZd hq),
        mem_normalizer_iff_map_conj_eq.mp (hnQe hq)]
    have hc := commutator_le_of_normalized_index_two (Z R d) (Z R d ⊓ Q R e)
      (Q R a) inf_le_left (by rwa [inf_relIndex_left]) hnZd hnint
    apply hne
    apply le_bot_iff.mp
    exact (commutator_mono (hc.trans inf_le_right) le_rfl).trans (by
      rw [commutator_comm,s.geometry.centralizes e he])
  have hZdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hda le_rfl)
  have hp : IsPGroup 2 (Z R d) :=
    (Q_isPGroup R s.two_group s.core_le a ha).to_le (hZdV.trans (V_le_Q R ha hb))
  let : Finite (stabilizer R a) := finite_stabilizer R a
  have hZa : Z R d ≤ stabilizer R a :=
    (hZdV.trans (V_le_Q R ha hb)).trans (fun _ hx => hx.1)
  let : Finite (Z R d) := Finite.of_injective (inclusion hZa) (inclusion_injective hZa)
  obtain ⟨n,hn⟩ := hp.index ((Q R e).subgroupOf (Z R d))
  change (Q R e).relIndex (Z R d) = 2^n at hn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp_all
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2

theorem exists_noncentral_critical_pair_large_image (hb : s.geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hn : ¬ ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R))) :
    ∃ d e, color R d = false ∧ color R e = false ∧
      (cosetGraph R).dist d a = 2 ∧ (cosetGraph R).dist e a = 2 ∧
      ⁅⁅Z R d,Q R a⁆,Z R e⁆ ≠ ⊥ ∧ 4 ≤ (Q R e).relIndex (Z R d) ∧
      ∃ hd : color R d = false,CriticalPair R d e (s.geometry.exists_critical d hd) := by
  obtain ⟨d,e,hd,he,hda,hea,ht,hcrit⟩ :=
    SectionFive.exists_noncentral_critical_pair R s.geometry hb a ha hn
  exact ⟨d,e,hd,he,hda,hea,ht,
    noncentral_generator_image_four_le s (by omega) a d e ha hd he hda.le hea.le ht,hcrit⟩

end Source
namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T)

/-- Failure of centrality in the original reduced source produces the genuine
large-image critical pair required by source (5.2)(i). -/
theorem reducedSource_noncentral_critical_pair_large_image (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : ((originalSource d h).reduce c).geometry.b c.radical = 4)
    (hn : ¬ ⁅V c.radical (alpha c.radical),Q c.radical (alpha c.radical)⁆ ≤
      centralizer (V c.radical (alpha c.radical) : Set (FreeAmalgam c.radical))) :
    ∃ a e, color c.radical a = false ∧ color c.radical e = false ∧
      (cosetGraph c.radical).dist a (alpha c.radical) = 2 ∧
      (cosetGraph c.radical).dist e (alpha c.radical) = 2 ∧
      ⁅⁅Z c.radical a,Q c.radical (alpha c.radical)⁆,Z c.radical e⁆ ≠ ⊥ ∧
      4 ≤ (Q c.radical e).relIndex (Z c.radical a) ∧
      ∃ ha : color c.radical a = false,
        CriticalPair c.radical a e (((originalSource d h).reduce c).geometry.exists_critical a ha) :=
  Source.exists_noncentral_critical_pair_large_image ((originalSource d h).reduce c)
    hb (alpha c.radical) rfl hn
end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
