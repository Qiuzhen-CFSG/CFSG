module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelSelectors
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.GroupTheory.IndexNormal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

/-!
# Opposite Thompson movers on the original Borel edges

Let J be an opposite Thompson mover of index two in an incident edge T.
If J does not contain the starting two-core Q, then QJ = T. Consequently,
whenever T and an actor A generate the local stabilizer, JA has index at
most two there and contains its actual two-residual. This argument takes
normality inside the vertex stabilizer; the free amalgam is not finite.
If J does contain Q and differs from the starting mover, their intersection
has exact index four over Q.

The paired-selector application transports the original opposite mover
along the same selected edges. It retains both residual-generation
conclusions with the same critical seed, or the original core-containment
and intersection-index branch. The full seeds and both moving-cover orders
remain unchanged. No quotient kernel is identified with the two-core.

This proves the core-noncontainment branch of the opposite-mover comparison
used in MS93 (5.5)(c), together with its synchronized small-critical-path
application and the numerical part of the other branch. The further
comparison when the opposite mover contains Q, backward criticality, and
the terminal contradictions (5.11)--(5.12) remain necessary; whole-core
exhaustion is not asserted.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.7), printed pp.915--919; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull

private theorem residual_le_of_index_le_two {H : Type*} [Group H]
    (P F : Subgroup H) [Finite P] (hi : F.relIndex P ≤ 2) :
    (pResidual 2 P).map P.subtype ≤ F := by
  have hpos : F.relIndex P ≠ 0 := index_ne_zero_of_finite
  have hc : F.relIndex P = 1 ∨ F.relIndex P = 2 := by omega
  rcases hc with hc | hc
  · exact (map_subtype_le _).trans (relIndex_eq_one.mp hc)
  · have hc' : (F.subgroupOf P).index = 2 := hc
    let : (F.subgroupOf P).Normal := normal_of_index_eq_two hc'
    have hquot : IsPGroup 2 (P ⧸ F.subgroupOf P) :=
      IsPGroup.of_card (n := 1) (by simpa only [←index_eq_card,pow_one] using hc')
    exact map_le_iff_le_comap.mpr (show pResidual 2 P ≤ F.subgroupOf P from
      sInf_le ⟨inferInstance,hquot⟩)

private theorem index_two_opposite_generation {H : Type*} [Group H]
    (P Q T J A : Subgroup H) [Finite P]
    (hQT : Q ≤ T) (hTP : T ≤ P) (hJT : J ≤ T)
    (hQN : P ≤ normalizer (Q : Set H)) (hi : J.relIndex T = 2)
    (hnot : ¬ Q ≤ J) (hgen : T ⊔ A = P) :
    (J ⊔ A).relIndex P ≤ 2 ∧ (pResidual 2 P).map P.subtype ≤ J ⊔ A := by
  let F := J ⊔ A
  have hFP : F ≤ P := sup_le (hJT.trans hTP) (le_sup_right.trans hgen.le)
  let : Finite F := Finite.of_injective (inclusion hFP) (inclusion_injective _)
  have hJT' : J ≤ Q ⊔ J := le_sup_right
  have hsupT : Q ⊔ J ≤ T := sup_le hQT hJT
  have hm := relIndex_mul_relIndex J (Q ⊔ J) T hJT' hsupT
  rw [hi] at hm
  have hd : J.relIndex (Q ⊔ J) ∣ 2 := ⟨(Q ⊔ J).relIndex T,by omega⟩
  have hQJ : Q ⊔ J = T := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
    · exact (hnot (le_sup_left.trans (relIndex_eq_one.mp he))).elim
    · rw [he] at hm
      have hone : (Q ⊔ J).relIndex T = 1 := by omega
      exact le_antisymm hsupT (relIndex_eq_one.mp hone)
  have hQF : Q ⊔ F = P := by
    change Q ⊔ (J ⊔ A) = P
    rw [←sup_assoc,hQJ,hgen]
  have hindex : F.relIndex P ≤ 2 := by
    rw [←hQF,relIndex_sup_of_normalizes Q F (hFP.trans hQN)]
    have hFT : F.relIndex T ≤ 2 := by
      have hz : J.relIndex T ≠ 0 := by omega
      exact (relIndex_le_of_le_left (show J ≤ F from le_sup_left) hz).trans_eq hi
    let : Finite T := Finite.of_injective (inclusion hTP) (inclusion_injective _)
    have hFTzero : F.relIndex T ≠ 0 := index_ne_zero_of_finite
    exact (relIndex_le_of_le_right hQT hFTzero).trans hFT
  exact ⟨hindex,residual_le_of_index_le_two P F hindex⟩

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- An opposite mover omitting the starting core generates the actual local
two-residual with every actor that generates with its edge. -/
theorem borel_opposite_generation_of_core_not_le (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg))
    (hgen : Q Rg t ⊔ A = stabilizer Rg a)
    (hnot : ¬ Q Rg a ≤ edgeOffenderJoin c t) :
    (edgeOffenderJoin c t ⊔ A).relIndex (stabilizer Rg a) ≤ 2 ∧
      Ltilde Rg a ≤ edgeOffenderJoin c t ⊔ A := by
  obtain ⟨J,_,hJ,_,hJT,hi,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hct
  rw [hJ] at hnot ⊢
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  let := finite_stabilizer Rg a
  exact index_two_opposite_generation (stabilizer Rg a) (Q Rg a) (Q Rg t) J A
    (Q_le_adjacent_h Rg ht hat)
    (fun _ hx => hx.2 _ (adjacent_symm Rg hat)) hJT (Q_normalized Rg a) hi hnot hgen

include h e hz hk in
/-- If a distinct opposite mover contains the starting core, its intersection
with the starting mover has index exactly four over that core. -/
theorem borel_opposite_containing_core_index (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t)
    (hcore : Q Rg a ≤ edgeOffenderJoin c t) :
    (Q Rg a).relIndex (edgeOffenderJoin a t ⊓ edgeOffenderJoin c t) = 4 := by
  obtain ⟨Ja,_,hJa,hQa,hAT,hAi,hQAi,_⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR ha hat
  rcases borel_adjacent_thompson_comparison h e hz hk u hR ha hc hat hct with
    he | ⟨_,hi,_,_⟩
  · exact (hne he).elim
  · rw [hJa] at hi ⊢
    have hmul := relIndex_mul_relIndex (Q Rg a) (Ja ⊓ edgeOffenderJoin c t) Ja
      (le_inf hQa hcore) inf_le_left
    rw [hi,hQAi] at hmul
    omega

include h e hz hk in
private theorem borel_core_not_le_transported_mover (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (hnot : ¬ Q Rg a ≤ edgeOffenderJoin c t)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a) :
    ¬ Q Rg a ≤ edgeOffenderJoin (act Rg g c) (act Rg g t) := by
  intro hn
  have hqa : (Q Rg a).map (MulAut.conj g⁻¹).toMonoidHom = Q Rg a := by
    rw [←Q_act,show act Rg g a = a from hg]
  rw [remaining_edge_join_act h e hz hk u (Or.inr hR) hc hct g,←hqa] at hn
  exact hnot ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hn)

include h e hz hk in
/-- On the same two selected edges, the actual transported opposite movers
both generate the local residual with the unchanged critical seed, unless
the original opposite mover contains the starting two-core. The latter
branch records its exact intersection index four; it is not a terminal
contradiction or the complete alternative (5.5)(c). -/
theorem borel_small_critical_opposite_selectors (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    {c : Vertex Rg} (hc : color Rg c = false)
    (hcb : Adjacent Rg c (p.walk.getVert 1))
    (hne : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ≠
      edgeOffenderJoin c (p.walk.getVert 1)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      ∃ r ∈ L.subgroupOf (L ⊔ R),
        let x := (embedM Rg r)⁻¹
        let J := edgeOffenderJoin (alpha Rg) t
        let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
        ∃ g ∈ stabilizer Rg (alpha Rg),
          act Rg g (p.walk.getVert 1) = t ∧
          (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
          J ⊔ J' = stabilizer Rg (alpha Rg) ∧
          Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
          Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
          Z Rg (p.walk.getVert 1) ⊓ centralizer (J : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          Z Rg (p.walk.getVert 1) ⊓ centralizer (J' : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ((Ltilde Rg (alpha Rg) ≤ edgeOffenderJoin (act Rg g c) t ⊔ Z Rg z ∧
            Ltilde Rg (alpha Rg) ≤
              edgeOffenderJoin (act Rg x (act Rg g c)) (act Rg x t) ⊔ Z Rg z) ∨
            (Q Rg (alpha Rg) ≤ edgeOffenderJoin c (p.walk.getVert 1) ∧
              (Q Rg (alpha Rg)).relIndex
                (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ⊓
                  edgeOffenderJoin c (p.walk.getVert 1)) = 4)) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,_,_,hBfirst,hBsecond,hfix,hfix',_⟩ :=
    borel_small_critical_seed_selectors h e hz hk u hR p hsmall
  let x := (embedM Rg r)⁻¹
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hab hat
  refine ⟨t,hat,r,hr,g,hg,hgt,hgen,hpair,hBfirst,hBsecond,hfix,hfix',?_⟩
  by_cases hcore : Q Rg (alpha Rg) ≤ edgeOffenderJoin c (p.walk.getVert 1)
  · exact Or.inr ⟨hcore,borel_opposite_containing_core_index h e hz hk u hR rfl hc
      hab hcb hne hcore⟩
  · have hcg : color Rg (act Rg g c) = false := by rw [action_preserves_color,hc]
    have hcgt : Adjacent Rg (act Rg g c) t := by
      rw [←hgt]
      exact (adjacent_act_iff Rg g _ _).mpr hcb
    have hcoreg : ¬ Q Rg (alpha Rg) ≤ edgeOffenderJoin (act Rg g c) t := by
      rw [←hgt]
      exact borel_core_not_le_transported_mover h e hz hk u hR hc hcb hcore g hg
    have hx : x ∈ stabilizer Rg (alpha Rg) := by
      change x ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨r⁻¹,by rw [map_inv]⟩
    have hxat : Adjacent Rg (alpha Rg) (act Rg x t) := by
      rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
      exact (adjacent_act_iff Rg x _ _).mpr hat
    have hcx : color Rg (act Rg x (act Rg g c)) = false := by
      rw [action_preserves_color,hcg]
    have hcxt := (adjacent_act_iff Rg x _ _).mpr hcgt
    have hcorex := borel_core_not_le_transported_mover h e hz hk u hR hcg hcgt hcoreg x hx
    exact Or.inl ⟨(borel_opposite_generation_of_core_not_le h e hz hk u hR rfl hcg
      hat hcgt _ hBfirst hcoreg).2,
      (borel_opposite_generation_of_core_not_le h e hz hk u hR rfl hcx
        hxat hcxt _ hBsecond hcorex).2⟩

include h e hz hk in
/-- Every original critical path, with either small or large image, admits
an actual edge transporter giving opposite-mover residual generation or
the precise core-containing branch. -/
theorem borel_critical_opposite_comparison (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    {c : Vertex Rg} (hc : color Rg c = false)
    (hcb : Adjacent Rg c (p.walk.getVert 1))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin c (p.walk.getVert 1)) :
    ∃ t, Adjacent Rg a t ∧ Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      ∃ g ∈ stabilizer Rg a, act Rg g (p.walk.getVert 1) = t ∧
        (Ltilde Rg a ≤ edgeOffenderJoin (act Rg g c) t ⊔ Z Rg z ∨
          (Q Rg a ≤ edgeOffenderJoin c (p.walk.getVert 1) ∧
            (Q Rg a).relIndex
              (edgeOffenderJoin a (p.walk.getVert 1) ⊓
                edgeOffenderJoin c (p.walk.getVert 1)) = 4)) := by
  obtain ⟨t,hat,hgen⟩ := borel_critical_generating_neighbor h e hz hk u hR p
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg a hab hat
  refine ⟨t,hat,hgen,g,hg,hgt,?_⟩
  by_cases hcore : Q Rg a ≤ edgeOffenderJoin c (p.walk.getVert 1)
  · exact Or.inr ⟨hcore,borel_opposite_containing_core_index h e hz hk u hR p.start_color hc
      hab hcb hne hcore⟩
  · have hcg : color Rg (act Rg g c) = false := by rw [action_preserves_color,hc]
    have hcgt : Adjacent Rg (act Rg g c) t := by
      rw [←hgt]
      exact (adjacent_act_iff Rg g _ _).mpr hcb
    have hcoreg : ¬ Q Rg a ≤ edgeOffenderJoin (act Rg g c) t := by
      rw [←hgt]
      exact borel_core_not_le_transported_mover h e hz hk u hR hc hcb hcore g hg
    exact Or.inl (borel_opposite_generation_of_core_not_le h e hz hk u hR p.start_color hcg
      hat hcgt _ hgen hcoreg).2

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
