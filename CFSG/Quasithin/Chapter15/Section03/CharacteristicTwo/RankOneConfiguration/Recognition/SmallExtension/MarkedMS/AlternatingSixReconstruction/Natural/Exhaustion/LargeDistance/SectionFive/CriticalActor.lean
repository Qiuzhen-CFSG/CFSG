module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PointControl
public import Theory.Representation.NormalElementaryQuotient.FixedIndex
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.ElementaryAbelian.Injective

/-!
# Reverse critical indices for the full symmetric central cover

An elementary image of order at least four contains an even involution.
Its action has fixed index at least four on the entire moved subgroup,
because the natural quotient detects nontrivial alternating action. Transport
through the literal endpoint embeddings gives the reverse critical index
and an actual even actor for the radius chief-factor argument.

Both cover orders are retained; no point-core image is assumed here.
Source: MS93 (5.2)(i), printed pp.913--914. The endpoint transport follows
NaturalSixControl.SymplecticSetup.CriticalEvenActor with the quotient cover.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

/-- A binary elementary subgroup of S6 of order at least four contains an even involution. -/
private theorem exists_even_involution_of_four_le (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hA : 4 ≤ Nat.card A) :
    ∃ a ∈ A, orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hex : ∃ a ∈ A, a ≠ 1 ∧ a ∈ alternatingGroup (Fin 6) := by
    by_contra hn
    push Not at hn
    let f := (Equiv.Perm.sign (α := Fin 6)).comp A.subtype
    have hf : Function.Injective f := by
      apply (injective_iff_map_eq_one f).mpr
      intro a ha
      by_contra hne
      exact hn a a.property (fun hh => hne (Subtype.ext hh)) ha
    have hc := Nat.card_le_card_of_injective f hf
    have htwo : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card,Fintype.card_units_int]
    rw [htwo] at hc
    omega
  obtain ⟨a,ha,hne,heven⟩ := hex
  exact ⟨a,ha,orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne,heven⟩

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

/-- The whole central cover has fixed index at least four under any
large elementary image. No complement to its fixed kernel is chosen. -/
theorem cover_fixedIndex_four_le (A : Subgroup d.overgroup) [IsElementaryAbelian 2 A]
    (hA : 4 ≤ Nat.card (A.map s.projection)) :
    4 ≤ (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) := by
  let := replacementMoved_normal h d
  let := IsElementaryAbelian.map (p := 2) (A := A) s.projection
  obtain ⟨a,haA,ha,heven⟩ := exists_even_involution_of_four_le (A.map s.projection) hA
  have hact : coverAction s a ≠ 1 := by
    intro hzero
    have hn : BinaryPermutation.naturalRepresentation (Fin 6) a = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d) v
      have heq := coverMap_equivariant s a w
      rw [hzero,Module.End.one_apply] at heq
      exact heq.symm
    have heq : a = 1 := BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      (hn.trans (map_one _).symm)
    rw [heq,orderOf_one] at ha
    contradiction
  have hl := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    (coverAction s) ⟨⟨a,heven⟩,hact⟩ a ha heven haA
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (replacementMoved d) s.projection s.surjective
    (s.projection_kernel.trans (moved_centralizer s).symm)]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl

include s in
/-- The native fixed-index bound transported through any faithful ambient embedding. -/
theorem embedded_centralizing_index_four_le {H : Type*} [Group H]
    (i : d.overgroup →* H) (hi : Function.Injective i)
    (A B : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hB : B ≤ centralizer (A : Set H))
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A) :
    4 ≤ B.relIndex ((replacementMoved d).map i) := by
  let A₀ := A.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
  have hmap : A₀.map i = A := map_comap_eq_self hA
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [←hmap,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hcard
    exact hcard
  have hB₀ : B.comap i ≤ centralizer (A₀ : Set d.overgroup) := by
    intro b hb a ha
    apply hi
    simpa only [map_mul] using hB hb (i a) ha
  rw [←relIndex_comap]
  exact (cover_fixedIndex_four_le s A₀ hcard₀).trans
    (relIndex_le_of_le_left hB₀ index_ne_zero_of_finite)

include s in
/-- A large critical image forces a large image in the reverse direction. -/
theorem reverse_critical_image_four_le (hc : DistanceTwo.CentralLayer d)
    (hb : 0 < (replacementGeometry h d).b d.radical) {a e : Vertex d.radical}
    (p : DistanceEight.PathCentrality.CriticalPath d.radical (replacementGeometry h d) a e)
    (hforward : 4 ≤ (Q d.radical e).relIndex (Z d.radical a)) :
    4 ≤ (Q d.radical a).relIndex (Z d.radical e) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.end_color
  let j := (MulAut.conj g⁻¹).toMonoidHom
  let i := j.comp (embedM d.radical)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical)
  have hact : act d.radical g (alpha d.radical) = e := by rw [hg]; simp only [alpha,act_mVertex,one_mul]
  have hQ : (pCore 2 d.overgroup).map i = Q d.radical e := by
    rw [←hact,Q_act,Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),map_map]
  have hU : (replacementMoved d).map i = U d.radical e := by
    rw [←hact,U_act,hc.U_eq_moved,map_map]
  have hG : i.range = stabilizer d.radical e := by
    rw [←hact,stabilizer_act]
    change (j.comp (embedM d.radical)).range = (stabilizer d.radical (mVertex d.radical 1)).map j
    rw [stabilizer_m_base,MonoidHom.range_comp]
    rfl
  have hA : Z d.radical a ≤ i.range := by
    rw [hG]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hB : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  let : IsElementaryAbelian 2 (X d.radical a) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z d.radical a) := IsElementaryAbelian.of_le
    ((replacementGeometry h d).omega_bound a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]
      exact hb))
  have hf : 4 ≤ (Q d.radical a).relIndex (U d.radical e) := by
    rw [←hU]
    apply embedded_centralizing_index_four_le s i hi (Z d.radical a) (Q d.radical a) hA hB
    rwa [hQ]
  let : Finite (stabilizer d.radical e) := finite_stabilizer d.radical e
  let : Finite (Z d.radical e) := Finite.of_injective (inclusion (Z_le_stabilizer d.radical e))
    (inclusion_injective _)
  exact hf.trans (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical e) index_ne_zero_of_finite)

/-- The opposite critical Z-layer supplies the even involution used by the chief budget. -/
theorem exists_even_involution_reverse_critical_image (hc : DistanceTwo.CentralLayer d)
    (hb : 0 < (replacementGeometry h d).b d.radical) {e : Vertex d.radical}
    (p : DistanceEight.PathCentrality.CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) e)
    (hforward : 4 ≤ (Q d.radical e).relIndex (Z d.radical (alpha d.radical))) :
    ∃ a ∈ ((Z d.radical e).comap (embedM d.radical)).map s.projection,
      orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hr := reverse_critical_image_four_le s hc hb p hforward
  have hZe : Z d.radical e ≤ (embedM d.radical).range := by
    change Z d.radical e ≤ Mbar d.radical
    rw [←stabilizer_m_base d.radical]
    apply Z_le_stabilizer_of_dist_le e ((replacementGeometry h d).exists_critical e p.end_color)
    change (cosetGraph d.radical).dist e (alpha d.radical) ≤ _
    rw [SimpleGraph.dist_comm,p.critical.1,(replacementGeometry h d).distance_constant _ p.start_color,
      (replacementGeometry h d).distance_constant _ p.end_color]
  have hmap : ((Z d.radical e).comap (embedM d.radical)).map (embedM d.radical) = Z d.radical e := map_comap_eq_self hZe
  have hcard : 4 ≤ Nat.card (((Z d.radical e).comap (embedM d.radical)).map s.projection) := by
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←hmap,
      relIndex_map_map_of_injective _ _ (embedM_injective d.radical),←s.projection_kernel,relIndex_ker] at hr
    exact hr
  let : IsElementaryAbelian 2 (X d.radical e) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z d.radical e) := IsElementaryAbelian.of_le
    ((replacementGeometry h d).omega_bound e p.end_color (by
      rw [(replacementGeometry h d).distance_constant e p.end_color]
      exact hb))
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM d.radical) (embedM_injective d.radical) (Z d.radical e)
  let := IsElementaryAbelian.map (p := 2) (A := (Z d.radical e).comap (embedM d.radical)) s.projection
  exact exists_even_involution_of_four_le _ hcard
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
