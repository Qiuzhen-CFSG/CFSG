module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCover
public import Theory.Representation.AlternatingSixInvolutionDisplacement

/-!
# Reverse critical actors with the cubic kernel retained

An elementary six-letter image of order at least four contains an even
involution. Its natural quotient moves at least four elements of the entire
initial cover. Transport through the original endpoint embedding forces
reverse critical image order at least four as well, and hence supplies an
even involution in the full reverse seed.

The two-subgroup index is measured modulo Q: E/Q has odd order and changes
no such index. Both cover orders and their fixed attachments are retained.
CubicCentrality uses this actor and also accepts proper restricted reverse
seeds, as required in the exceptional transvection case of the source.
This adapts Natural.Exhaustion.LargeDistance.SectionFive.CriticalActor.
Source: MS93 (5.0), (5.2)(i), printed pp.912--914.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.NaturalSixControl
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (mark : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "T" => edge L R
local notation "π" => CubicAction.projection h mark hz hk
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

/-- A large elementary image moves at least four elements of the entire cover. -/
theorem cover_fixedIndex_four_le (A : Subgroup (L ⊔ R : Subgroup G))
    [IsElementaryAbelian 2 A] (hA : 4 ≤ Nat.card (A.map π)) :
    4 ≤ (centralizer (A : Set (L ⊔ R : Subgroup G))).relIndex (initialMoved L R) := by
  let := IsElementaryAbelian.map (p := 2) (A := A) π
  obtain ⟨a,haA,ha,heven⟩ := exists_even_involution_of_four_le (A.map π) hA
  let ρ := BinaryPermutation.naturalRepresentation (Fin 6)
  have hn : ∃ g : alternatingGroup (Fin 6), ρ g ≠ 1 := by
    refine ⟨⟨a,heven⟩,?_⟩
    intro he
    have hh : a = 1 := BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      (he.trans (map_one ρ).symm)
    rw [hh,orderOf_one] at ha
    contradiction
  have hl := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    ρ hn a ha heven haA
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl).trans
    (CubicEven.natural_index_le_initialMoved h mark hz hk A)

include h mark hz hk in
/-- The native fixed-index bound transported through any faithful ambient embedding. -/
theorem embedded_centralizing_index_four_le {H : Type*} [Group H]
    (i : (L ⊔ R : Subgroup G) →* H) (hi : Function.Injective i)
    (A B : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hB : B ≤ centralizer (A : Set H))
    (hcard : 4 ≤ ((pCore 2 (L ⊔ R : Subgroup G)).map i).relIndex A) :
    4 ≤ B.relIndex ((initialMoved L R).map i) := by
  let A₀ := A.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
  have hmap : A₀.map i = A := map_comap_eq_self hA
  have hcard₀ : 4 ≤ Nat.card (A₀.map π) := by
    rw [CubicAction.permutation_image_card_of_two h mark hz hk A₀
      (IsElementaryAbelian.isPGroup 2 A₀)]
    rwa [←hmap,relIndex_map_map_of_injective _ _ hi] at hcard
  have hB₀ : B.comap i ≤ centralizer (A₀ : Set (L ⊔ R : Subgroup G)) := by
    intro b hb a ha
    apply hi
    simpa only [map_mul] using hB hb (i a) ha
  rw [←relIndex_comap]
  exact (cover_fixedIndex_four_le h mark hz hk A₀ hcard₀).trans
    (relIndex_le_of_le_left hB₀ index_ne_zero_of_finite)

include h mark hz hk in
/-- A large critical image forces a large image in the reverse direction. -/
theorem reverse_critical_image_four_le (hb : 0 < (sourceGeometry h).b T) {a e : Vertex T}
    (p : DistanceEight.PathCentrality.CriticalPath T (sourceGeometry h) a e)
    (hforward : 4 ≤ (Q T e).relIndex (Z T a)) :
    4 ≤ (Q T a).relIndex (Z T e) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color T p.end_color
  let j := (MulAut.conj g⁻¹).toMonoidHom
  let i := j.comp (embedM T)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective T)
  have hact : act T g (alpha T) = e := by rw [hg]; simp only [alpha,act_mVertex,one_mul]
  have hQ : (pCore 2 (L ⊔ R : Subgroup G)).map i = Q T e := by
    rw [←hact,Q_act,Q_alpha T (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le),map_map]
  have hU : (initialMoved L R).map i = U T e := by
    rw [←hact,U_act,←graph_U_map h mark hz,map_map]
  have hG : i.range = stabilizer T e := by
    rw [←hact,stabilizer_act]
    change (j.comp (embedM T)).range = (stabilizer T (mVertex T 1)).map j
    rw [stabilizer_m_base,MonoidHom.range_comp]
    rfl
  have hA : Z T a ≤ i.range := by
    rw [hG]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hB : Q T a ≤ centralizer (Z T a : Set (FreeAmalgam T)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T a p.start_color))
  let : IsElementaryAbelian 2 (X T a) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z T a) := IsElementaryAbelian.of_le
    ((sourceGeometry h).omega_bound a p.start_color (by
      rw [(sourceGeometry h).distance_constant a p.start_color]
      exact hb))
  have hf : 4 ≤ (Q T a).relIndex (U T e) := by
    rw [←hU]
    apply embedded_centralizing_index_four_le h mark hz hk i hi (Z T a) (Q T a) hA hB
    rwa [hQ]
  let : Finite (stabilizer T e) := finite_stabilizer T e
  let : Finite (Z T e) := Finite.of_injective (inclusion (Z_le_stabilizer T e))
    (inclusion_injective _)
  have hUZ : U T e ≤ Z T e := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (Z_normalized T e))
  exact hf.trans (relIndex_le_of_le_right hUZ index_ne_zero_of_finite)

/-- The opposite critical Z-layer supplies the even involution used by the chief budget. -/
theorem exists_even_involution_reverse_critical_image (hb : 0 < (sourceGeometry h).b T) {e : Vertex T}
    (p : DistanceEight.PathCentrality.CriticalPath T (sourceGeometry h) (alpha T) e)
    (hforward : 4 ≤ (Q T e).relIndex (Z T (alpha T))) :
    ∃ a ∈ ((Z T e).comap (embedM T)).map π,
      orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hr := reverse_critical_image_four_le h mark hz hk hb p hforward
  have hZe : Z T e ≤ (embedM T).range := by
    change Z T e ≤ Mbar T
    rw [←stabilizer_m_base T]
    apply Z_le_stabilizer_of_dist_le e ((sourceGeometry h).exists_critical e p.end_color)
    change (cosetGraph T).dist e (alpha T) ≤ _
    rw [SimpleGraph.dist_comm,p.critical.1,(sourceGeometry h).distance_constant _ p.start_color,
      (sourceGeometry h).distance_constant _ p.end_color]
  have hmap : ((Z T e).comap (embedM T)).map (embedM T) = Z T e := map_comap_eq_self hZe
  let : IsElementaryAbelian 2 (X T e) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z T e) := IsElementaryAbelian.of_le
    ((sourceGeometry h).omega_bound e p.end_color (by
      rw [(sourceGeometry h).distance_constant e p.end_color]
      exact hb))
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM T) (embedM_injective T) (Z T e)
  let := IsElementaryAbelian.map (p := 2) (A := (Z T e).comap (embedM T)) π
  have hcard : 4 ≤ Nat.card (((Z T e).comap (embedM T)).map π) := by
    rw [CubicAction.permutation_image_card_of_two h mark hz hk _
      (IsElementaryAbelian.isPGroup 2 _)]
    rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,←hmap,
      relIndex_map_map_of_injective _ _ (embedM_injective T)] at hr
    exact hr
  exact exists_even_involution_of_four_le _ hcard
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
