module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MaximalOffenders
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MovingLayer
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalCommutator

/-!
# An even actor in the reverse critical image

An elementary subgroup of S6 of order at least four contains an even
involution. Such an involution has fixed index at least four on the literal
natural module. At the opposite critical endpoint, the starting kernel
centralizes the starting Z-layer, so this fixed-index bound forces the
reverse Z-image to have order at least four. Extracting an even involution
again gives the actor required by the noncentral chief-factor budget.

The endpoint embedding is constructed by conjugating the source embedding.
The final application uses the original characteristic replacement and
its actual critical path.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2)(i), printed pp.913--914.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.NaturalSixControl
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

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

namespace Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
    (s : Source L R W)

omit [Finite M] in
/-- The natural source module is moved with index at least four by a large elementary image. -/
theorem natural_fixedIndex_four_le (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : 4 ≤ Nat.card (A.map s.projection)) :
    4 ≤ (centralizer (A : Set M)).relIndex W := by
  let := IsElementaryAbelian.map (p := 2) (A := A) s.projection
  obtain ⟨a,haA,ha,heven⟩ := exists_even_involution_of_four_le (A.map s.projection) hA
  have hn : Model.rho a ≠ 1 := by
    intro he
    have heq : a = 1 := BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      (he.trans (map_one Model.rho).symm)
    rw [heq,orderOf_one] at ha
    contradiction
  have hl := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    Model.rho ⟨⟨a,heven⟩,hn⟩ a ha heven haA
  rw [s.fixed_index]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph

include s in
/-- The native fixed-index bound transported through any faithful ambient embedding. -/
theorem embedded_centralizing_index_four_le {G : Type*} [Group G]
    (i : M →* G) (hi : Function.Injective i)
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hB : B ≤ centralizer (A : Set G))
    (hcard : 4 ≤ ((pCore 2 M).map i).relIndex A) :
    4 ≤ B.relIndex (W.map i) := by
  let A₀ := A.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
  have hmap : A₀.map i = A := map_comap_eq_self hA
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [←hmap,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hcard
    exact hcard
  have hB₀ : B.comap i ≤ centralizer (A₀ : Set M) := by
    intro b hb a ha
    apply hi
    simpa only [map_mul] using hB hb (i a) ha
  rw [←relIndex_comap]
  exact (s.natural_fixedIndex_four_le A₀ hcard₀).trans
    (relIndex_le_of_le_left hB₀ index_ne_zero_of_finite)

/-- A large critical image forces a large image in the reverse direction. -/
theorem reverse_critical_image_four_le (h : NativeCentralLayer s)
    (hb : 0 < s.geometry.b R) {a e : Vertex R}
    (p : DistanceEight.PathCentrality.CriticalPath R s.geometry a e)
    (hforward : 4 ≤ (Q R e).relIndex (Z R a)) :
    4 ≤ (Q R a).relIndex (Z R e) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R p.end_color
  let j := (MulAut.conj g⁻¹).toMonoidHom
  let i := j.comp (embedM R)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hact : act R g (alpha R) = e := by rw [hg]; simp only [alpha,act_mVertex,one_mul]
  have hQ : (pCore 2 M).map i = Q R e := by
    rw [←hact,Q_act,Q_alpha R s.two_group s.core_le,map_map]
  have hU : W.map i = U R e := by
    rw [←hact,U_act,h.U_eq_module,map_map]
  have hG : i.range = stabilizer R e := by
    rw [←hact,stabilizer_act]
    change (j.comp (embedM R)).range = (stabilizer R (mVertex R 1)).map j
    rw [stabilizer_m_base,MonoidHom.range_comp]
    rfl
  have hA : Z R a ≤ i.range := by
    rw [hG]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hB : Q R a ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a p.start_color))
  let := s.geometry.Z_elementary hb a p.start_color
  have hf : 4 ≤ (Q R a).relIndex (U R e) := by
    rw [←hU]
    apply s.embedded_centralizing_index_four_le i hi (Z R a) (Q R a) hA hB
    rwa [hQ]
  let : Finite (stabilizer R e) := finite_stabilizer R e
  let : Finite (Z R e) := Finite.of_injective (inclusion (Z_le_stabilizer R e))
    (inclusion_injective _)
  exact hf.trans (relIndex_le_of_le_right (DistanceEight.U_le_Z R e) index_ne_zero_of_finite)

/-- The opposite critical Z-layer supplies the even involution used by the chief budget. -/
theorem exists_even_involution_reverse_critical_image (h : NativeCentralLayer s)
    (hb : 0 < s.geometry.b R) {e : Vertex R}
    (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e)
    (hforward : 4 ≤ (Q R e).relIndex (Z R (alpha R))) :
    ∃ a ∈ ((Z R e).comap (embedM R)).map s.projection,
      orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hr := s.reverse_critical_image_four_le h hb p hforward
  have hZe : Z R e ≤ (embedM R).range := by
    change Z R e ≤ Mbar R
    rw [←stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_le e (s.geometry.exists_critical e p.end_color)
    change (cosetGraph R).dist e (alpha R) ≤ _
    rw [SimpleGraph.dist_comm,p.critical.1,s.geometry.distance_constant _ p.start_color,
      s.geometry.distance_constant _ p.end_color]
  have hmap : ((Z R e).comap (embedM R)).map (embedM R) = Z R e := map_comap_eq_self hZe
  have hcard : 4 ≤ Nat.card (((Z R e).comap (embedM R)).map s.projection) := by
    rw [Q_alpha R s.two_group s.core_le,←hmap,
      relIndex_map_map_of_injective _ _ (embedM_injective R),←s.projection_kernel,relIndex_ker] at hr
    exact hr
  let := s.geometry.Z_elementary hb e p.end_color
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM R) (embedM_injective R) (Z R e)
  let := IsElementaryAbelian.map (p := 2) (A := (Z R e).comap (embedM R)) s.projection
  exact exists_even_involution_of_four_le _ hcard
end Source
namespace SourceData
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T)

/-- The original characteristic replacement supplies the required even actor
from its actual forward critical image. -/
theorem reducedSource_critical_even_actor (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) {e : Vertex c.radical}
    (p : DistanceEight.PathCentrality.CriticalPath c.radical
      ((originalSource d h).reduce c).geometry (alpha c.radical) e)
    (hforward : 4 ≤ (Q c.radical e).relIndex (Z c.radical (alpha c.radical))) :
    ∃ a ∈ ((Z c.radical e).comap (embedM c.radical)).map
        ((originalSource d h).reduce c).projection,
      orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  apply Source.exists_even_involution_reverse_critical_image ((originalSource d h).reduce c)
    (reduced_nativeCentralLayer d h c) _ p hforward
  exact ((originalSource d h).reduce c).criticalDistance_pos
end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
