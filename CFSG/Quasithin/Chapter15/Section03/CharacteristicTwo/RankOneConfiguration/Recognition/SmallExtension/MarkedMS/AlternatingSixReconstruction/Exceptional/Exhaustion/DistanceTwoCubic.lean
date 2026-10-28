module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CriticalOffenders
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Conjugacy

/-!
# Cubic-kernel distance-two exclusions

At a critical pair of distance two the opposite Q lies in the base vertex
stabilizer and centralizes the endpoint X. A self-centralizing image in the
actual natural actor therefore controls its entire action on the base X,
including the fixed attachment. Frattini detection gives whole-core
exhaustion, contradicting the retained cubic kernel.

This excludes the A₆-image case and both rank-three elementary image types.
In the remaining S₆ case every critical image has order at most four; a
favorable pair has exact displacement on the canonical natural quotient.
The smaller-image and larger-distance branches remain with reconstruction.
The applications in Source retain the entire intrinsic blockU.

Source: MS93 (3.3), pp.866--868, and (3.6), pp.870--872;
Aschbacher--Smith B.3.2, pp.83--84, for the six-letter offender catalogue.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)

/-- Reverse and translate the critical pair to use a bound on the opposite
Q-action. This preserves the original graph and intrinsic whole core. -/
theorem coreExhaustion_of_opposite_critical_bound
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hb : ⁅Q T c,X T (alpha T)⁆ ≤ ⁅X T c,X T (alpha T)⁆) : CoreExhaustion L R := by
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hcCol
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hgcCol : color T (act T g⁻¹ c) = false := by rw [hg]; rfl
  have hc' := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hcCol)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hgcCol)).mpr hr
  have hd : CriticalPair T (alpha T) (act T g⁻¹ (alpha T))
      ((sourceGeometry h).exists_critical (alpha T) rfl) := by simpa only [hg] using hc'
  have hm := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hb
  rw [map_commutator,map_commutator,←Q_act,←X_act,←X_act,hg] at hm
  apply coreExhaustion_of_critical_comparison h e hz (act T g⁻¹ (alpha T)) hd
  have hZ := (sourceGeometry h).omega_bound (act T g⁻¹ (alpha T))
    (critical_endpoint_color T (alpha T) rfl _ hd) (by
      rw [(sourceGeometry h).distance_constant _ (critical_endpoint_color T (alpha T) rfl _ hd)]
      exact sourceDistance_pos h)
  exact ((commutator_mono le_rfl hZ).trans hm).trans le_sup_right

namespace CubicAction
open scoped commutatorElement IsMulCommutative

private theorem commutator_le_of_image_le
    {H I : Type*} [Group H] [Group I] (f : H →* I)
    (A B X : Subgroup H) (hk : f.ker ≤ centralizer (X : Set H))
    (hab : A.map f ≤ B.map f) : ⁅A,X⁆ ≤ ⁅B,X⁆ := by
  apply commutator_le.mpr
  intro a ha x hx
  obtain ⟨b,hb,hba⟩ := hab (mem_map_of_mem f ha)
  have he : b⁻¹*a ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hba,inv_mul_cancel]
  have hc := hk he x hx
  have heq : ⁅a,x⁆ = ⁅b,x⁆ := by
    simp only [commutatorElement_def]
    calc a*x*a⁻¹*x⁻¹ = b*((b⁻¹*a)*x*(b⁻¹*a)⁻¹)*b⁻¹*x⁻¹ := by group
         _ = b*x*b⁻¹*x⁻¹ := by rw [←hc,mul_inv_cancel_right]
  rw [heq]
  exact commutator_mem_commutator hb hx

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "π" => projection h e hz hk
local notation "ρ₆" => BinaryPermutation.naturalRepresentation (Fin 6)

/-- A critical image that is self-centralizing in the actual natural actor
controls the opposite Q-action on the entire X-layer. -/
private theorem distanceTwo_commutator_bound_of_centralizer
    (hb : sourceDistance h = 2)
    (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hself : (π).range ⊓ centralizer (graphImage h e hz hk (X T c) : Set _) =
      graphImage h e hz hk (X T c)) :
    ⁅Q T c,X T (alpha T)⁆ ≤ ⁅X T c,X T (alpha T)⁆ := by
  obtain ⟨t,hat,hct,_,_⟩ := distanceTwo_source_actor h e hb c hc
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hat
    change false ≠ color T t at hh
    cases hcol : color T t <;> simp_all
  have hQc : Q T c ≤ stabilizer T (alpha T) :=
    (Q_le_adjacent_h T ht hct).trans (fun _ hx => hx.2 (alpha T) (adjacent_symm T hat))
  have hXc : X T c ≤ stabilizer T (alpha T) := (omegaCenter_le (Q T c)).trans hQc
  have hi : graphImage h e hz hk (Q T c) ≤ graphImage h e hz hk (X T c) := by
    rw [←hself]
    refine le_inf ?_ ?_
    · exact map_le_range _ _
    · rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩
      have hh := (Q_le_centralizer_X T c hy) (embedM T x) hx
      have heq : x*y = y*x := (embedM_injective T) (by simpa only [map_mul] using hh)
      simpa only [map_mul] using congrArg π heq
  have hker : (π).ker ≤ centralizer (centralOmega L R : Set M) := by
    rw [projection_kernel,←hk]
  have hcomm := commutator_le_of_image_le π
    ((Q T c).comap (embedM T)) ((X T c).comap (embedM T)) (centralOmega L R) hker hi
  have hm := map_mono (f := embedM T) hcomm
  rw [map_commutator,map_commutator,
    map_comap_eq_self (hQc.trans_eq (stabilizer_m_base T)),
    map_comap_eq_self (hXc.trans_eq (stabilizer_m_base T)),←graph_X h] at hm
  exact hm

open ChapterB.Offenders.Six in
private theorem threePair_centralizing_words : ∀ g : Equiv.Perm (Fin 6),
    g * planeWords 4 1 = planeWords 4 1 * g →
    g * planeWords 4 2 = planeWords 4 2 * g →
    ∃ i : Fin 8, dWords i = g := by decide +kernel

open ChapterB.Offenders ChapterB.Offenders.Six in
private theorem threePair_centralizer :
    centralizer (D 6 : Set (Equiv.Perm (Fin 6))) = D 6 := by
  apply le_antisymm
  · intro g hg
    have h1 := hg (planeWords 4 1) (((mem_evenPart_iff _).mpr ⟨1,rfl⟩).1)
    have h2 := hg (planeWords 4 2) (((mem_evenPart_iff _).mpr ⟨2,rfl⟩).1)
    obtain ⟨i,hi⟩ := threePair_centralizing_words g h1.symm h2.symm
    exact (mem_disjointTranspositions_iff 3 g).mpr ⟨i,hi⟩
  · intro g hg a ha
    let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions 3
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : D 6) ⟨g,hg⟩)

open ChapterB.Offenders ChapterB.Offenders.Six in
private theorem evenPart_centralizer :
    alternatingGroup (Fin 6) ⊓ centralizer (evenPart 6 : Set (Equiv.Perm (Fin 6))) =
      evenPart 6 := by
  apply le_antisymm
  · intro g hg
    have h1 := hg.2 (planeWords 4 1) ((mem_evenPart_iff _).mpr ⟨1,rfl⟩)
    have h2 := hg.2 (planeWords 4 2) ((mem_evenPart_iff _).mpr ⟨2,rfl⟩)
    obtain ⟨i,hi⟩ := threePair_centralizing_words g h1.symm h2.symm
    exact ⟨(mem_disjointTranspositions_iff 3 g).mpr ⟨i,hi⟩,hg.1⟩
  · intro g hg
    refine ⟨hg.2,?_⟩
    let := isElementaryTwo_evenPart.2
    intro a ha
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : evenPart 6) ⟨g,hg⟩)

open ChapterB.Offenders in
private theorem conjugate_evenPart_centralizer {A : Subgroup (Equiv.Perm (Fin 6))}
    (hA : IsConjugateTo A (evenPart 6)) :
    alternatingGroup (Fin 6) ⊓ centralizer (A : Set (Equiv.Perm (Fin 6))) = A := by
  obtain ⟨g,rfl⟩ := hA
  let f := (MulAut.conj g).toMonoidHom
  apply le_antisymm
  · intro x hx
    let y := (MulAut.conj g).symm x
    have hy : y ∈ alternatingGroup (Fin 6) ⊓
        centralizer (evenPart 6 : Set (Equiv.Perm (Fin 6))) := by
      constructor
      · exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem x hx.1 g⁻¹
      · intro a ha
        apply (MulAut.conj g).injective
        rw [map_mul, map_mul]
        have hf : (MulAut.conj g) y = x := (MulAut.conj g).apply_symm_apply x
        rw [hf]
        exact hx.2 _ (mem_map_of_mem f ha)
    rw [evenPart_centralizer] at hy
    exact ⟨y, hy, (MulAut.conj g).apply_symm_apply x⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨(inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a ha.2 g, ?_⟩
    rintro b ⟨c, hc, rfl⟩
    have hcomm := ((show a ∈ alternatingGroup (Fin 6) ⊓
        centralizer (evenPart 6 : Set (Equiv.Perm (Fin 6))) by
      rw [evenPart_centralizer]; exact ha).2 c hc)
    simpa only [map_mul] using congrArg f hcomm

private theorem selfCentralizer_map {H : Type*} [Group H] (A : Subgroup H)
    (hA : centralizer (A : Set H) = A) (g : H) :
    centralizer (A.map (MulAut.conj g).toMonoidHom : Set H) =
      A.map (MulAut.conj g).toMonoidHom := by
  have hh := map_inf_centralizer_of_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective ⊤ A
  rw [map_top_of_surjective _ (MulAut.conj g).surjective,top_inf_eq,top_inf_eq,hA] at hh
  exact hh

open ChapterB.Offenders in
private theorem conjugate_threePair_centralizer {A : Subgroup (Equiv.Perm (Fin 6))}
    (hA : IsConjugateTo A (D 6)) : centralizer (A : Set (Equiv.Perm (Fin 6))) = A := by
  obtain ⟨g,rfl⟩ := hA
  exact selfCentralizer_map _ threePair_centralizer g

open ChapterB.Offenders ChapterB.Offenders.Six in
private theorem exceptional_centralizer :
    centralizer (exceptional 6 (by decide) : Set (Equiv.Perm (Fin 6))) =
      exceptional 6 (by decide) := by
  have words : ∀ g : Equiv.Perm (Fin 6),
      g * exceptionalWords 1 = exceptionalWords 1 * g →
      g * exceptionalWords 2 = exceptionalWords 2 * g →
      g * exceptionalWords 4 = exceptionalWords 4 * g →
      ∃ i : Fin 8, exceptionalWords i = g := by decide +kernel
  apply le_antisymm
  · intro g hg
    have h1 := hg (exceptionalWords 1) ((mem_exceptional_iff _).mpr ⟨1,rfl⟩)
    have h2 := hg (exceptionalWords 2) ((mem_exceptional_iff _).mpr ⟨2,rfl⟩)
    have h4 := hg (exceptionalWords 4) ((mem_exceptional_iff _).mpr ⟨4,rfl⟩)
    exact (mem_exceptional_iff _).mpr (words g h1.symm h2.symm h4.symm)
  · intro g hg a ha
    let := isElementaryTwo_exceptional.2
    exact congrArg Subtype.val
      (mul_comm (⟨a,ha⟩ : exceptional 6 (by decide)) ⟨g,hg⟩)

open ChapterB.Offenders ChapterB.Offenders.Six in
private theorem rankThree_centralizer {A : Subgroup (Equiv.Perm (Fin 6))}
    (ha : IsElementaryTwo A) (hr : rank A = 3) : centralizer (A : Set _) = A := by
  rcases elementaryTwo_conjugacy ha with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · have hh := hc.rank_eq
    rw [rank_A1,hr] at hh
    omega
  · have hh := hc.rank_eq
    rw [rank_A2,hr] at hh
    omega
  · exact conjugate_threePair_centralizer hc
  · obtain ⟨g,rfl⟩ := hc
    exact selfCentralizer_map _ exceptional_centralizer g
  · have hh := hc.rank_eq
    rw [rank_evenPart,hr] at hh
    omega
  · have hh := hc.rank_eq
    rw [rank_plus,hr] at hh
    omega
  · have hh := hc.rank_eq
    rw [rank_double,hr] at hh
    omega
  · have hh := hc.rank_eq
    rw [rank_triple,hr] at hh
    omega
  · have hh := hc.rank_eq
    rw [rank_klein,hr] at hh
    omega
  · have hh := hc.rank_eq
    rw [rank_twisted,hr] at hh
    omega

/-- Every rank-three critical image bounds the entire opposite Q-action. -/
theorem distanceTwo_rankThree_commutator_bound
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hi : rank (graphImage h e hz hk (X T c)) = 3) :
    ⁅Q T c,X T (alpha T)⁆ ≤ ⁅X T c,X T (alpha T)⁆ := by
  apply distanceTwo_commutator_bound_of_centralizer h e hz hk hb c hc
  rw [rankThree_centralizer (critical_image_data h e hz hk c hc).1 hi]
  exact inf_eq_right.mpr (map_le_range _ _)

/-- Rank three at a critical endpoint exhausts the literal whole core. -/
theorem coreExhaustion_of_distanceTwo_rankThree
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hi : rank (graphImage h e hz hk (X T c)) = 3) : CoreExhaustion L R :=
  coreExhaustion_of_opposite_critical_bound h e hz c hc
    (distanceTwo_rankThree_commutator_bound h e hz hk hb c hc hi)

/-- At distance two, an even critical offender controls the opposite
Q-action on all of X, including the fixed attachment. -/
theorem distanceTwo_even_commutator_bound
    (hb : sourceDistance h = 2)
    (himage : (π).range = alternatingGroup (Fin 6))
    (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (ho : IsOffender ρ₆ (graphImage h e hz hk (X T c))) :
    ⁅Q T c,X T (alpha T)⁆ ≤ ⁅X T c,X T (alpha T)⁆ := by
  apply distanceTwo_commutator_bound_of_centralizer h e hz hk hb c hc
  rw [himage]
  apply conjugate_evenPart_centralizer
  apply (ChapterB.Offenders.Six.caseBFamily_even_iff _).mp
  refine ⟨(ChapterB.Offenders.Six.isOffender_natural_iff _).mp ho,?_⟩
  rw [←himage]
  exact map_le_range _ _

/-- The entire exceptional core is exhausted in the distance-two cubic
branch when the actual natural quotient actor is A₆. -/
theorem coreExhaustion_of_distanceTwo_even
    (hb : sourceDistance h = 2)
    (himage : (π).range = alternatingGroup (Fin 6)) : CoreExhaustion L R := by
  obtain ⟨c,hc,ho⟩ := exists_critical_offender h e hz hk
  exact coreExhaustion_of_opposite_critical_bound h e hz c hc
    (distanceTwo_even_commutator_bound h e hz hk hb himage c hc ho)

include h hz hk in
private theorem not_coreExhaustion (hx : CoreExhaustion L R) : False := by
  have he : extensionKernel h = pCore 2 M := hk.symm.trans (centralOmega_centralizer h hx)
  have hi := extensionKernel_core_index h hz
  have htop : pCore 2 (extensionKernel h) = ⊤ := by
    apply map_injective (extensionKernel h).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact (extensionKernel_twoCore h).trans he.symm
  rw [htop,index_top] at hi
  norm_num at hi

/-- Exhaustion contradicts the retained cubic initial kernel. -/
theorem not_distanceTwo_even
    (hb : sourceDistance h = 2)
    (himage : (π).range = alternatingGroup (Fin 6)) : False :=
  not_coreExhaustion h hz hk
    (coreExhaustion_of_distanceTwo_even h e hz hk hb himage)

/-- A critical image of rank three is impossible with the cubic initial kernel. -/
theorem not_distanceTwo_rankThree
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hi : rank (graphImage h e hz hk (X T c)) = 3) : False :=
  not_coreExhaustion h hz hk
    (coreExhaustion_of_distanceTwo_rankThree h e hz hk hb c hc hi)

/-- In the remaining cubic distance-two branch, every critical endpoint has
image of order at most four under the actual natural quotient map. -/
theorem critical_image_card_le_four_of_distanceTwo
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    Nat.card (graphImage h e hz hk (X T c)) ≤ 4 := by
  have hel := (critical_image_data h e hz hk c hc).1
  have hr := ChapterB.Offenders.Six.rank_le_three hel
  have hn := not_distanceTwo_rankThree h e hz hk hb c hc
  have htwo : rank (graphImage h e hz hk (X T c)) ≤ 2 :=
    Nat.le_of_lt_succ (lt_of_le_of_ne hr hn)
  rw [hel.card_eq_two_pow_rank]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) htwo).trans_eq (by norm_num)

/-- A favorable critical pair has exact displacement on the natural
quotient. In particular, the fixed central attachment contributes no extra
displacement for this pair; its actual quotient image has order at most four. -/
theorem exists_distanceTwo_tight_offender (hb : sourceDistance h = 2) :
    ∃ c : Vertex T,
      CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl) ∧
      IsOffender ρ₆ (graphImage h e hz hk (X T c)) ∧
      Nat.card (graphImage h e hz hk (X T c)) ≤ 4 ∧
      2 ^ fixedCodim ρ₆ (graphImage h e hz hk (X T c)) =
        Offenders.displacement (X T (alpha T)) (X T c) := by
  obtain ⟨c,hc,hcomp⟩ := exists_base_favorable_critical_pair h e
  have ho := critical_offender_of_comparison h e hz hk c hc hcomp
  have hn : ¬ IsStrongOffender ρ₆ (graphImage h e hz hk (X T c)) := by
    intro hs
    have hh := (ChapterB.Offenders.Six.isStrongOffender_natural_iff _).mp hs
    exact not_distanceTwo_rankThree h e hz hk hb c hc
      (hh.rank_eq.trans ChapterB.Offenders.Six.rank_D)
  have heq : fixedCodim ρ₆ (graphImage h e hz hk (X T c)) =
      rank (graphImage h e hz hk (X T c)) := by
    apply Nat.le_antisymm ho.2
    exact Nat.le_of_not_gt (fun hl => hn ⟨ho.1,hl⟩)
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  have hE := critical_X_le_vertex h e c hcCol (alpha T) hr
  refine ⟨c,hc,ho,critical_image_card_le_four_of_distanceTwo h e hz hk hb c hc,?_⟩
  apply le_antisymm (graphImage_index_le h e hz hk (X T c) hE)
  rw [heq,←ho.1.card_eq_two_pow_rank,graphImage_card h e hz hk (X T c) hE]
  exact hcomp

/-- At distance two a cubic initial kernel forces the full S₆ action on
the natural central quotient. The derived-image case is excluded above. -/
theorem projection_surjective_of_distanceTwo (hb : sourceDistance h = 2) :
    Function.Surjective (projection h e hz hk) :=
  (range_alternatives h e hz hk).resolve_left
    (fun himage => not_distanceTwo_even h e hz hk hb himage)

end CubicAction
end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
