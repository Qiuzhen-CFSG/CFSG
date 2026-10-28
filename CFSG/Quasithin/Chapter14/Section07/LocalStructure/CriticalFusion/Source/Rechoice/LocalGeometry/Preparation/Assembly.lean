module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary

/-!
# One prepared critical rechoice for 14.7.70

The marked-cover and permitted-choice proofs are assembled on the same actual
critical path, using the original conjugation section and projection. The
literal cubic actor used to mark V supplies the orbit input, and the marked
calculation supplies the upper-space identity needed for the choice. Thus
neither spanning, disjointness, careful placement nor quotient centrality is
an assumption of `exists_prepared_rechoice`.

The earlier full commutator [U,O₂(H)]=V₁ gives both core-commutator bounds,
after conjugating the actual core at the opposite endpoint. The reciprocal
placement and alternating image are transported through the one permitted
rechoice; no element interchanging the two endpoints is used. The resulting
`Prepared` record is an output of these proofs, not an earlier source input.

`exists_prepared_branches` applies the published fixed-line and intersection
consumers in low rank, and constructs the independent rank-three consumer's
literal `Preliminary` interface. Its preceding68 exclusion and marked
disjointness also give Zα not≤V. The rank-three contradiction, E-action and
Goldschmidt arguments remain with the local-geometry and full70 owners.

The remaining explicit inputs are genuine earlier source contracts: the
rank selection and reciprocal39/66 placement/image (qt-14-07), module
separation14.7.2(1) (qt-14-07-solvable), core action14.5.15(4) (qt-14-05),
full commutator14.5.21(2) (qt-14-05-terminal-duality), the literal68 and69
conclusions (qt-14-07-critical-residual-fusion and
qt-14-07-critical-order-two), compatible R₁ marking and local cubic/fixed
actors (qt-14-03 and qt-14-07), and the final consumer's exact14.7.3(4)
conjugacy implication (qt-14-07). The source owner qt-14-07 retains their
final discharge. No additional preparation premise remains.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.5.21(2), printed p.1019, and proof of14.7.70,
printed pp.1073–1074 (PDF pp.1090–1091).
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

omit [Finite G] in
private theorem conjugate_product (A : Subgroup G) (g h : G) :
    conjugate A (g * h) = conjugate (conjugate A g) h := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

include d in
/-- Reciprocal placement survives the same permitted rechoice, since its
actor normalizes the original U. -/
theorem reselect_reciprocal_placement (n : group F L)
    (hUH : F.U ≤ conjugate F.H c.conjugator) :
    F.U ≤ conjugate F.H (c.reselect n).conjugator := by
  have hU : conjugate F.U n = F.U := (conjugate_eq_iff F.U n).mpr
    (d.conjugationSection.normalized (group_le_H n.property))
  rw [c.reselect_conjugator, conjugate_product, ← hU]
  exact map_mono hUH

/-- Transport the actual opposite quotient image through the updated
critical conjugator, retaining the original S₅ marking. -/
theorem reselect_reciprocal_even (n : group F L)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) :
    (F.U.subgroupOf (conjugate F.H (c.reselect n).conjugator)).map
      (reciprocalQuotient d (c.reselect n)) ≤ alternatingGroup (Fin 5) := by
  rintro _ ⟨y, hy, rfl⟩
  have hxU : (n : G) * y * (n : G)⁻¹ ∈ F.U :=
    (mem_normalizer_iff.mp (d.conjugationSection.normalized
      (group_le_H n.property)) y).mp hy
  let x : conjugate F.H c.conjugator := ⟨(n : G) * y * (n : G)⁻¹, hUH hxU⟩
  have he : reciprocalQuotient d c x = reciprocalQuotient d (c.reselect n) y := by
    apply congrArg d.qH
    apply Subtype.ext
    change c.conjugator * ((n : G) * y * (n : G)⁻¹) * c.conjugator⁻¹ =
      (c.reselect n).conjugator * y * (c.reselect n).conjugator⁻¹
    simp only [c.reselect_conjugator, mul_inv_rev, mul_assoc]
  exact heven ⟨x, hxU, he⟩

omit [Finite G] in
/-- The earlier full core commutator14.5.21(2) supplies both bounds used
with F.9.13(6), including the bound at the actual opposite vertex. -/
theorem critical_core_commutator_bounds
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα ∧ ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1 := by
  have hQ : c.Qα = conjugate (F.H.pCoreIn 2) c.conjugator :=
    (map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective).symm
  have hcomm' : ⁅F.H.pCoreIn 2, F.U⁆ = F.Vi 1 :=
    (commutator_comm _ _).trans hcomm
  have hα : ⁅c.Qα, c.Uα⁆ = c.Zα := by
    rw [hQ, CriticalPath.Uα, CriticalPath.Zα]
    simpa only [conjugate, ← map_commutator] using
      congrArg (fun A : Subgroup G => conjugate A c.conjugator) hcomm'
  exact ⟨(commutator_mono inf_le_right le_rfl).trans_eq hα,
    (commutator_mono inf_le_right le_rfl).trans_eq hcomm'⟩

/-- The marked seed's actual diagonal actor supplies the cubic orbit input
with upper-conjugation parameter zero. -/
theorem MarkedSpans.LocalActors.localCubic (actors : MarkedSpans.LocalActors d) :
    PermittedChoice.ActorOrbits.LocalCubic d := by
  obtain ⟨l, hl, a, ha, ha1, he⟩ := actors.cubic
  refine ⟨l, hl, a, ha, ha1, 0, ?_⟩
  have hz : SL2FourNatural.upper 0 = 1 := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [SL2FourNatural.upper]
  simpa only [hz, one_mul, inv_one, mul_one] using he

/-- Output of the opening calculations and permitted choice, on a single
actual path and the original section. Every field is constructed below. -/
structure Prepared (s : d.ActionDescent) : Prop where
  earlier : c.EarlierImages
  selection : c.RankSelection
  star_card : Nat.card (star F c.Uα) = 2
  star_central : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G))
  rank_bound : primeRank 2 d.U₀ ≤ 3
  original_codim : Module.finrank (ZMod 2) (tilde d (F.U ⊓ c.Qα)) + 1 ≥
    Module.finrank (ZMod 2) W
  reciprocal_codim :
    Module.finrank (ZMod 2) ((reciprocalSection d c).imageSpace (c.Uα ⊓ F.H.pCoreIn 2)) + 1 ≥
      Module.finrank (ZMod 2) W
  original_commutator : ⁅F.U ⊓ c.Qα, c.Uα⁆ = c.Zα
  reciprocal_commutator : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ = F.Vi 1
  commutator_le : Fcomm c ≤ F.U ⊓ c.Uα
  opposite_le : c.Zα ≤ Fcomm c
  point_le : F.Vi 1 ≤ Fcomm c
  commutator_normalized : (T : Subgroup G) ≤ normalizer (Fcomm c : Set G)
  commutator_card : Nat.card (Fcomm c) = 8
  commutator_inf : Fcomm c ⊓ d.U₀ = F.Vi 1
  opposite_not_le : ¬ c.Zα ≤ d.U₀
  upper_space : SL2CentralExtension.upperFixed
    (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker
  spanning : tilde d (Fcomm c) ⊔ tilde d V =
    SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient))
  upper_actors : ∀ a : SL2FourNatural.F, alternatingActor d.naturalQuotient
    (SL2FourNatural.upper a) ∈ (actorT (F := F)).map d.qH
  actor : ∃ h : F.H, (h : G) ∈ c.Uα ∧ ∃ t : SL2FourNatural.F, t ≠ 0 ∧
    d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t) ∧
    (∀ x : actorT (F := F), Commute (d.qH (x : F.H)) (d.qH h)) ∧
    tilde d (Fcomm c) = (d.action h - LinearMap.id).range
  careful : primeRank 2 d.U₀ ≤ 2 → c.Zα ≤ F.Vi 2 ⊔ d.U₀
  disjoint_images : primeRank 2 d.U₀ = 3 → Disjoint (tilde d (Fcomm c)) (tilde d V)

/-- Construct one permitted rechoice and discharge all preparation obligations
for it. Only literal earlier source inputs occur among the premises. -/
theorem exists_prepared_rechoice
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (mark : UpperMarking d) (actors : MarkedSpans.LocalActors d)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) :
    ∃ n : group F L, (n : G) ∈ F.Li L 1 ∧
      Prepared d (c.reselect n) (d.actionDescentOfCore hcore) := by
  let s := d.actionDescentOfCore hcore
  have h65 := MarkedSpans.upper_eq_seed_sup_kernel d s mark separation actors
  have hF9 := (critical_core_commutator_bounds c hcomm).1
  obtain ⟨n, hn, hcentral, hplane⟩ :=
    PermittedChoice.exists_permitted_rechoice_with_selected_point d c earlier selection
      h69 separation (actors.localCubic d) hcore hcomm h68 mark h65 hF9
  have earlier' := c.reselect_earlierImages earlier n
  have selection' := reselect_rankSelection d c earlier selection n
  have h69' : Nat.card (star F (c.reselect n).Uα) = 2 :=
    (c.reselect_star_card earlier n).trans h69
  have hUH' := reselect_reciprocal_placement d c n hUH
  obtain ⟨hF9', hF9α'⟩ := critical_core_commutator_bounds (c.reselect n) hcomm
  obtain ⟨hD, hDα, hZ, hP⟩ := opening_commutators d (c.reselect n) earlier' s mark
    selection' h69' hUH' (reselect_reciprocal_even d c n hUH heven)
      hF9' hF9α'
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d (c.reselect n) earlier' mark h69'
  refine ⟨n, hn, {
    earlier := earlier'
    selection := selection'
    star_card := h69'
    star_central := hcentral
    rank_bound := d.U₀_rank_le_three s
    original_codim := original_codimension d (c.reselect n) selection' h69'
    reciprocal_codim := reciprocal_codimension d (c.reselect n) earlier' h69'
    original_commutator := hD
    reciprocal_commutator := hDα
    commutator_le := commutator_le_intersection d (c.reselect n) earlier' hUH'
    opposite_le := hZ
    point_le := hP
    commutator_normalized := T_normalizes_commutator d (c.reselect n) earlier' s mark
      h69' hP hcentral
    commutator_card := commutator_card d (c.reselect n) earlier' s mark h69' hP
    commutator_inf := commutator_inf_U₀ d (c.reselect n) earlier' s mark h69' hP
    opposite_not_le := point_not_le_U₀ d (c.reselect n) h69' h68
    upper_space := h65
    spanning := MarkedSpans.commutator_spans d s (c.reselect n) earlier' mark
      separation actors h69'
    upper_actors := upper_mem_actorT d mark
    actor := ⟨h, hh, t, ht, he, actorT_commutes d (c.reselect n) hcentral h hh,
      commutator_image d (c.reselect n) earlier' s h69' h hh
        (upper_actor_ne_one d h t ht he)⟩
    careful := fun hrank => (hplane hrank).trans le_sup_left
    disjoint_images := MarkedSpans.commutator_disjoint d s (c.reselect n) earlier' mark
      separation actors h69'
  }⟩

namespace Prepared
variable {d c} {s : d.ActionDescent} (p : Prepared d c s)
include p

/-- The published fixed-line theorem applies to the actual actor and careful
choice constructed for this same path. -/
theorem selected_point (separation : d.ModuleSeparation) (hrank : primeRank 2 d.U₀ ≤ 2) :
    c.Zα ≤ F.Vi 2 := by
  obtain ⟨h, _, t, ht, he, hc, hF⟩ := p.actor
  exact selected_point_le_plane d c p.earlier separation s h t ht he hc hF
    p.upper_space p.upper_actors hrank p.opposite_le (p.careful hrank)

/-- Apply the intersection consumer after the literal earlier14.7.3(4)
implication supplies the L-conjugate. No normalization or spanning premise
remains to be supplied by the local-geometry owner. -/
theorem low_rank (separation : d.ModuleSeparation) (hrank : primeRank 2 d.U₀ ≤ 2)
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l) :
    c.Zα ≤ F.Vi 2 ∧ F.U ⊓ c.Uα = d.U₀ ⊔ V ∧
      F.U ⊓ c.Uα = Fcomm c ⊔ V ∧ F.U ⊓ c.Uα = Fcomm c ⊔ d.U₀ ∧
      c.b = 3 ∧ ∃ l ∈ L, c.Uα = conjugate F.U l := by
  have hZ := p.selected_point separation hrank
  obtain ⟨hb, l, hl, heq⟩ := earlier_conjugacy c (hZ.trans (F.le_seed 2))
  obtain ⟨h, hh, t, ht, he, _, hF⟩ := p.actor
  have hmutual : F.U ≤ normalizer (c.Uα : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (p.commutator_le.trans inf_le_right)
  obtain ⟨h₁, h₂, h₃⟩ := intersection_equalities d c p.earlier s h hh t ht he hF
    p.upper_space p.spanning hmutual l hl heq
  exact ⟨hZ, h₁, h₂, h₃, hb, l, hl, heq⟩

/-- Supply every field of the independent rank-three consumer's actual
preliminary interface, including the proved marked disjointness. -/
theorem rank_three (hrank : primeRank 2 d.U₀ = 3) : RankThree.Preliminary d c where
  earlier := p.earlier
  rank_three := hrank
  star_card := p.star_card
  star_central := p.star_central
  commutator_le := p.commutator_le
  point_le := p.point_le
  opposite_le := p.opposite_le
  commutator_normalized := p.commutator_normalized
  commutator_card := p.commutator_card
  commutator_inf := p.commutator_inf
  opposite_not_le := p.opposite_not_le
  disjoint_images := p.disjoint_images hrank

/-- The marked rank-three calculation and the literal preceding68 exclusion
give the point exclusion used on printed p.1074. -/
theorem rank_three_point_not_le_seed (hrank : primeRank 2 d.U₀ = 3) : ¬ c.Zα ≤ V :=
  point_not_le_seed d c p.earlier p.opposite_le p.opposite_not_le (p.disjoint_images hrank)

end Prepared

/-- Final preparation assembly for the local-geometry owner. The same
constructed rechoice supplies the complete low-rank consumer and all the
independent rank-three consumer's preliminary data. The latter branch's
contradiction is deliberately left to its source owner. -/
theorem exists_prepared_branches
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (mark : UpperMarking d) (actors : MarkedSpans.LocalActors d)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l) :
    ∃ n : group F L, (n : G) ∈ F.Li L 1 ∧
      Prepared d (c.reselect n) (d.actionDescentOfCore hcore) ∧
      (primeRank 2 d.U₀ ≤ 2 →
        (c.reselect n).Zα ≤ F.Vi 2 ∧ F.U ⊓ (c.reselect n).Uα = d.U₀ ⊔ V ∧
        F.U ⊓ (c.reselect n).Uα = Fcomm (c.reselect n) ⊔ V ∧
        F.U ⊓ (c.reselect n).Uα = Fcomm (c.reselect n) ⊔ d.U₀ ∧
        c.b = 3 ∧ ∃ l ∈ L, (c.reselect n).Uα = conjugate F.U l) ∧
      (primeRank 2 d.U₀ = 3 →
        RankThree.Preliminary d (c.reselect n) ∧ ¬ (c.reselect n).Zα ≤ V) := by
  obtain ⟨n, hn, p⟩ := exists_prepared_rechoice d c earlier selection h69 separation
    hcore hcomm h68 mark actors hUH heven
  refine ⟨n, hn, p, ?_, fun hrank =>
    ⟨p.rank_three hrank, p.rank_three_point_not_le_seed hrank⟩⟩
  intro hrank
  simpa only [CriticalPath.reselect_b] using p.low_rank separation hrank earlier_conjugacy

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
