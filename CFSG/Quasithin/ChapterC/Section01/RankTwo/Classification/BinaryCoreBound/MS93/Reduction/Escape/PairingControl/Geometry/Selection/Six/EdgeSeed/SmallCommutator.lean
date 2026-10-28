module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Preliminaries
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Symmetry.SmallAction

/-!
# The actual small commutator on a native edge intersection

For each neighbor d of t, [Z_d,Q_a] has order at most four. If d moves,
step (3) identifies it with the common edge plane. Otherwise its local
normality and the genuine SL3(2) quotient force it into the fixed core.
Generation by neighboring Z-layers gives [V_t,Q_a] inside the edge plane
joined with the fixed core. The commutator on Vcirc_a intersect V_t lies
in U_a, so the disjoint fixed summand disappears.

The imported small-action theorem is a finite-group result for an arbitrary
SL3(2) quotient with a two-group kernel; no propagation conclusion is used.
The distance-two cardinal calculation extends the proof in PairingControl.Basic
by retaining only the distance hypothesis actually needed there.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(3)--(5), pp.883--885,
and the small-commutator premise of (1.7), p.847.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

theorem distance_two_commutator_card_le_four (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {a d : Vertex R} (ha : color R a = false) (hdcolor : color R d = false) (hd : (cosetGraph R).dist a d = 2) :
    Nat.card (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  have hQa : Q R a ≤ stabilizer R d := Q_le_stabilizer_of_dist_two R a d ha hd
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hUQ : U R d ≤ Q R a :=
    (U_le_Z d).trans ((show Z R d ≤ V R a from le_iSup_of_le d (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hd]) le_rfl)).trans (geometry.V_le_Q hb a ha))
  have hcomm : ⁅Z R d, Q R a⁆ = ⁅U R d, Q R a⁆ := by
    rw [commutator_comm (Z R d), commutator_comm (U R d)]
    symm
    apply commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (s.decomposition_at d hdcolor).symm)
    · exact inf_le_right.trans (centralizer_le hQa)
    · exact hUQ.trans (Q R a).le_normalizer
  have hnorm : Q R a ≤ normalizer (U R d : Set (FreeAmalgam R)) :=
    hQa.trans (U_normalized d)
  have hle : ⁅U R d, Q R a⁆ ≤ U R d :=
    le_normalizer_iff_commutator_le_left.mp hnorm
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at d hdcolor]; decide)
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hne : ⁅U R d, Q R a⁆ ≠ U R d := by
    intro heq
    have hbot : U R d ≤ ⊥ := le_of_le_sup_commutator_of_isNilpotent
      (Q R a) (U R d) ⊥ (Q R a)
      (Q_isPGroup R source.two_group source.core_le a ha).isNilpotent
      hUQ bot_le le_rfl le_normalizer_of_normal
      (by simpa only [bot_sup_eq, heq] using (le_refl (U R d)))
    have hc := modules.natural.card_at d hdcolor
    rw [le_bot_iff.mp hbot, card_bot] at hc
    omega
  have hcardne : Nat.card (⁅U R d, Q R a⁆ : Subgroup (FreeAmalgam R)) ≠ 8 := by
    intro hc
    exact hne (eq_of_le_of_card_ge hle (by rw [hc, modules.natural.card_at d hdcolor]))
  have hdiv := card_dvd_of_le hle
  rw [modules.natural.card_at d hdcolor] at hdiv
  have hdivs := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdivs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdivs
  rw [hcomm]
  omega

omit [Finite M] in
private theorem neighbor_distance_two {a t d : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hne : a ≠ d) : (cosetGraph R).dist a d = 2 := by
  have hd : color R d = false := by
    have h₁ := adjacent_color_ne R hat
    have h₂ := adjacent_color_ne R hdt
    cases ht : color R t <;> cases hd : color R d <;> simp_all
  have hlow := (cosetGraph_connected R).one_lt_dist_of_ne_of_not_adj hne (by
    intro h
    exact (adjacent_color_ne R ((cosetGraph_adj R _ _).mp h)) (ha.trans hd.symm))
  have hupp := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := d)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat),
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))] at hupp
  omega

theorem fixed_neighbor_commutator_le_fixedCore (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {a d : Vertex R}
    (ha : color R a = false) (hdcolor : color R d = false)
    (hd : (cosetGraph R).dist a d = 2)
    (hB : Z R d ≤ B R a (geometry.Z_normal a)) :
    ⁅Z R d, Q R a⁆ ≤ fixedCore R a := by
  let S := stabilizer R a
  let K := ⁅Z R d, Q R a⁆
  have hZQ : Z R d ≤ Q R a :=
    (show Z R d ≤ V R a from le_iSup_of_le d
      (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hd]) le_rfl)).trans
        (geometry.V_le_Q hb a ha)
  have hKQ : K ≤ Q R a := (commutator_mono hZQ le_rfl).trans (commutator_le_self _)
  have hKS : K ≤ S := hKQ.trans (fun _ hx => hx.1)
  let := finite_stabilizer R a
  let : (K.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (FirstPairing.StepThree.fixed_subgroup_commutator_normalized source hb ha hB)
  obtain ⟨o⟩ := facts.opposite a ha
  have hsmall : Nat.card (K.subgroupOf S) ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv]
    exact distance_two_commutator_card_le_four source hb modules ha hdcolor hd
  have hz := Propagation.Backward.Moving.Symmetry.small_normal_centralizes_residual
    o.projection o.surjective (by
      rw [o.kernel]
      exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype)
    (K.subgroupOf S) hsmall
  have hz' := congrArg (Subgroup.map S.subtype) hz
  rw [map_commutator, map_subgroupOf_eq_of_le hKS, Subgroup.map_bot] at hz'
  exact le_inf hKQ (commutator_eq_bot_iff_le_centralizer.mp hz')

theorem native_edge_commutator_le_sup (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ⁅V R t, Q R a⁆ ≤ edgeDisplacement a t ⊔ fixedCore R a := by
  let E := edgeDisplacement a t
  let D := fixedCore R a
  let N := E ⊔ D
  have hEZ : E ≤ Z R a := (Initial.edge_le_natural source a t ha hat).trans (U_le_Z a)
  have hnorm : Q R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    apply (le_inf _ _).trans (normalizer_inf_normalizer_le_normalizer_sup E D)
    · exact ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes a ha))).trans (centralizer_le hEZ)).trans
          (Subgroup.centralizer_le_normalizer _)
    · exact (show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (fixedCore_normalized a)
  have hgen : V R t ≤ commutatorPreimage (Q R a) (Q R a) N := by
    apply Initial.Consequences.V_le_of_h_neighbors ha hat
    intro d hdt
    have hlocal : Z R d ≤ Q R a :=
      (show Z R d ≤ V R t from le_iSup_of_le d (le_iSup_of_le (by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)]
        decide) le_rfl)).trans
        ((Initial.Consequences.edge_radius_le_radius ha hat).trans (geometry.V_le_Q hb a ha))
    apply le_commutatorPreimage hlocal
    by_cases heq : d = a
    · subst d
      rw [geometry.centralizes a ha]
      exact bot_le
    have hd : (cosetGraph R).dist a d = 2 := neighbor_distance_two ha hat hdt (Ne.symm heq)
    have hdcolor : color R d = false := by
      have h₁ := adjacent_color_ne R hat
      have h₂ := adjacent_color_ne R hdt
      cases ht : color R t <;> cases hdc : color R d <;> simp_all
    by_cases hB : Z R d ≤ B R a (geometry.Z_normal a)
    · exact (fixed_neighbor_commutator_le_fixedCore source hb modules facts ha hdcolor hd hB).trans
        le_sup_right
    · have hmov : d ∈ movingNeighbors geometry a := ⟨hd, hB⟩
      rw [FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega)
        initial bad a t d ha hat hdt hmov, facts.edge_eq a t d ha hat hdt hmov]
      exact le_sup_left
  exact (commutator_mono hgen le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnorm)

theorem native_intersection_commutator_le_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ⁅Vcirc R a ⊓ V R t, Q R a⁆ ≤ edgeDisplacement a t := by
  have hU : ⁅Vcirc R a ⊓ V R t, Q R a⁆ ≤ U R a :=
    (commutator_mono inf_le_left le_rfl).trans (facts.H_eq_U a ha).le
  have hE : ⁅Vcirc R a ⊓ V R t, Q R a⁆ ≤ edgeDisplacement a t ⊔ fixedCore R a :=
    (commutator_mono inf_le_right (le_refl (Q R a))).trans
    (native_edge_commutator_le_sup source hb modules initial facts p bad ha hat)
  have hEU := Initial.edge_le_natural source a t ha hat
  have hnorm : edgeDisplacement a t ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    ((hEU.trans (U_le_Z a)).trans (Z_le_stabilizer R a)).trans (fixedCore_normalized a)
  intro x hx
  have hxU := hU hx
  have hxprod : x ∈ fixedCore R a ⊔ edgeDisplacement a t := by
    rw [sup_comm]
    exact hE hx
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hnorm] at hxprod
  obtain ⟨d, hd, e, he, hde⟩ := hxprod
  change d * e = x at hde
  have hdU : d ∈ U R a := by
    have hm := (U R a).mul_mem (hde ▸ hxU) ((U R a).inv_mem (hEU he))
    simpa only [mul_inv_cancel_right] using hm
  have hd1 : d = 1 := (EdgeTransfer.U_fixed_eq_bot modules a ha).le ⟨hdU, hd.2⟩
  rw [hd1, one_mul] at hde
  exact hde ▸ he

theorem native_intersection_commutator_card (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    Nat.card (⁅Vcirc R a ⊓ V R t, Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  have hE := Initial.edge_le_natural source a t ha hat
  let := finite_stabilizer R a
  let : Finite (edgeDisplacement a t) := Finite.of_injective
    (inclusion ((hE.trans (U_le_Z a)).trans (Z_le_stabilizer R a))) (inclusion_injective _)
  exact (card_le_of_le
    (native_intersection_commutator_le_edge source hb modules initial facts p bad ha hat)).trans
      (Initial.edge_card_le_four source hb modules a t ha hat)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed
