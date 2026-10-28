module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Linear

/-!
# Faithfulness of the actual radius-head action

The radius-one span at a neighboring holomorph vertex contains Z_a and lies
in V_a. If [V_a,Ltilde_a] lay in Z_a, both adjacent stabilizers would normalize
that span. The source characteristic condition would make it trivial,
contradicting the natural subgroup of order eight in Z_a.

The triple bound puts [Z_a[V_a,Q_a],Ltilde_a] in Z_a. Idempotence of the
two-residual commutator therefore excludes [V_a,G_a] ≤ Z_a[V_a,Q_a]. The
literal quotient-conjugation formula and simplicity of the specified SL₃(2)
carrier now prove faithfulness of its action on V_a/(Z_a[V_a,Q_a]).

This argument needs no order-four assumption once the triple bound is supplied.
The final wrapper retains the inputs of the initial contrary configuration.
It neither assumes nor constructs the subsequent natural-module splitting.

Source: Meierfrankenfeld--Stellmacher (1993), (2.1)(iii), p.855, the notation
c(U), p.881, and the nontrivial action in (4.3.1)(iii), pp.882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
private theorem ball_normalized (t : Vertex R) (n : ℕ) :
    stabilizer R t ≤ normalizer (VBall R t n : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (VBall R t n).map (MulAut.conj g).toMonoidHom = VBall R t n
  have h := VBall_act R g⁻¹ t n
  have hgt : act R g⁻¹ t = t := (stabilizer R t).inv_mem hg
  simpa only [hgt, inv_inv] using h.symm

private theorem radius_moving_not_le_Z_at_edge (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    ¬ Vcirc R a ≤ Z R a := by
  intro hfixed
  let N := VBall R t 1
  have hatd : (cosetGraph R).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have hZN : Z R a ≤ N := le_iSup_of_le a (le_iSup_of_le hatd.le le_rfl)
  have hNV : N ≤ V R a := by
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    apply le_iSup_of_le d
    apply le_iSup_of_le (show (cosetGraph R).dist d a ≤ 2 from ?_)
    · exact le_rfl
    · have hh := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := a)
      rw [SimpleGraph.dist_comm (u := t), hatd] at hh
      omega
  have hNQ := hNV.trans (geometry.V_le_Q hb a ha)
  have hNS : N ≤ stabilizer R a ⊓ stabilizer R t :=
    le_inf (hNQ.trans (fun _ hx => hx.1)) (hNQ.trans (fun _ hx => hx.2 t hat))
  have hNt : stabilizer R t ≤ normalizer (N : Set (FreeAmalgam R)) :=
    ball_normalized t 1
  have hNa : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    rw [← source.local_generation a ha]
    refine sup_le ?_ ((show Q R a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans hNt)
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hNV le_rfl).trans (hfixed.trans hZN)
  have hbot := no_common_normal_at_edge R source.characteristic a t ha hat N hNS
    (normal_subgroupOf_of_le_normalizer hNa) (normal_subgroupOf_of_le_normalizer hNt)
  have hU : U R a = ⊥ := le_bot_iff.mp ((U_le_Z a).trans (hZN.trans hbot.le))
  have hcard := modules.natural.card_at a ha
  rw [hU, card_bot] at hcard
  omega

/-- The actual radius quotient has nontrivial residual action. The proof uses
the source common-normal-subgroup obstruction at an adjacent edge. -/
theorem radius_moving_not_le_Z (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) : ¬ Vcirc R a ≤ Z R a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  exact radius_moving_not_le_Z_at_edge source geometry hb modules
    (mVertex R g) (hVertex R g) rfl
    ((adjacent_iff_exists_common R _ _).mpr ⟨g, Or.inl ⟨rfl, rfl⟩⟩)

private theorem local_moving_not_le_Z (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    ¬ ⁅localRadius a, pResidual 2 (stabilizer R a)⁆ ≤ localZ a := by
  intro h
  apply radius_moving_not_le_Z source geometry hb modules a ha
  have hh := map_mono (f := (stabilizer R a).subtype) h
  rwa [map_commutator,
    map_subgroupOf_eq_of_le ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at hh

private theorem local_commutator_le_radical_of_head_trivial (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (htriv : (radiusHeadAction source geometry a ha).ker = ⊤) :
    ⁅localRadius a, (⊤ : Subgroup (stabilizer R a))⁆ ≤ localRadical a := by
  let := localRadical_normal geometry a
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g _ v hv
  have hg : radiusHeadAction source geometry a ha (localProjection source a ha g) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [htriv]
    trivial
  have he := radiusHeadAction_apply source geometry a ha g ⟨v, hv⟩
  rw [hg] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he.symm
  change g * v * g⁻¹ / v ∈ localRadical a at hh
  simpa only [commutatorElement_def, div_eq_mul_inv] using hh

private theorem local_radical_commutator_le_Z (geometry : Geometry R)
    (hb : 2 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (htriple : ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a) :
    ⁅localRadical a, pResidual 2 (stabilizer R a)⁆ ≤ localZ a := by
  let := geometry.Z_normal a
  have hD : localRadical a ≤
      commutatorPreimage ⊤ (pResidual 2 (stabilizer R a)) (localZ a) :=
    sup_le (le_commutatorPreimage le_top (commutator_le_left _ _))
      (le_commutatorPreimage le_top (local_triple geometry hb a ha htriple))
  exact (commutator_mono hD le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

/-- The full local commutator survives in the radius head. All commutators
and quotients here are inside the finite vertex stabilizer. -/
theorem local_radius_commutator_not_le_radical (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (a : Vertex R) (ha : color R a = false)
    (htriple : ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a) :
    ¬ ⁅localRadius a, (⊤ : Subgroup (stabilizer R a))⁆ ≤ localRadical a := by
  intro h
  apply local_moving_not_le_Z source geometry hb modules a ha
  let := finite_stabilizer R a
  have hperfect := commutator_isPPerfect_idempotent
    (pResidual 2 (stabilizer R a)) (localRadius a) (isPPerfect_pResidual 2)
    (source.V_isPGroup geometry hb a ha).comap_subtype le_normalizer_of_normal
  rw [← hperfect]
  exact (commutator_mono ((commutator_mono le_rfl le_top).trans h) le_rfl).trans
    (local_radical_commutator_le_Z geometry hb a ha htriple)

/-- Simplicity turns geometric nontriviality into faithfulness of the
specified quotient-conjugation action, without representation recognition. -/
theorem radiusHeadAction_injective_of_triple (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (a : Vertex R) (ha : color R a = false)
    (htriple : ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a) :
    Function.Injective (radiusHeadAction source geometry a ha) := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  apply (radiusHeadAction source geometry a ha).ker_eq_bot_iff.mp
  rcases (MonoidHom.normal_ker (radiusHeadAction source geometry a ha)).eq_bot_or_eq_top with hk | hk
  · exact hk
  · exact False.elim ((local_radius_commutator_not_le_radical source geometry hb modules a ha htriple)
      (local_commutator_le_radical_of_head_trivial source geometry a ha hk))

/-- Faithfulness with the exact inputs of the initial contrary configuration.
The stronger preceding theorem shows that the order-four input is unnecessary
for this step once the triple-commutator bound has been supplied. -/
theorem radiusHeadAction_injective (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (_hfour : Nat.card (radiusCommutator p.a p.a') = 4)
    (htriple : ⁅⁅V R p.a, Q R p.a⁆, Ltilde R p.a⁆ ≤ Z R p.a) :
    Function.Injective (radiusHeadAction source geometry p.a p.color_a) :=
  radiusHeadAction_injective_of_triple source geometry hb modules p.a p.color_a htriple

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
