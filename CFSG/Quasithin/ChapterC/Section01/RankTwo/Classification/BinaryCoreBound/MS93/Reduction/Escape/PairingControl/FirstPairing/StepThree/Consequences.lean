module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic

/-!
# Deductions from the rank-one identification in MS93 (4.3.2)(3)

A subgroup of the literal fixed preimage B has its Q-commutator normalized
by the entire vertex stabilizer. Irreducibility of U then excludes a nonzero
normal subgroup inside an edge displacement of order four.

The contrary configuration has a moving neighbor: otherwise V is contained
in B, Vcirc is contained in Z, and H is trivial, contradicting step (1).
Once the rank-one argument identifies [Z_delta,Q_alpha] with the alpha-side
edge displacement, conjugate generation therefore gives H = U, without
first assuming coordinates on Vcirc/U.

Edge equality also gives moving symmetry. If Z_alpha were contained in
B_delta, its Q_delta-commutator would be a normal subgroup of U_delta of
order at most four, hence trivial. Faithfulness on U_alpha and equality of
the local two-core orders then give Q_delta = Q_alpha. This contradicts
the order-four moving commutator supplied by the transported InitialFacts.

These are conditional deductions from the rank-one identification, not a
proof of that identification. Only the orientation on V/Z is used here;
OppositeSectionAt and later source conclusions are not premises.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(3), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

theorem fixed_subgroup_commutator_normalized (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {W : Subgroup (FreeAmalgam R)} (hW : W ≤ B R a (geometry.Z_normal a)) :
    stabilizer R a ≤ normalizer ((⁅W, Q R a⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hV := (geometry.V_le_Q hb a ha).trans (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)
  have hWQ : W ≤ Q R a := (hW.trans (EdgeTransfer.B_le_radius hb a ha)).trans
    (geometry.V_le_Q hb a ha)
  have hreduce := commutator_eq_of_centralizing_sup
    (B := Z R a ⊔ W) rfl
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))
    (hWQ.trans (Q R a).le_normalizer)
  rw [← source.local_generation a ha]
  refine sup_le ?_ (normalizer_commutator_ge_right _ _)
  apply le_normalizer_iff.mpr
  intro l hl x hx
  have hWmap : W.map (MulAut.conj l).toMonoidHom ≤ Z R a ⊔ W := by
    rintro y ⟨w, hw, rfl⟩
    have hfixed := ((mem_B_iff R a _ hV w).mp (hW hw)).2 l hl
    have hh := (Z R a ⊔ W).mul_mem (mem_sup_left hfixed) (mem_sup_right hw)
    change l * w * l⁻¹ ∈ Z R a ⊔ W
    simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  have hQmap : (Q R a).map (MulAut.conj l).toMonoidHom = Q R a :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized R a) (Ltilde_le_stabilizer a hl))
  have hh := mem_map_of_mem (MulAut.conj l).toMonoidHom hx
  rw [map_commutator, hQmap] at hh
  have hh' := commutator_mono hWmap (le_refl (Q R a)) hh
  rw [commutator_comm (Z R a ⊔ W), ← hreduce, commutator_comm] at hh'
  exact hh'

omit [Finite M] in
theorem normal_in_U_eq_bot_or_eq {a : Vertex R} (o : MovingOrientationAt a)
    (K : Subgroup (FreeAmalgam R)) (hKU : K ≤ U R a)
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R))) :
    K = ⊥ ∨ K = U R a := by
  have hUG := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hKG := hKU.trans hUG
  let : (K.subgroupOf (stabilizer R a)).Normal := normal_subgroupOf_of_le_normalizer hn
  have him : (⊤ : Subgroup (stabilizer R a)).map o.projection = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr o.natural_section.projection_surjective
  rcases o.naturalU.irreducible him (K.subgroupOf (stabilizer R a))
    (fun _ hx => hKU hx) le_normalizer_of_normal with h | h
  · left
    have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
    simpa only [map_subgroupOf_eq_of_le hKG, Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
    simpa only [map_subgroupOf_eq_of_le hKG, map_subgroupOf_eq_of_le hUG] using hh

omit [Finite M] in
theorem H_eq_U_of_le (transfer : NormalizationTransfer R)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (o : MovingOrientationAt p.a) (hle : H R p.a ≤ U R p.a) : H R p.a = U R p.a := by
  rcases normal_in_U_eq_bot_or_eq o (H R p.a) hle (H_normalized p.a) with h | h
  · exact (H_not_le_fixed transfer bad (h ▸ bot_le)).elim
  · exact h

theorem exists_moving_neighbor (hb : 2 < geometry.b R)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ d, d ∈ movingNeighbors geometry p.a := by
  by_contra! h
  have hVB : V R p.a ≤ B R p.a (geometry.Z_normal p.a) := by
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    have hd' : (cosetGraph R).dist p.a d ≤ 2 := by rwa [SimpleGraph.dist_comm]
    by_cases htwo : (cosetGraph R).dist p.a d = 2
    · exact Classical.not_not.mp (fun hnot => h d ⟨htwo, hnot⟩)
    · have hz : (cosetGraph R).dist p.a d = 0 ∨ (cosetGraph R).dist p.a d = 1 := by omega
      rcases hz with hz | hone
      · have he := (cosetGraph_connected R).dist_eq_zero_iff.mp hz
        subst d
        exact EdgeTransfer.Z_le_B hb p.a p.color_a
      · have hadj : Adjacent R p.a d :=
          (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hone)
        exact (EdgeTransfer.edge_Z_le p.a d p.color_a hadj).trans
          (EdgeTransfer.Z_le_B hb p.a p.color_a)
  have hV := (geometry.V_le_Q hb p.a p.color_a).trans
    (show Q R p.a ≤ stabilizer R p.a from fun _ hx => hx.1)
  have hCZ : Vcirc R p.a ≤ Z R p.a := by
    rw [Vcirc, commutator_comm]
    apply commutator_le.mpr
    intro l hl v hv
    exact ((mem_B_iff R p.a _ hV v).mp (hVB hv)).2 l hl
  have hH : H R p.a ≤ ⊥ := by
    exact (commutator_mono hCZ le_rfl).trans (geometry.centralizes p.a p.color_a).le
  exact H_not_le_fixed transfer bad (hH.trans bot_le)

theorem H_eq_U_of_alpha_commutators (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (initial : InitialFacts p) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (o : MovingOrientationAt p.a)
    (identify : ∀ t d, Adjacent R p.a t → Adjacent R d t →
      d ∈ movingNeighbors geometry p.a → ⁅Z R d, Q R p.a⁆ = edgeDisplacement p.a t) :
    H R p.a = U R p.a := by
  obtain ⟨d, hd⟩ := exists_moving_neighbor hb transfer p bad
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R p.a d hd.1
  apply H_eq_U_of_le transfer p bad o
  apply (H_le_conjugates_commutator hb initial hd).trans
  rw [identify t d hat hdt hd]
  calc
    NormalizerTransfer.conjugatesIn (edgeDisplacement p.a t) (stabilizer R p.a) ≤
        NormalizerTransfer.conjugatesIn (U R p.a) (stabilizer R p.a) :=
      iSup_mono fun _ => map_mono
        (EdgeTransfer.edge_commutator_le_natural hb modules p.a t p.color_a hat)
    _ = U R p.a := conjugatesIn_eq_of_normalized _ _ (U_normalized p.a)

theorem moving_symmetric_of_edge_eq (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t d : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a)
    (o : MovingOrientationAt d) (he : edgeDisplacement a t = edgeDisplacement d t) :
    a ∈ movingNeighbors geometry d := by
  have hdc := moving_color ha hd
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases hh : color R t <;> simp_all
  refine ⟨by rw [SimpleGraph.dist_comm, hd.1], ?_⟩
  intro hB
  let K := ⁅Z R a, Q R d⁆
  have hKedge : K ≤ edgeDisplacement d t := by
    rw [← he]
    exact commutator_mono le_rfl (Q_le_adjacent_h R ht hdt)
  have hKU := hKedge.trans (EdgeTransfer.edge_commutator_le_natural hb modules d t hdc hdt)
  have hzero : K = ⊥ := by
    rcases normal_in_U_eq_bot_or_eq o K hKU
      (fixed_subgroup_commutator_normalized source hb hdc hB) with h | h
    · exact h
    · have hUedge : U R d ≤ edgeDisplacement d t := h ▸ hKedge
      let := finite_stabilizer R d
      let : Finite (edgeDisplacement d t) := Finite.of_injective
        (inclusion ((EdgeTransfer.edge_commutator_le_natural hb modules d t hdc hdt).trans
          ((U_le_Z d).trans (Z_le_stabilizer R d)))) (inclusion_injective _)
      have hcard := Nat.card_le_card_of_injective (inclusion hUedge) (inclusion_injective _)
      rw [modules.natural.card_at d hdc, edge_card p (by omega) initial d t hdc hdt] at hcard
      omega
  have hQa : Q R d ≤ Q R a := by
    rw [← modules.natural.centralizer a ha]
    refine le_inf (Q_le_stabilizer_of_dist_two R d a hdc (by rw [SimpleGraph.dist_comm, hd.1])) ?_
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (centralizer_le (U_le_Z a))
  have hQeq : Q R d = Q R a := by
    let := finite_stabilizer R a
    let : Finite (Q R a) := Finite.of_injective
      (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)) (inclusion_injective _)
    exact eq_of_le_of_card_ge hQa (by rw [source.Q_card a ha, source.Q_card d hdc])
  have hcomm : ⁅Z R d, Q R a⁆ = ⊥ := by
    rw [← hQeq]
    exact geometry.centralizes d hdc
  have hc := moving_commutator_card_at p (by omega) initial bad a t d ha hat hdt hd
  rw [hcomm, card_bot] at hc
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
