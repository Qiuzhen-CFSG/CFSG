module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Symmetry.SmallAction
/-!
# The normal commutator in the asymmetric case

The joined moving groups lie in the common kernel intersection by b ≥ 6.
Their commutator with that intersection is normal at the first vertex and
lies in the product HₐH_d. The first factor is residual-fixed; the second
lies in the natural Uₐ and has order at most four. The small-action lemma
and the absence of residual-fixed vectors in Uₐ remove that second factor.
Disjointness of the two H groups then gives [Vcirc_d,Qₐ ∩ Q_d] = 1.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(ii), printed p.888.
Normality of the intersection is used only at a.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

omit [Finite M] in
private theorem H_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (H R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Vcirc R a, Q R a⁆ : Subgroup (FreeAmalgam R)).map _ = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized a hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  rfl

/-- The normal commutator has no component in the opposite natural subgroup. -/
theorem asymmetric_commutator_le_H (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (products : ProductFacts geometry) {d : Vertex R}
    (hm : p.a ∈ movingNeighbors geometry d) (hn : d ∉ movingNeighbors geometry p.a) :
    ⁅Vcirc R p.a ⊔ Vcirc R d, Q R p.a ⊓ Q R d⁆ ≤ H R p.a := by
  have hd : (cosetGraph R).dist p.a d = 2 := by rw [SimpleGraph.dist_comm]; exact hm.1
  have hdc : color R d = false :=
    (color_eq_of_dist_even R d p.a (hm.1.symm ▸ (by decide : Even 2))).trans p.color_a
  let K := ⁅Vcirc R p.a ⊔ Vcirc R d, Q R p.a ⊓ Q R d⁆
  let I := Q R p.a ⊓ Q R d
  have hHnorm := H_normalized (R := R) p.a
  have hDnorm := H_normalized (R := R) d
  have hInorm : I ≤ normalizer (H R p.a ⊔ H R d : Subgroup (FreeAmalgam R)) :=
    (le_inf ((inf_le_left.trans (show Q R p.a ≤ stabilizer R p.a from fun _ hx => hx.1)).trans hHnorm)
      ((inf_le_right.trans (show Q R d ≤ stabilizer R d from fun _ hx => hx.1)).trans hDnorm)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hAV : Vcirc R p.a ≤ V R p.a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer p.a).trans (V_normalized p.a))
  have hDV : Vcirc R d ≤ V R d := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer d).trans (V_normalized d))
  have hAI : Vcirc R p.a ≤ I := le_inf (hAV.trans (geometry.V_le_Q hb p.a p.color_a))
    (hAV.trans (V_le_Q_of_dist_add_two_lt p.color_a (by rw [hd]; have := initial.six_le; omega)))
  have hDI : Vcirc R d ≤ I := le_inf
    (hDV.trans (V_le_Q_of_dist_add_two_lt hdc (by rw [hm.1]; have := initial.six_le; omega)))
    (hDV.trans (geometry.V_le_Q hb d hdc))
  have hbound : K ≤ H R p.a ⊔ H R d := by
    have ha : Vcirc R p.a ≤ commutatorPreimage I I (H R p.a ⊔ H R d) :=
      le_commutatorPreimage hAI ((commutator_mono le_rfl inf_le_left).trans le_sup_left)
    have hd' : Vcirc R d ≤ commutatorPreimage I I (H R p.a ⊔ H R d) :=
      le_commutatorPreimage hDI ((commutator_mono le_rfl inf_le_right).trans le_sup_right)
    exact (commutator_mono (sup_le ha hd') le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hInorm)
  have hHG : H R p.a ≤ stabilizer R p.a :=
    (H_le_fixedCore p (by omega) control p.a p.color_a).trans
      (inf_le_left.trans (fun _ hx => hx.1))
  have hDU := reverse_H_le_U p hb modules control p.color_a hm
  have hUG : U R p.a ≤ stabilizer R p.a := (U_le_Z p.a).trans (Z_le_stabilizer R p.a)
  have hDG := hDU.trans hUG
  have hKG := hbound.trans (sup_le hHG hDG)
  let S := stabilizer R p.a
  let := finite_stabilizer R p.a
  let K₀ := K.subgroupOf S
  let H₀ := (H R p.a).subgroupOf S
  let U₀ := (U R p.a).subgroupOf S
  let D₀ := (H R d).subgroupOf S
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer
    (asymmetric_commutator_normalized source p hb products p.color_a hd hm hn)
  let : H₀.Normal := normal_subgroupOf_of_le_normalizer hHnorm
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (U_normalized p.a)
  let π := initial.natural_section.projection
  have hp : IsPGroup 2 π.ker := by
    rw [initial.natural_section.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le p.a p.color_a).comap_subtype
  have hHC : H₀ ≤ centralizer (pResidual 2 S : Set S) := by
    intro h hh l hl
    exact Subtype.ext ((H_le_fixedCore p (by omega) control p.a p.color_a hh).2 l
      (mem_map_of_mem S.subtype hl))
  have hUC : U₀ ⊓ centralizer (pResidual 2 S : Set S) = ⊥ := by
    apply le_bot_iff.mp
    rintro u ⟨hu, hc⟩
    apply Subtype.ext
    apply (EdgeTransfer.U_fixed_eq_bot modules p.a p.color_a).le
    refine ⟨hu, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact congrArg Subtype.val (hc l hl)
  have hDcard : Nat.card D₀ ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDG).toEquiv]
    obtain ⟨t, hdt, hat⟩ := exists_common_neighbor_of_dist_two R d p.a hm.1
    rw [(moving_edge_eq_at p (by omega) control d t p.a hdc hdt hat hm).2]
    exact EdgeTransfer.edge_displacement_card_le_four hb modules p.a t p.color_a hat
  have hK₀ : K₀ ≤ H₀ ⊔ D₀ := by
    dsimp only [H₀, D₀]
    rw [← subgroupOf_sup hHG hDG]
    exact fun _ hx => hbound hx
  have hresult := Symmetry.le_fixed_factor_of_normal π
    initial.natural_section.module_section.projection_surjective hp K₀ H₀ U₀ D₀
    hHC hUC (fun _ hx => hDU hx) hDcard hK₀
  intro x hx
  exact hresult (show (⟨x, hKG hx⟩ : S) ∈ K₀ from hx)

/-- Disjointness of the two H factors kills the opposite commutator. -/
theorem asymmetric_intersection_centralizes (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (products : ProductFacts geometry) {d : Vertex R}
    (hm : p.a ∈ movingNeighbors geometry d) (hn : d ∉ movingNeighbors geometry p.a) :
    ⁅Vcirc R d, Q R p.a ⊓ Q R d⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← disjoint_iff.mp (reverse_H_disjoint p hb modules control p.color_a hm)]
  exact le_inf ((commutator_mono le_sup_right le_rfl).trans
    (asymmetric_commutator_le_H source p hb modules initial control products hm hn))
    (commutator_mono le_rfl inf_le_right)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
