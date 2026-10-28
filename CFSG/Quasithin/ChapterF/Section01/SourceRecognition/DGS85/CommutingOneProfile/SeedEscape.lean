module
public import Theory.GroupTheory.QuadraticCoreActor
public import Theory.GroupAction.ThreePointKernelSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphSeeds

/-!
# Escape and movement of the opposite Chapter 11 seed

If Zα ∩ Qβ lies in Qγ, both Zα and Zγ centralize [Qβ,Zα].
The normal closure argument for quadratic actors forces <Zα,Zγ> to be
a two-group, proving the algebraic step in (11.2)(c). The non-two-group
premise is retained for arbitrary local rank-one actions.

When the beta vertex is cubic, this premise is proved directly. A critical
center fixes exactly its own neighbor: an element fixing two of three
neighbors fixes the whole star. A two-group would have a common fixed
neighbor, contradicting the two different center fixed points. This gives
unconditional seed escape and nonzero movement in that local degree-three
branch, without identifying the full kernel Uβ with Qβ.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.2)(c), printed p.168. The remaining rank-one, seed-size and generation
arguments for (11.3)--(11.8) are separate obligations.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem adjacent_center_le (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    Z (family P) a ≤ stabilizer (family P) b :=
  ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
    ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right))

/-- Centralizing the first seed forces the pair of neighboring centers to generate a two-group. -/
theorem source_pair_isPGroup_of_seed_centralized (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hc : Z (family P) c ≤ centralizer (Z (family P) a ⊓ Q (family P) b : Set G)) :
    IsPGroup 2 (Z (family P) a ⊔ Z (family P) c : Subgroup G) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let M := stabilizer (family P) b
  let A := (Z (family P) a).subgroupOf M
  let C := (Z (family P) c).subgroupOf M
  let E := (Z (family P) a ⊓ Q (family P) b).subgroupOf M
  have haM := adjacent_center_le h hab
  have hcM := adjacent_center_le h hbc.symm
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hcM
  have hcomm : ⁅pCore 2 M,A⁆ ≤ E := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le haM,
      map_subgroupOf_eq_of_le (inf_le_right.trans (Q_le_stabilizer _ b))]
    change ⁅Q (family P) b,Z (family P) a⁆ ≤ Z (family P) a ⊓ Q (family P) b
    apply le_inf (le_normalizer_iff_commutator_le_right.mp
      (source_adjacent_core_normalizes_center h hab))
    have hn : stabilizer (family P) b ≤ normalizer (Q (family P) b : Set G) := by
      simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
        using (pCore 2 M).le_normalizer_map M.subtype
    exact le_normalizer_iff_commutator_le_left.mp (haM.trans hn)
  have hAE : A ≤ centralizer (E : Set M) := by
    intro x hx y hy
    apply Subtype.ext
    exact (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative (Z (family P) a))) hx y.val hy.1
  have hCE : C ≤ centralizer (E : Set M) := by
    intro x hx y hy
    exact Subtype.ext (hc hx y.val hy)
  have hp := isPGroup_sup_of_centralized_displacement (pCore 2 M) A C E
    (pCore_isPGroup (p := 2)) (IsElementaryAbelian.isPGroup 2 C)
    le_normalizer_of_normal le_normalizer_of_normal
    (inf_le_right.trans (source_vertex_core_selfCentralizing h b)) hcomm hAE hCE
  rw [←subgroupOf_sup haM hcM] at hp
  exact hp.of_equiv (subgroupOfEquivOfLe (sup_le haM hcM))

/-- The algebraic contradiction in source (11.2)(c), on the actual graph. -/
theorem source_seed_not_le_opposite_core (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hnot : ¬ IsPGroup 2 (Z (family P) a ⊔ Z (family P) c : Subgroup G)) :
    ¬ Z (family P) a ⊓ Q (family P) b ≤ Q (family P) c := by
  intro hle
  apply hnot (source_pair_isPGroup_of_seed_centralized h hab hbc ?_)
  exact le_centralizer_iff.mp (hle.trans (source_core_centralizes_center h c))

/-- The same argument proves actual movement of the seed by the opposite center. -/
theorem source_seed_commutator_ne_bot (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hnot : ¬ IsPGroup 2 (Z (family P) a ⊔ Z (family P) c : Subgroup G)) :
    ⁅Z (family P) a ⊓ Q (family P) b,Z (family P) c⁆ ≠ ⊥ := by
  intro he
  apply hnot (source_pair_isPGroup_of_seed_centralized h hab hbc ?_)
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)

private theorem cubic_center_unique_fixed_neighbor (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (he : ¬ Z (family P) a ≤ U (family P) b)
    (hfix : ∀ g ∈ Z (family P) a, g • c = c) : c = a := by
  by_contra hn
  apply he
  intro g hg
  have ha : g • a = a := Z_le_stabilizer _ a hg
  have hb : g • b = b := adjacent_center_le h hab hg
  have hgc := hfix g hg
  have hall : ∀ z ∈ (graph (family P)).neighborSet b, g • z = z :=
    MulAction.fixes_three_point_set _ hcard g (fun z => by
      change (graph (family P)).Adj b z ↔ (graph (family P)).Adj b (g • z)
      simpa only [Subgroup.CosetGeometry.translationGraphIso_apply,hb] using
        ((Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff
          (v := b) (w := z)).symm) hab.symm hbc (Ne.symm hn) ha hgc
  intro z hz
  rcases (mem_ball_one (family P) b z).mp hz with hz | rfl
  · exact hall z hz
  · exact hb

/-- At a cubic beta vertex, two distinct neighboring critical centers
cannot generate a two-group. No rank-one recognition premise is needed. -/
theorem source_cubic_centers_not_isPGroup (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    ¬ IsPGroup 2 (Z (family P) a ⊔ Z (family P) c : Subgroup G) := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  have haM := adjacent_center_le h hab
  have hcM := adjacent_center_le h hbc.symm
  have hce : ¬ Z (family P) c ≤ U (family P) b := by
    obtain ⟨g,hg,hz,_,_⟩ := source_neighbor_conjugate h hab hbc
    intro hh
    apply hc.2
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
    rw [←hz,map_map,←U_translate] at hm
    have hZa : ((Z (family P) a).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = Z (family P) a := by
      rw [←Z_translate,←Z_translate,inv_smul_smul]
    rw [←map_map,hZa,show g⁻¹ • b = b from (stabilizer (family P) b).inv_mem hg] at hm
    exact hm
  intro hp
  let L := Z (family P) a ⊔ Z (family P) c
  have hLM : L ≤ stabilizer (family P) b := sup_le haM hcM
  let f : L →* Equiv.Perm ((graph (family P)).neighborSet b) :=
    (Theory.GroupTheory.AmalgamGraph.localAction (family P) b).comp (inclusion hLM)
  let : MulAction L ((graph (family P)).neighborSet b) := MulAction.compHom _ f
  obtain ⟨w,hw⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card
    ((graph (family P)).neighborSet b) (by rw [hcard]; decide)
  have hfix (g : G) (hg : g ∈ L) : g • w.val = w.val := by
    have he := hw (⟨g,hg⟩ : L)
    exact congrArg Subtype.val he
  have hwa := cubic_center_unique_fixed_neighbor h hab w.property hcard hc.2
    (fun g hg => hfix g (mem_sup_left hg))
  have hwc := cubic_center_unique_fixed_neighbor h hbc.symm w.property hcard hce
    (fun g hg => hfix g (mem_sup_right hg))
  exact hac (hwa.symm.trans hwc)

/-- Source (11.2)(c) on the cubic beta branch, with the two-center
non-two-group premise discharged on the original graph. -/
theorem source_cubic_seed_escape (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    ¬ Z (family P) a ⊓ Q (family P) b ≤ Q (family P) c :=
  source_seed_not_le_opposite_core h (source_critical_one_adjacent hc hb) hbc
    (source_cubic_centers_not_isPGroup h hc hb hbc hac hcard)

/-- Nonzero seed movement on the same cubic branch. -/
theorem source_cubic_seed_moved (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    ⁅Z (family P) a ⊓ Q (family P) b,Z (family P) c⁆ ≠ ⊥ :=
  source_seed_commutator_ne_bot h (source_critical_one_adjacent hc hb) hbc
    (source_cubic_centers_not_isPGroup h hc hb hbc hac hcard)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
