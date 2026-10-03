module
public import Stellmacher.SectionFiveToSeven.SixThreeNativeQuotients
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionEight.NoncentralSylowCenterAction
public import Stellmacher.SectionTwo.NestedSL2OutsideGeneration

/-!
# A generating backward neighbor in Stellmacher (8.2)

In the noncentral first-step case of the fixed Section Eight local context,
there is a neighbor m of the initial critical vertex a such that the
intersection of their stabilizers generates G_a together with Z_a'.
The chosen neighbor is an actual vertex of the original coset graph.

The native (6.3) companion supplies the nested SL2 quotient of G_a.
Reversed criticality makes Z_a' a two-subgroup of G_a outside its core.
The outside-generation theorem gives a Sylow subgroup T generating with
Z_a'. Conjugate the supplied edge Sylow to T inside G_a; the corresponding
inverse graph action sends firstStep to m and fixes a. Stabilizer and
adjacency covariance place T in the new edge intersection, so its native
generation equality maps to the required ambient join.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), p.37, the choice
of a-1 in Delta(a), refs/latex/stellmacher-n-group.tex. No containment of
Z_m in the opposite endpoint stabilizer or new critical-pair property is
assumed; those form the subsequent case split.
The legacy ambient-Sylow signature is retained through `toLocalContext`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_exists_backward_neighbor_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∃ m : ctx.Γ.Vertex, m ∈ neighborhood ctx.Γ ctx.criticalPath.a ∧
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
        ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let A := (z Γ cp.a').subgroupOf P
  have h7 := ctx.sectionSeven
  have h74 := lemma_seven_four h7 Γ cp
  have hloc := (SevenSix.edge_local_data h7 Γ cp).1
  have hZP : z Γ cp.a' ≤ P := h74.reverse_containment.1
  have hZne : ¬ z Γ cp.a' ≤ q Γ cp.a := (h74.commutator_case ctx.commutator_ne).2.2
  have hQne : pCore 2 P ≠ ⊥ := by
    intro hb
    apply hloc.1.1.2.2.1
    change twoCoreIn P = ⊥
    simp [twoCoreIn, hb]
  have hlen := cp.length_pos
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hlast : last ∈ neighborhood Γ cp.a' := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    have ha := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by apply Fin.ext; simp; omega
    rw [hi, cp.path_end] at ha
    exact Γ.adjacent_symm ha
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ hlast
  have hAp : IsPGroup 2 A :=
    (IsElementaryAbelian.isPGroup 2 (z Γ cp.a')).comap_of_injective P.subtype P.subtype_injective
  have hout : ¬ A ≤ pCore 2 P := by
    intro hAQ
    apply hZne
    have hm := Subgroup.map_mono (f := P.subtype) hAQ
    rw [Subgroup.map_subgroupOf_eq_of_le hZP] at hm
    change z Γ cp.a' ≤ Γ.twoCoreAt cp.a
    rw [Γ.twoCoreAt_def]
    exact hm
  obtain ⟨_hcomm1, hcomm2⟩ := eight_two_noncentral_sylow_center_action_local ctx hcenter
  obtain ⟨hA1, hA2⟩ := ctx.sixThree.nativeSL2 hcomm2
  have hPn : IsSL2Two ((P ⧸ pCore 2 P) ⧸ frattini (P ⧸ pCore 2 P)) := by
    rcases cp.edge_stabilizers_are_P with he | he
    · change IsSL2Two ((stabilizer Γ cp.a ⧸ pCore 2 (stabilizer Γ cp.a)) ⧸
        frattini (stabilizer Γ cp.a ⧸ pCore 2 (stabilizer Γ cp.a)))
      rw [he.1]
      exact hA1
    · change IsSL2Two ((stabilizer Γ cp.a ⧸ pCore 2 (stabilizer Γ cp.a)) ⧸
        frattini (stabilizer Γ cp.a ⧸ pCore 2 (stabilizer Γ cp.a)))
      rw [he.1]
      exact hA2
  obtain ⟨T, hgen⟩ := SectionTwo.exists_sylow_sup_eq_top_of_outside_nestedSL2Two
    hloc.2 hQne A hAp hout hPn
  obtain ⟨_hSP, R, hR⟩ := hloc.1.1.2.1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P R T
  let m := Γ.act ((g : G)⁻¹) cp.firstStep
  have hfix : Γ.act ((g : G)⁻¹) cp.a = cp.a := by
    have hmem : (g : G)⁻¹ ∈ stabilizer Γ cp.a := P.inv_mem g.property
    have hd := Γ.stabilizer_def cp.a
    exact Set.ext_iff.mp hd _ |>.mp hmem
  have hm : m ∈ neighborhood Γ cp.a := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    have ha := adjacent_act Γ ((g : G)⁻¹) cp.firstStep_adj
    rwa [hfix] at ha
  have hTm : (T : Subgroup P).map P.subtype ≤ stabilizer Γ m := by
    rw [show m = Γ.act ((g : G)⁻¹) cp.firstStep from rfl, stabilizer_act,
      inv_inv, conjugateBy]
    have hgmap : (T : Subgroup P).map P.subtype = S.map (MulAut.conj (g : G)).toMonoidHom := by
      rw [← hg]
      change ((R : Subgroup P).map (MulAut.conj g).toMonoidHom).map P.subtype = _
      calc
        _ = ((R : Subgroup P).map P.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map]
          rfl
        _ = _ := congrArg (Subgroup.map (MulAut.conj (g : G)).toMonoidHom) hR
    rw [hgmap]
    exact Subgroup.map_mono (cp.S_le_edge_stabilizers.trans inf_le_right)
  have hgenm : z Γ cp.a' ⊔ (T : Subgroup P).map P.subtype = P := by
    have hmap := congrArg (Subgroup.map P.subtype) hgen
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZP,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap
  refine ⟨m, hm, le_antisymm (sup_le inf_le_left hZP) ?_⟩
  change P ≤ (P ⊓ stabilizer Γ m) ⊔ z Γ cp.a'
  conv_lhs => rw [← hgenm]
  exact sup_le le_sup_right
    ((le_inf (Subgroup.map_subtype_le _) hTm).trans le_sup_left)

public theorem eight_two_exists_backward_neighbor
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∃ m : ctx.Γ.Vertex, m ∈ neighborhood ctx.Γ ctx.criticalPath.a ∧
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
        ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a :=
  eight_two_exists_backward_neighbor_local ctx.toLocalContext hcenter

end Stellmacher.SectionEight
