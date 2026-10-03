module

public import Stellmacher.SectionEight.GeneratedContext

public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts

/-!
# Rank-one action on the distance-one cores

With the exact Section Eight context, noncentral first-step center,
critical distance one, and explicit elementary-core hypotheses at both
distinguished ends, each native core has fixed subgroup of index two
under a Sylow two-subgroup of its stabilizer.

The actual odd-dihedral core quotients give index two for both cores in
the common edge Sylow subgroup. Noncommutation of the critical centers
ensures neither core centralizes the other. Thus their join is the edge
Sylow subgroup. Since both cores are abelian, their intersection
centralizes this join and bounds each fixed-subgroup index by two.
Noncommutation excludes index one. Restriction to the stabilizer then
gives the native centralizer index for an actual Sylow subgroup.

This supplies the full-core action input for the central decomposition
in Stellmacher (8.2), final paragraph, Journal of Algebra 190 (1997),
p.38, `refs/latex/stellmacher-n-group.tex`. The argument works directly
on the distinguished edge, avoiding transfer from the source's backward
edge. It does not assume that a decomposition of the vertex center
already decomposes the whole core, nor assert the four-factor conclusion.

The supplemental theorem uses `SectionEightLocalContext` and its genuine
Section Seven hypotheses. The original public theorem remains a wrapper
through `SectionEightContext.toLocalContext`, preserving the graph and
critical path definitionally. No additional Sylow hypothesis is imposed
on the ambient group of the supplemental theorem.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem fourFactor_core_index_two
    {G : Type u} [Group G] [Finite G] (P W : Subgroup G)
    (hW : IsSylowTwoIn W P)
    (hD : ∃ n : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ n))) :
    (twoCoreIn P).relIndex W = 2 := by
  obtain ⟨n, ⟨equiv⟩⟩ := hD
  obtain ⟨_, T, hT⟩ := hW
  rw [← hT, twoCoreIn, Subgroup.relIndex_map_map_of_injective _ _ P.subtype_injective]
  let projection := QuotientGroup.mk' (pCore 2 P)
  have hker : projection.ker = pCore 2 P := QuotientGroup.ker_mk' _
  rw [← hker, Subgroup.relIndex_ker]
  let image := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 P))
  change Nat.card image = 2
  rw [Sylow.card_eq_multiplicity, Nat.card_congr equiv.toEquiv, DihedralGroup.nat_card]
  norm_num [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_three,
    Nat.prime_two]

private theorem fourFactor_join_of_index_two
    {G : Type u} [Group G] (Q R W : Subgroup G)
    (hQW : Q ≤ W) (hRW : R ≤ W) (hindex : R.relIndex W = 2)
    (hnot : ¬ Q ≤ R) : Q ⊔ R = W := by
  obtain ⟨element, hQ, hR⟩ := SetLike.not_le_iff_exists.mp hnot
  apply le_antisymm (sup_le hQW hRW)
  intro other hother
  by_cases hotherR : other ∈ R
  · exact (le_sup_right : R ≤ Q ⊔ R) hotherR
  · let elementW : W := ⟨element, hQW hQ⟩
    let otherW : W := ⟨other, hother⟩
    have hprod : otherW * elementW⁻¹ ∈ R.subgroupOf W :=
      ((R.subgroupOf W).mul_mem_iff_of_index_two hindex).mpr
        (by change other ∈ R ↔ element⁻¹ ∈ R; simp [hotherR, hR])
    have hmem : other * element⁻¹ ∈ Q ⊔ R := (le_sup_right : R ≤ Q ⊔ R) hprod
    simpa [mul_assoc] using (Q ⊔ R).mul_mem hmem ((le_sup_left : Q ≤ Q ⊔ R) hQ)

private theorem fourFactor_rank_one_of_abelian_pair
    {G : Type u} [Group G] [Finite G] (Q R W : Subgroup G)
    [IsMulCommutative Q] [IsMulCommutative R]
    (hQW : Q ≤ W) (hRW : R ≤ W) (hindex : R.relIndex W = 2)
    (hnot : ¬ Q ≤ Subgroup.centralizer (R : Set G)) :
    (Subgroup.centralizer (W : Set G)).relIndex Q = 2 := by
  have hnotle : ¬ Q ≤ R := fun hle => hnot (hle.trans (Subgroup.le_centralizer R))
  have hjoin := fourFactor_join_of_index_two Q R W hQW hRW hindex hnotle
  have hcentral : Q ⊓ R ≤ Subgroup.centralizer (W : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [← hjoin]
    apply sup_le
    · exact (Subgroup.le_centralizer Q).trans (Subgroup.centralizer_le inf_le_left)
    · exact (Subgroup.le_centralizer R).trans (Subgroup.centralizer_le inf_le_right)
  have hbound : (Q ⊓ R).relIndex Q ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact hindex ▸ Subgroup.relIndex_le_of_le_right hQW (by rw [hindex]; decide)
  have hbound' : (Subgroup.centralizer (W : Set G)).relIndex Q ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hcentral
      (Subgroup.index_ne_zero_of_finite (H := (Q ⊓ R).subgroupOf Q))).trans hbound
  have hneone : (Subgroup.centralizer (W : Set G)).relIndex Q ≠ 1 := by
    intro hone
    exact hnot ((Subgroup.relIndex_eq_one.mp hone).trans (Subgroup.centralizer_le hRW))
  have hpositive : 0 < (Subgroup.centralizer (W : Set G)).relIndex Q :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := (Subgroup.centralizer (W : Set G)).subgroupOf Q))
  omega

private theorem fourFactor_native_centralizer_index
    {G : Type u} [Group G] (P W : Subgroup G) (hWP : W ≤ P) :
    (Subgroup.centralizer (W.subgroupOf P : Set P)).relIndex (pCore 2 P) =
      (Subgroup.centralizer (W : Set G)).relIndex (twoCoreIn P) := by
  have hcentral : Subgroup.centralizer (W.subgroupOf P : Set P) =
      (Subgroup.centralizer (W : Set G)).subgroupOf P := by
    ext element
    constructor
    · intro he other hother
      exact congrArg Subtype.val (he ⟨other, hWP hother⟩ hother)
    · intro he other hother
      exact Subtype.ext (he other hother)
  have hcore : pCore 2 P = (twoCoreIn P).subgroupOf P := by
    exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
  rw [hcentral, hcore]
  exact Subgroup.relIndex_subgroupOf (Subgroup.map_subtype_le _)

public theorem eight_two_distance_one_core_action_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1)
    (helementary : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d))) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ T : Sylow 2 (GAt ctx.Γ d),
          (Subgroup.centralizer (T : Set (GAt ctx.Γ d))).relIndex
            (pCore 2 (GAt ctx.Γ d)) = 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have h7 := ctx.sectionSeven
  have h73 := lemma_seven_three h7 Γ
  have hfirst : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by have := cp.length_pos; omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hlength.symm
      _ = cp.a' := cp.path_end
  have hadj := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hrev := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    (Γ.adjacent_symm cp.firstStep_adj)
  have hZa : z Γ cp.a ≤ q Γ cp.a := (h73.center_core _ _ hadj).trans
    ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hZb : z Γ cp.firstStep ≤ q Γ cp.firstStep := (h73.center_core _ _ hrev).trans
    ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hnoncomm : ¬ q Γ cp.a ≤ Subgroup.centralizer (q Γ cp.firstStep : Set G) := by
    intro hcomm
    apply ctx.commutator_ne
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [← hfirst]
    exact hZa.trans (hcomm.trans (Subgroup.centralizer_le hZb))
  have he (d : Γ.Vertex) (hd : d = cp.a ∨ d = cp.firstStep) :
      IsElementaryAbelian 2 (q Γ d) := by
    let _ := helementary d hd
    rw [q, Γ.twoCoreAt_def]
    change IsElementaryAbelian 2 ((pCore 2 (GAt Γ d)).map (GAt Γ d).subtype)
    exact IsElementaryAbelian.map (GAt Γ d).subtype
  let _ := he cp.a (Or.inl rfl)
  let _ := he cp.firstStep (Or.inr rfl)
  have hSylow := SevenSix.edge_sylow_data h7 Γ cp
  have hcoreS := SevenSix.local_cores_le_edge_sylow h7 Γ cp
  have hquot := eight_two_dihedral_core_local ctx hcenter
  have hindex (d : Γ.Vertex) (hS : IsSylowTwoIn S (GAt Γ d)) :
      (q Γ d).relIndex S = 2 := by
    rw [q, Γ.twoCoreAt_def]
    exact fourFactor_core_index_two _ _ hS (hquot d)
  have hleft := fourFactor_rank_one_of_abelian_pair _ _ _ hcoreS.1 hcoreS.2
    (hindex _ hSylow.2) hnoncomm
  have hright := fourFactor_rank_one_of_abelian_pair _ _ _ hcoreS.2 hcoreS.1
    (hindex _ hSylow.1) (fun hcomm => hnoncomm (Subgroup.le_centralizer_iff.mp hcomm))
  have hfinish (d : Γ.Vertex) (hS : IsSylowTwoIn S (GAt Γ d))
      (haction : (Subgroup.centralizer (S : Set G)).relIndex (q Γ d) = 2) :
      ∃ T : Sylow 2 (GAt Γ d),
        (Subgroup.centralizer (T : Set (GAt Γ d))).relIndex
          (pCore 2 (GAt Γ d)) = 2 := by
    obtain ⟨hSP, T, hT⟩ := hS
    have hnative : (T : Subgroup (GAt Γ d)) = S.subgroupOf (GAt Γ d) := by
      apply Subgroup.map_injective (GAt Γ d).subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hSP]
      exact hT
    refine ⟨T, ?_⟩
    change (Subgroup.centralizer ((T : Subgroup (GAt Γ d)) : Set (GAt Γ d))).relIndex _ = 2
    rw [hnative, fourFactor_native_centralizer_index _ _ hSP]
    simpa only [q, Γ.twoCoreAt_def, GAt, stabilizer] using haction
  intro d hd
  rcases hd with rfl | rfl
  · exact hfinish _ hSylow.1 hleft
  · exact hfinish _ hSylow.2 hright

public theorem eight_two_distance_one_core_action
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1)
    (helementary : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d))) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ T : Sylow 2 (GAt ctx.Γ d),
          (Subgroup.centralizer (T : Set (GAt ctx.Γ d))).relIndex
            (pCore 2 (GAt ctx.Γ d)) = 2 :=
  eight_two_distance_one_core_action_local ctx.toLocalContext hcenter hlength helementary

end Stellmacher.SectionEight
