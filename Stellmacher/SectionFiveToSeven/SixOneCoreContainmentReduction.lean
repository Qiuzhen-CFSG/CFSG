module
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# The core-containment reduction in Stellmacher (6.1)

Under Hypothesis 2, assume for contradiction that the Baumann subgroup
`B(S)` lies in `Q₂ = O₂(P₂)`. Then `S` is the distinguished ambient Sylow
subgroup `S₀`, and the elementary Thompson subgroup `J(S)` is not contained
in `Q₁`. This is the opening reduction in the proof of Stellmacher (6.1),
Journal of Algebra 190 (1997), p.30; see `refs/latex/stellmacher-n-group.tex`.

The inclusion `J(S) ≤ B(S)` puts `J(S)` in `Q₂`. Whenever `J(S) ≤ Qᵢ`,
comparison of the maximum elementary-abelian orders in `Qᵢ ≤ S` identifies
`J(S)` with `J(Qᵢ)`. Automorphism covariance of the Thompson subgroup then
makes `J(S)` normal in `Pᵢ`. Normality in `P₂` excludes alternative (5.1)(c),
so either (a) or (b) gives `S = S₀`.

If `J(S)` also lay in `Q₁`, it would be a normal 2-subgroup of the actual
join `P₁ ∨ P₂`, whose 2-core is trivial by Hypothesis 2. This would give
`J(S) = 1` and hence `B(S) = S`. The assumed core containment would force
`S = Q₂`, contrary to the defining local-family condition. All normality
and core calculations are performed inside the join supplied by Hypothesis 2.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u
variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem core_le_sylow (S P : Subgroup H) (h : IsSylowTwoIn S P) :
    twoCoreIn P ≤ S := by
  obtain ⟨_, T, hT⟩ := h
  rw [← hT]
  exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T)

omit [Finite H] in
private theorem maxJ_le_baumann (S : Subgroup H) :
    elementaryAbelianMaxJ S ≤ baumannIn S := by
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  refine le_inf hJS ?_
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨zJ, hzJ, rfl⟩ := hz
  obtain ⟨zC, _, rfl⟩ := hzJ
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp zC.property) ⟨j, hj⟩).symm

private theorem maxJ_normal_of_le_core
    (S P : Subgroup H) (hSyl : IsSylowTwoIn S P)
    (hJQ : elementaryAbelianMaxJ S ≤ twoCoreIn P) :
    NormalIn (elementaryAbelianMaxJ S) P := by
  have hQS := core_le_sylow S P hSyl
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq (twoCoreIn P) S hQS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S (twoCoreIn P) hJQ
  have horder : elementaryAbelianMaxOrder (twoCoreIn P) = elementaryAbelianMaxOrder S :=
    le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (twoCoreIn P) :=
    le_antisymm (hlarge.2 horder.symm) (hsmall.2 horder)
  have hQP : twoCoreIn P ≤ P := Subgroup.map_subtype_le _
  have hQnormal : ((twoCoreIn P).subgroupOf P).Normal := by
    rw [twoCoreIn, subgroupOf_map_subtype_eq]
    infer_instance
  have hPnormQ : P ≤ Subgroup.normalizer (twoCoreIn P) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp hQnormal
  have hJP := hJQ.trans hQP
  refine ⟨hJP, (Subgroup.normal_subgroupOf_iff_le_normalizer hJP).mpr ?_⟩
  intro p hp
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hQmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPnormQ hp)
  change (twoCoreIn P).map (MulAut.conj p).toMonoidHom = twoCoreIn P at hQmap
  have hJmap := elementaryAbelianMaxJ_map_equiv (MulAut.conj p) (twoCoreIn P)
  rw [hQmap] at hJmap
  rw [hJeq]
  exact hJmap.symm

public theorem sixOne_coreContainment_reduction
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hB : baumannIn S ≤ twoCoreIn P2) :
    S = (S0 : Subgroup H) ∧ ¬ elementaryAbelianMaxJ S ≤ twoCoreIn P1 := by
  have hSyl1 : IsSylowTwoIn S P1 := h.fiveOne.P1_mem.1.2.1
  have hSyl2 : IsSylowTwoIn S P2 := h.fiveOne.P2_mem.1.2.1
  have hJ2 : elementaryAbelianMaxJ S ≤ twoCoreIn P2 := (maxJ_le_baumann S).trans hB
  have hn2 := maxJ_normal_of_le_core S P2 hSyl2 hJ2
  have hS0 : S = (S0 : Subgroup H) := by
    cases h.fiveOne.alternative with
    | a hS _ _ => exact hS
    | b hS _ => exact hS
    | c _ _ _ _ _ _ hnJ2 _ _ _ _ _ _ => exact (hnJ2 hn2).elim
  refine ⟨hS0, ?_⟩
  intro hJ1
  have hn1 := maxJ_normal_of_le_core S P1 hSyl1 hJ1
  let J := elementaryAbelianMaxJ S
  let L := P1 ⊔ P2
  have hJL : J ≤ L := hn1.1.trans le_sup_left
  have hLnormJ : L ≤ Subgroup.normalizer J :=
    sup_le ((Subgroup.normal_subgroupOf_iff_le_normalizer hn1.1).mp hn1.2)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hn2.1).mp hn2.2)
  have hJnormal : (J.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJL).mpr hLnormJ
  have hJp : IsPGroup 2 J :=
    h.sectionThreeHypotheses.nontrivial_two_subgroup.2.to_le (sSup_le fun _ hA => hA.1)
  have hJpL : IsPGroup 2 (J.subgroupOf L) :=
    hJp.of_equiv (Subgroup.subgroupOfEquivOfLe hJL).symm
  have hJcore : J ≤ twoCoreIn L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hJL]
    exact Subgroup.map_mono (show J.subgroupOf L ≤ pCore 2 L from le_sSup ⟨hJnormal, hJpL⟩)
  have hJbot : J = ⊥ := le_bot_iff.mp (hJcore.trans_eq h.fiveOne.join_twoCore_eq_bot)
  have hOmegaBot : omegaOneCenter J = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.map_subtype_le _).trans_eq hJbot
  have hBwhole : baumannIn S = S := by
    change S ⊓ Subgroup.centralizer (omegaOneCenter J : Set H) = S
    rw [hOmegaBot]
    apply inf_eq_left.mpr
    intro s _hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz1 : z = 1 := hz
    rw [hz1]
    simp
  have hSQ2 : S ≤ twoCoreIn P2 := hBwhole ▸ hB
  exact h.fiveOne.P2_mem.1.2.2.2 (le_antisymm hSQ2 (core_le_sylow S P2 hSyl2))

end Stellmacher.SectionsFiveToSeven
