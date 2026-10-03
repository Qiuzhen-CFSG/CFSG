module
public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.SectionEight.EightTwoCriticalPairTransport
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts
public import Theory.GroupTheory.SpecificGroups.OddDihedralTwoNormalizer
public import Theory.GroupTheory.Commutator.ElementaryIndexTwoQuadratic

/-!
# Quadratic edge action in the noncentral case of Stellmacher (8.2)

For adjacent vertices d,m, the edge intersection acts quadratically on Z_d
under the actual local Section Eight context and first-step noncentrality.
No additional Sylow-intersection or faithful-action hypothesis is imposed.

Result (7.3) supplies a Sylow subgroup of the edge whose ambient image W
is Sylow in both stabilizers. Their odd-dihedral core quotients put both
cores at index two in W. Containment of one core in the other would force
equality and hence a nontrivial normal two-subgroup of the group generated
by both stabilizers, contradicting the trivial ambient core.
The image of Q_m in G_d/Q_d is therefore a nontrivial two-subgroup. The edge
normalizes this image, whose odd-dihedral normalizer is itself. Thus the
edge lies in W and is itself Sylow. Finally, Q_d centralizes the elementary
abelian group Z_d; its index-two quotient in the edge acts quadratically.

This gives the edge-centralization input for the shifted commutators in
Stellmacher (8.2), Journal of Algebra 190 (1997), pp.37–38,
`refs/latex/stellmacher-n-group.tex`. The core quotients and graph data come
from (6.3), (7.1), and (7.3); neither a critical-distance bound nor the final
stabilizer classification is used. The exact core-index and edge-Sylow
results are also exported for the distance-two common-subgroup argument.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The local core has index two in every supplied Sylow image. -/
public theorem eight_two_core_relIndex_two
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


private theorem core_le_edge_sylow
    {G : Type u} [Group G] [Finite G] (P W : Subgroup G)
    (hW : IsSylowTwoIn W P) : twoCoreIn P ≤ W := by
  obtain ⟨_, T, hT⟩ := hW
  rw [← hT]
  exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal T)

private theorem adjacent_core_noncontainment
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (d m : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d m) :
    ¬ q ctx.Γ m ≤ q ctx.Γ d := by
  let Γ := ctx.Γ
  let h := ctx.sectionSeven
  let P := stabilizer Γ d
  let M := stabilizer Γ m
  let K := P ⊓ M
  let T : Sylow 2 K := default
  let W := sylowTwoAmbient K T
  have hm : m ∈ neighborhood Γ d :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj
  have hd : d ∈ neighborhood Γ m :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj)
  obtain ⟨hWd, hWm, _⟩ := (lemma_seven_three h Γ).sylow_and_core d m hm T
  have hQdW : q Γ d ≤ W := by
    rw [q, Γ.twoCoreAt_def]
    exact core_le_edge_sylow P W hWd
  have hQmW : q Γ m ≤ W := by
    rw [q, Γ.twoCoreAt_def]
    exact core_le_edge_sylow M W hWm
  have hId : (q Γ d).relIndex W = 2 := by
    rw [q, Γ.twoCoreAt_def]
    exact eight_two_core_relIndex_two P W hWd (eight_two_dihedral_core_local ctx hcenter d)
  have hIm : (q Γ m).relIndex W = 2 := by
    rw [q, Γ.twoCoreAt_def]
    exact eight_two_core_relIndex_two M W hWm (eight_two_dihedral_core_local ctx hcenter m)
  have hcard : Nat.card (q Γ d) = Nat.card (q Γ m) := by
    have hdcard := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (q Γ d) W bot_le hQdW
    have hmcard := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (q Γ m) W bot_le hQmW
    simp only [Subgroup.relIndex_bot_left, hId, hIm] at hdcard hmcard
    omega
  intro hle
  have heq : q Γ m = q Γ d := Subgroup.eq_of_le_of_card_ge hle hcard.le
  have hPm : P ≤ Subgroup.normalizer (q Γ m : Set G) := by
    rw [heq]
    exact SevenSix.stabilizer_le_normalizer_q Γ d
  have hMm : M ≤ Subgroup.normalizer (q Γ m : Set G) :=
    SevenSix.stabilizer_le_normalizer_q Γ m
  have hgen : P ⊔ M = ⊤ := (edge_sectionThree_data h Γ hm T).2.2.2.2.1
  have hnormal : (q Γ m).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hPm hMm
  have hp : IsPGroup 2 (q Γ m) := by
    rw [q, Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := M)).map M.subtype
  have hbot : q Γ m = ⊥ :=
    le_bot_iff.mp ((show q Γ m ≤ pCore 2 G from le_sSup ⟨hnormal, hp⟩).trans_eq h.twoCore_eq_bot)
  have hZm : z Γ m ≤ q Γ m :=
    ((lemma_seven_three h Γ).center_core m d hd).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  apply eight_two_all_vertex_centers_noncentral_local ctx hcenter m
  exact (hZm.trans_eq hbot).trans bot_le


/-- In the noncentral case, the actual edge intersection is itself Sylow. -/
public theorem eight_two_adjacent_intersection_is_sylow_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (d m : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d m) :
    IsSylowTwoIn (stabilizer ctx.Γ d ⊓ stabilizer ctx.Γ m) (stabilizer ctx.Γ d) := by
  let Γ := ctx.Γ
  let h := ctx.sectionSeven
  let P := stabilizer Γ d
  let M := stabilizer Γ m
  let K := P ⊓ M
  let T : Sylow 2 K := default
  let W := sylowTwoAmbient K T
  have hm : m ∈ neighborhood Γ d :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj
  obtain ⟨hWd, hWm, _⟩ := (lemma_seven_three h Γ).sylow_and_core d m hm T
  have hQdW : q Γ d ≤ W := by
    rw [q, Γ.twoCoreAt_def]
    exact core_le_edge_sylow P W hWd
  have hQmW : q Γ m ≤ W := by
    rw [q, Γ.twoCoreAt_def]
    exact core_le_edge_sylow M W hWm
  have hQmP : q Γ m ≤ P := hQmW.trans hWd.1
  let R := (q Γ m).subgroupOf P
  let I := K.subgroupOf P
  let projection := QuotientGroup.mk' (pCore 2 P)
  have hRtwo : IsPGroup 2 R := by
    have hp : IsPGroup 2 (q Γ m) := by
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := M)).map M.subtype
    exact hp.comap_of_injective P.subtype P.subtype_injective
  have hIR : I ≤ Subgroup.normalizer (R : Set P) := by
    have hK : K ≤ Subgroup.normalizer (q Γ m : Set G) :=
      inf_le_right.trans (SevenSix.stabilizer_le_normalizer_q Γ m)
    exact (Subgroup.comap_mono hK).trans (Subgroup.le_normalizer_comap P.subtype)
  have hRne : R.map projection ≠ ⊥ := by
    intro hbot
    have hRcore := (Subgroup.map_eq_bot_iff R).mp hbot
    rw [QuotientGroup.ker_mk'] at hRcore
    apply adjacent_core_noncontainment ctx hcenter d m hadj
    have hmapped := Subgroup.map_mono (f := P.subtype) hRcore
    rw [show R = (q Γ m).subgroupOf P from rfl,
      Subgroup.map_subgroupOf_eq_of_le hQmP] at hmapped
    exact hmapped.trans_eq (Γ.twoCoreAt_def d).symm
  have himage : I.map projection ≤ (W.subgroupOf P).map projection := by
    have hN := (Subgroup.map_mono (f := projection) hIR).trans
      (Subgroup.le_normalizer_map projection)
    obtain ⟨n, ⟨model⟩⟩ := eight_two_dihedral_core_local ctx hcenter d
    rw [odd_dihedral_two_subgroup_normalizer (3 ^ n) ((by decide : Odd 3).pow)
      model (R.map projection) (hRtwo.map projection) hRne] at hN
    exact hN.trans (Subgroup.map_mono (Subgroup.comap_mono hQmW))
  have hkernel : projection.ker ≤ W.subgroupOf P := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    apply hQdW
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype hx
  have hIK : I ≤ W.subgroupOf P := by
    have hle := Subgroup.map_le_iff_le_comap.mp himage
    rwa [Subgroup.comap_map_eq, sup_eq_left.mpr hkernel] at hle
  have hKW : K ≤ W := by
    intro x hx
    exact hIK (show (⟨x, hx.1⟩ : P) ∈ I from hx)
  have heq : K = W := le_antisymm hKW (Subgroup.map_subtype_le _)
  obtain ⟨_, U, hU⟩ := hWd
  exact ⟨inf_le_left, U, hU.trans heq.symm⟩


public theorem eight_two_edge_quadratic_action_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (d m : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d m) :
    ⁅⁅ZAt ctx.Γ d, GAt ctx.Γ d ⊓ GAt ctx.Γ m⁆,
      GAt ctx.Γ d ⊓ GAt ctx.Γ m⁆ = ⊥ := by
  let Γ := ctx.Γ
  let K := stabilizer Γ d ⊓ stabilizer Γ m
  have hm : m ∈ neighborhood Γ d :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj
  let _ : IsElementaryAbelian 2 (z Γ d) :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hm
  have hSylow := eight_two_adjacent_intersection_is_sylow_local ctx hcenter d m hadj
  have hQK : q Γ d ≤ K := by
    rw [q, Γ.twoCoreAt_def]
    exact core_le_edge_sylow (stabilizer Γ d) K hSylow
  have hZQ : z Γ d ≤ Subgroup.centralizer (q Γ d : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core d m hm).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))
  have hindex : (q Γ d).relIndex K = 2 := by
    rw [q, Γ.twoCoreAt_def]
    exact eight_two_core_relIndex_two (stabilizer Γ d) K hSylow
      (eight_two_dihedral_core_local ctx hcenter d)
  exact Subgroup.commutator_commutator_eq_bot_of_centralizing_index_two
    (z Γ d) (q Γ d) K
    (inf_le_left.trans (stabilizer_le_normalizer_z Γ d)) hQK
    (Subgroup.le_centralizer_iff.mp hZQ) hindex

end Stellmacher.SectionEight
