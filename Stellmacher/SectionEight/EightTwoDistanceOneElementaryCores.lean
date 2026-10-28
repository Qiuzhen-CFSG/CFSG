module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts
public import Theory.Frattini.CentralElementarySupplement

/-!
# Elementary two-cores at critical distance one

In the noncentral first-step case of the actual Section Eight context,
critical distance one forces the two-cores of both distinguished edge
stabilizers to be elementary abelian. These are the native cores inside
the stabilizers, as needed for the final whole-group classification in (8.2).

The argument works directly on the distinguished edge: length one identifies
its second vertex with the opposite critical endpoint. Criticality and its
reverse from (7.4) put each vertex center outside the opposite core. The
actual dihedral core quotients from `eight_two_local_quotients` have Sylow
two-subgroups of order two, so both cores have index two in the shared
Sylow subgroup. Consequently each core is its vertex center joined with
the intersection of the two cores. The vertex centers are elementary and
central in their own cores by (7.3).

Central elementary supplements preserve the ambient Frattini subgroup.
The common Frattini image is therefore normalized by both generating
stabilizers. It is a normal two-subgroup of the ambient group, whose
two-core is trivial, so both Frattini subgroups vanish. Finally restrict
the elementary ambient cores back to the native stabilizer cores.

Source: Stellmacher (8.2), final paragraph, Journal of Algebra 190 (1997),
p.38, `refs/latex/stellmacher-n-group.tex`. The source uses a backward edge;
the direct argument here needs neither a transfer from that edge nor the
critical-distance theorem. No faithful-action quotient is substituted for
an actual two-core quotient.

The supplemental theorem uses `SectionEightLocalContext` and its genuine
Section Seven hypotheses. The original public theorem remains a wrapper
through `SectionEightContext.toLocalContext`, preserving the graph and
critical path definitionally. No additional Sylow hypothesis is imposed
on the ambient group of the supplemental theorem.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem core_index_two
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

private theorem central_supplement_of_index_two
    {G : Type u} [Group G] (W Q Z B : Subgroup G)
    (hQW : Q ≤ W) (hZQ : Z ≤ Q) (hnot : ¬ Z ≤ B)
    (hindex : B.relIndex W = 2) : Q = Z ⊔ (Q ⊓ B) := by
  obtain ⟨element, hZ, hB⟩ := SetLike.not_le_iff_exists.mp hnot
  apply le_antisymm
  · intro other hother
    by_cases hotherB : other ∈ B
    · exact (le_sup_right : Q ⊓ B ≤ Z ⊔ (Q ⊓ B)) ⟨hother, hotherB⟩
    · let elementW : W := ⟨element, hQW (hZQ hZ)⟩
      let otherW : W := ⟨other, hQW hother⟩
      have hprod : otherW * elementW⁻¹ ∈ B.subgroupOf W :=
        ((B.subgroupOf W).mul_mem_iff_of_index_two hindex).mpr
          (by change other ∈ B ↔ element⁻¹ ∈ B; simp [hotherB, hB])
      have hmem : other * element⁻¹ ∈ Z ⊔ (Q ⊓ B) :=
        (le_sup_right : Q ⊓ B ≤ Z ⊔ (Q ⊓ B))
          ⟨Q.mul_mem hother (Q.inv_mem (hZQ hZ)), hprod⟩
      simpa [mul_assoc] using (Z ⊔ (Q ⊓ B)).mul_mem hmem
        ((le_sup_left : Z ≤ Z ⊔ (Q ⊓ B)) hZ)
  · exact sup_le hZQ inf_le_left

private theorem normalizer_le_frattini_normalizer
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((frattini Q).map Q.subtype : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro element helement other hother
  obtain ⟨otherQ, hotherQ, rfl⟩ := hother
  let elementN : Subgroup.normalizer (Q : Set G) := ⟨element, helement⟩
  let automorphism := Subgroup.normalizerMonoidHom Q elementN
  have hfix := (inferInstance : (frattini Q).Characteristic).fixed automorphism
  have hmem : automorphism otherQ ∈ frattini Q := by
    change otherQ ∈ (frattini Q).comap automorphism.toMonoidHom
    rw [hfix]
    exact hotherQ
  exact ⟨automorphism otherQ, hmem, by
    simp [automorphism, elementN, mul_assoc,
      Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

private theorem elementary_of_equal_frattini
    {G : Type u} [Group G] [Finite G] (P L Q R : Subgroup G)
    (hgen : P ⊔ L = ⊤) (hcore : pCore 2 G = ⊥)
    (hQ : IsPGroup 2 Q) (hR : IsPGroup 2 R)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hphi : (frattini Q).map Q.subtype = (frattini R).map R.subtype) :
    IsElementaryAbelian 2 Q ∧ IsElementaryAbelian 2 R := by
  let N := (frattini Q).map Q.subtype
  have hPN : P ≤ Subgroup.normalizer (N : Set G) :=
    hPQ.trans (normalizer_le_frattini_normalizer Q)
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
    change L ≤ Subgroup.normalizer ((frattini Q).map Q.subtype : Set G)
    rw [hphi]
    exact hLR.trans (normalizer_le_frattini_normalizer R)
  have hnormal : N.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hPN hLN))
  have hNp : IsPGroup 2 N :=
    (hQ.to_subgroup (frattini Q)).map Q.subtype
  have hNbot : N = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨hnormal, hNp⟩
  let _ : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let _ : Fact (IsPGroup 2 R) := ⟨hR⟩
  constructor
  · apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    exact (Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective).mp hNbot
  · apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    apply (Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective).mp
    exact hphi ▸ hNbot

/-- At critical distance one, both distinguished stabilizers have elementary two-cores. -/
public theorem eight_two_distance_one_elementary_cores_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have h7 := ctx.sectionSeven
  have h73 := lemma_seven_three h7 Γ
  have h74 := lemma_seven_four h7 Γ cp
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
  have hcorele (d : Γ.Vertex) : q Γ d ≤ stabilizer Γ d := by
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hcorep (d : Γ.Vertex) : IsPGroup 2 (q Γ d) := by
    rw [q, Γ.twoCoreAt_def]
    exact pCore_isPGroup.map (stabilizer Γ d).subtype
  have hZa := h73.center_core _ _ hadj
  have hZb := h73.center_core _ _ hrev
  have hZale : z Γ cp.a ≤ q Γ cp.a := hZa.trans
    ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hZble : z Γ cp.firstStep ≤ q Γ cp.firstStep := hZb.trans
    ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hZacent : z Γ cp.a ≤ Subgroup.centralizer (q Γ cp.a : Set G) := hZa.trans
    ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
      (SevenSix.centerAmbient_le_centralizer _))
  have hZbcent : z Γ cp.firstStep ≤ Subgroup.centralizer (q Γ cp.firstStep : Set G) :=
    hZb.trans ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
      (SevenSix.centerAmbient_le_centralizer _))
  have hZanot : ¬ z Γ cp.a ≤ q Γ cp.firstStep := by
    rw [hfirst]
    exact cp.critical.2
  have hZbnot : ¬ z Γ cp.firstStep ≤ q Γ cp.a := by
    rw [hfirst]
    exact (h74.commutator_case ctx.commutator_ne).2.2
  have hSylow := SevenSix.edge_sylow_data h7 Γ cp
  have hcoreS := SevenSix.local_cores_le_edge_sylow h7 Γ cp
  have hquot := eight_two_dihedral_core_local ctx hcenter
  have hindex (d : Γ.Vertex) (hS : IsSylowTwoIn S (stabilizer Γ d)) :
      (q Γ d).relIndex S = 2 := by
    rw [q, Γ.twoCoreAt_def]
    exact core_index_two _ _ hS (hquot d)
  have hsuppa := central_supplement_of_index_two S _ _ _ hcoreS.1 hZale hZanot
    (hindex _ hSylow.2)
  have hsuppb := central_supplement_of_index_two S _ _ _ hcoreS.2 hZble hZbnot
    (hindex _ hSylow.1)
  have hPhiA := frattini_map_eq_of_central_elementary_supplement
    (q Γ cp.a) (q Γ cp.a ⊓ q Γ cp.firstStep) (z Γ cp.a)
    (hcorep _) (SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ hadj) hZacent hsuppa
  have hPhiB := frattini_map_eq_of_central_elementary_supplement
    (q Γ cp.firstStep) (q Γ cp.a ⊓ q Γ cp.firstStep) (z Γ cp.firstStep)
    (hcorep _) (SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ hrev) hZbcent
    (by simpa only [inf_comm] using hsuppb)
  have hgen : stabilizer Γ cp.a ⊔ stabilizer Γ cp.firstStep = ⊤ := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1, hedge.2]
      exact h7.generated
    · rw [hedge.1, hedge.2, sup_comm]
      exact h7.generated
  have helementary := elementary_of_equal_frattini _ _ _ _ hgen h7.twoCore_eq_bot
    (hcorep _) (hcorep _) (SevenSix.stabilizer_le_normalizer_q Γ cp.a)
    (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep) (hPhiA.trans hPhiB.symm)
  have htransfer (d : Γ.Vertex) (he : IsElementaryAbelian 2 (q Γ d)) :
      IsElementaryAbelian 2 (pCore 2 (stabilizer Γ d)) := by
    let _ := he
    have hi := IsElementaryAbelian.subgroupOf (p := 2) (hcorele d)
    rw [q, Γ.twoCoreAt_def] at hi
    change IsElementaryAbelian 2
      (((pCore 2 (stabilizer Γ d)).map (stabilizer Γ d).subtype).subgroupOf
        (stabilizer Γ d)) at hi
    rw [subgroupOf_map_subtype_eq] at hi
    exact hi
  intro d hd
  rcases hd with rfl | rfl
  · exact htransfer _ helementary.1
  · exact htransfer _ helementary.2

public theorem eight_two_distance_one_elementary_cores
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d)) :=
  eight_two_distance_one_elementary_cores_local ctx.toLocalContext hcenter hlength

end Stellmacher.SectionEight
