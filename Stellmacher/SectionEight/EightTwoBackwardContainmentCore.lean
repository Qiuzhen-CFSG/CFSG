module
public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# The first containment case of Stellmacher (8.2)

For the fixed Section Eight local context, assume the first-step vertex center
is noncentral. A backward neighbor whose edge stabilizer generates the
initial stabilizer with the opposite endpoint center cannot have its
center contained in the opposite stabilizer unless the critical length
exceeds one and the first-edge core intersection is normal in the initial
stabilizer. No critical-distance hypothesis is assumed.

The two backward centers generate a two-group in both relevant stabilizers.
The opposite stabilizer's dihedral core quotient has Sylow two-subgroups
of order two. Since the initial center is outside the opposite core, the
backward center lies in their product. That core centralizes the opposite
center, so conjugating the backward center changes it only by the initial
center. The generation hypothesis therefore makes the center join normal.
Its containment in the initial two-core and local transitivity exclude
length one. Result (7.3)(c) identifies its centralizer inside the initial
core with the backward core intersection, proving normality. Finally the
graph action and core covariance transport this intersection to the first
edge; the normal subgroup is unchanged by the transporting conjugation.
Only the packaged dihedral quotients and genuine Section Seven hypotheses
are used. The legacy signature is retained through `toLocalContext`.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.2), pp.37–38,
`refs/latex/stellmacher-n-group.tex`, the first containment case. This is the
input to the separate smaller-local-Sylow and translate-normality arguments.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped Pointwise
universe u

private theorem normalizer_centralizer {G : Type*} [Group G] (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (A : Set G))).mp inferInstance

private theorem core_index_two
    {G : Type*} [Group G] [Finite G] (P W : Subgroup G)
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

private theorem two_subgroup_le_sup_core
    {G : Type*} [Group G] [Finite G] (P A B : Subgroup G)
    (hle : A ⊔ B ≤ P) (hp : IsPGroup 2 (A ⊔ B : Subgroup G))
    (hnot : ¬ A ≤ twoCoreIn P)
    (hD : ∃ n : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ n))) :
    B ≤ A ⊔ twoCoreIn P := by
  obtain ⟨T, hT⟩ := (hp.comap_subtype (K := P)).exists_le_sylow
  let W := sylowTwoAmbient P T
  have hAW : A ⊔ B ≤ W := by
    intro element helement
    exact ⟨⟨element, hle helement⟩, hT helement, rfl⟩
  have hindex := core_index_two P W ⟨Subgroup.map_subtype_le _, T, rfl⟩ hD
  obtain ⟨element, hA, hQ⟩ := SetLike.not_le_iff_exists.mp hnot
  intro other hB
  by_cases hother : other ∈ twoCoreIn P
  · exact (le_sup_right : twoCoreIn P ≤ A ⊔ twoCoreIn P) hother
  · let elementW : W := ⟨element, hAW ((le_sup_left : A ≤ A ⊔ B) hA)⟩
    let otherW : W := ⟨other, hAW ((le_sup_right : B ≤ A ⊔ B) hB)⟩
    have hprod : otherW * elementW⁻¹ ∈ (twoCoreIn P).subgroupOf W :=
      ((twoCoreIn P).subgroupOf W).mul_mem_iff_of_index_two hindex |>.mpr
        (by change other ∈ twoCoreIn P ↔ element⁻¹ ∈ twoCoreIn P; simp [hother, hQ])
    have hmem : other * element⁻¹ ∈ A ⊔ twoCoreIn P :=
      (le_sup_right : twoCoreIn P ≤ A ⊔ twoCoreIn P) hprod
    simpa [mul_assoc] using (A ⊔ twoCoreIn P).mul_mem hmem
      ((le_sup_left : A ≤ A ⊔ twoCoreIn P) hA)

private theorem normalizes_sup_of_le_sup_centralizer
    {G : Type*} [Group G] (A B D : Subgroup G)
    (hDA : D ≤ Subgroup.normalizer (A : Set G))
    (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hB : B ≤ A ⊔ Subgroup.centralizer (D : Set G)) :
    D ≤ Subgroup.normalizer ((B ⊔ A : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro element helement
  have hmap : B ⊔ A ≤ (B ⊔ A).comap (MulAut.conj element).toMonoidHom := by
    apply sup_le
    · intro other hother
      have hother' := hB hother
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (hAD.trans (normalizer_centralizer D))] at hother'
      obtain ⟨left, hleft, right, hright, rfl⟩ := hother'
      have hcomm : element * left * element⁻¹ * left⁻¹ ∈ A :=
        A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDA helement) left).mp hleft)
          (A.inv_mem hleft)
      have heq : element⁻¹ * right = right * element⁻¹ :=
        Subgroup.mem_centralizer_iff.mp hright element⁻¹ (D.inv_mem helement)
      change element * (left * right) * element⁻¹ ∈ B ⊔ A
      have hprod := (B ⊔ A).mul_mem ((le_sup_right : A ≤ B ⊔ A) hcomm)
        ((le_sup_left : B ≤ B ⊔ A) hother)
      convert hprod using 1
      simpa [mul_assoc] using heq.symm
    · intro other hother
      exact (le_sup_right : A ≤ B ⊔ A)
        ((Subgroup.mem_normalizer_iff.mp (hDA helement) other).mp hother)
  exact hmap

private theorem z_le_core_of_neighbor
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2) (Γ : CosetGraphContext G S P1 P2)
    {d l : Γ.Vertex} (hl : l ∈ neighborhood Γ d) : z Γ d ≤ q Γ d :=
  ((lemma_seven_three h Γ).center_core d l hl).trans
    ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))

private theorem q_le_stabilizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (d : Γ.Vertex) : q Γ d ≤ stabilizer Γ d := by
  rw [q, Γ.twoCoreAt_def]
  exact Subgroup.map_subtype_le _

private theorem backward_center_join_normal
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (m : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hgen : (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
      ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a)
    (hcontained : ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a') :
    NormalIn (ZAt ctx.Γ m ⊔ ZAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h7 := ctx.sectionSeven
  have h73 := lemma_seven_three h7 Γ
  have h74 := lemma_seven_four h7 Γ cp
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hmrev := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm))
  have hZaGa := (z_le_core_of_neighbor h7 Γ hfirst).trans (q_le_stabilizer Γ cp.a)
  have hZmGa : z Γ m ≤ stabilizer Γ cp.a :=
    (z_le_core_of_neighbor h7 Γ hmrev).trans
      ((h73.sylow_and_core m cp.a hmrev default).2.2)
  have hZaPend := h74.first_containment.1.trans h74.first_containment.2
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ hfirst
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ hmrev
  have hp : IsPGroup 2 (z Γ cp.a ⊔ z Γ m : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 (z Γ cp.a)).to_sup_of_normal_left'
      (IsElementaryAbelian.isPGroup 2 (z Γ m))
      (hZmGa.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hZanot : ¬ z Γ cp.a ≤ twoCoreIn (stabilizer Γ cp.a') := by
    rw [← show q Γ cp.a' = twoCoreIn (stabilizer Γ cp.a') from Γ.twoCoreAt_def cp.a']
    exact cp.critical.2
  have hZmSup := two_subgroup_le_sup_core (stabilizer Γ cp.a')
    (z Γ cp.a) (z Γ m) (sup_le hZaPend hcontained) hp hZanot
    (eight_two_dihedral_core_local ctx hcenter cp.a')
  have hQcentral : twoCoreIn (stabilizer Γ cp.a') ≤
      Subgroup.centralizer (z Γ cp.a' : Set G) := by
    rw [← show q Γ cp.a' = twoCoreIn (stabilizer Γ cp.a') from Γ.twoCoreAt_def cp.a']
    rw [← (h74.commutator_case ctx.commutator_ne).1 default]
    exact inf_le_right
  have hZendN := normalizes_sup_of_le_sup_centralizer
    (z Γ cp.a) (z Γ m) (z Γ cp.a')
    (h74.reverse_containment.1.trans (stabilizer_le_normalizer_z Γ cp.a))
    (hZaPend.trans (stabilizer_le_normalizer_z Γ cp.a'))
    (hZmSup.trans (sup_le_sup_left hQcentral _))
  have hNle : z Γ m ⊔ z Γ cp.a ≤ stabilizer Γ cp.a := sup_le hZmGa hZaGa
  refine ⟨hNle, (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr ?_⟩
  change (stabilizer Γ cp.a ⊓ stabilizer Γ m) ⊔ z Γ cp.a' = stabilizer Γ cp.a at hgen
  rw [← hgen]
  exact sup_le
    ((le_inf (inf_le_right.trans (stabilizer_le_normalizer_z Γ m))
      (inf_le_left.trans (stabilizer_le_normalizer_z Γ cp.a))).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)) hZendN

private theorem centrality_of_map
    {G : Type*} [Group G] (A P : Subgroup G) (e : G ≃* G) (hAP : A ≤ P)
    (h : A.map e.toMonoidHom ≤ CenterAmbient (P.map e.toMonoidHom)) :
    A ≤ CenterAmbient P := by
  intro element helement
  refine ⟨⟨element, hAP helement⟩, ?_, rfl⟩
  change (⟨element, hAP helement⟩ : P) ∈ Subgroup.center P
  rw [Subgroup.mem_center_iff]
  intro other
  apply Subtype.ext
  change (other : G) * element = element * (other : G)
  apply e.injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using Subgroup.mem_centralizer_iff.mp
    (SevenSix.centerAmbient_le_centralizer _ (h (Subgroup.mem_map_of_mem _ helement)))
    (e other) (Subgroup.mem_map_of_mem _ other.property)

private theorem centralizer_sup {G : Type*} [Group G] (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (le_sup_left : A ≤ A ⊔ B))
      (Subgroup.centralizer_le (le_sup_right : B ≤ A ⊔ B))
  · apply Subgroup.le_centralizer_iff.mpr
    exact sup_le (Subgroup.le_centralizer_iff.mp inf_le_left)
      (Subgroup.le_centralizer_iff.mp inf_le_right)

public theorem eight_two_core_intersection_normal_of_backward_containment_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (m : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hgen : (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
      ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a)
    (hcontained : ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a') :
    1 < ctx.criticalPath.length ∧
      NormalIn (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
        (GAt ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h7 := ctx.sectionSeven
  have h73 := lemma_seven_three h7 Γ
  have h74 := lemma_seven_four h7 Γ cp
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hmrev := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm))
  have hN := backward_center_join_normal ctx hcenter m hm hgen hcontained
  let N := z Γ m ⊔ z Γ cp.a
  have hNnorm : stabilizer Γ cp.a ≤ Subgroup.normalizer (N : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN.1).mp hN.2
  have hZmGa : z Γ m ≤ stabilizer Γ cp.a := (le_sup_left : z Γ m ≤ N).trans hN.1
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ hfirst
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ hmrev
  have hNp : IsPGroup 2 N :=
    (IsElementaryAbelian.isPGroup 2 (z Γ m)).to_sup_of_normal_right'
      (IsElementaryAbelian.isPGroup 2 (z Γ cp.a))
      (hZmGa.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hNQ : N ≤ q Γ cp.a := by
    have hcore : N.subgroupOf (stabilizer Γ cp.a) ≤ pCore 2 (stabilizer Γ cp.a) :=
      le_sSup ⟨hN.2, hNp.comap_subtype⟩
    have hmap := Subgroup.map_mono (f := (stabilizer Γ cp.a).subtype) hcore
    rw [Subgroup.map_subgroupOf_eq_of_le hN.1] at hmap
    rw [q, Γ.twoCoreAt_def]
    exact hmap
  obtain ⟨actor, hactor⟩ := (lemma_seven_one h7 Γ).local_transitivity cp.a hfirst hm
  let conjugation := MulAut.conj ((actor : H)⁻¹)
  have hfix : Γ.act (actor : H) cp.a = cp.a := by
    have hmem := actor.property
    change (actor : H) ∈ (Γ.vertexStabilizer cp.a : Set H) at hmem
    rwa [Γ.stabilizer_def cp.a] at hmem
  have hQa : (q Γ cp.a).map conjugation.toMonoidHom = q Γ cp.a := by
    rw [← SevenSix.q_act Γ (actor : H), hfix]
  have hZm : (z Γ cp.firstStep).map conjugation.toMonoidHom = z Γ m := by
    rw [← z_act Γ (actor : H), hactor]
  have hQm : (q Γ cp.firstStep).map conjugation.toMonoidHom = q Γ m := by
    rw [← SevenSix.q_act Γ (actor : H), hactor]
  have hfirstQ : z Γ cp.firstStep ≤ q Γ cp.a := by
    apply (Subgroup.map_le_map_iff_of_injective (f := conjugation.toMonoidHom)
      conjugation.injective).mp
    rw [hZm, hQa]
    exact (le_sup_left : z Γ m ≤ N).trans hNQ
  have hlength : 1 < cp.length := by
    by_contra hnot
    have hlen : cp.length = 1 := by have := cp.length_pos; omega
    have heq : cp.firstStep = cp.a' := by
      calc
        cp.firstStep = cp.path ⟨1, by have := cp.length_pos; omega⟩ := cp.path_first.symm
        _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by congr 1; apply Fin.ext; exact hlen.symm
        _ = cp.a' := cp.path_end
    exact (h74.commutator_case ctx.commutator_ne).2.2 (heq ▸ hfirstQ)
  have hPm : (stabilizer Γ cp.firstStep).map conjugation.toMonoidHom = stabilizer Γ m := by
    change conjugateBy (stabilizer Γ cp.firstStep) ((actor : H)⁻¹) = stabilizer Γ m
    rw [← stabilizer_act Γ (actor : H), hactor]
  have hmnoncentral : ¬ z Γ m ≤ CenterAmbient (stabilizer Γ m) := by
    intro hmcentral
    apply hcenter
    apply centrality_of_map (z Γ cp.firstStep) (stabilizer Γ cp.firstStep) conjugation
      ((z_le_core_of_neighbor h7 Γ
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))).trans
          (q_le_stabilizer Γ cp.firstStep))
    rwa [hZm, hPm]
  let T : Sylow 2 ↥(stabilizer Γ m ⊓ stabilizer Γ cp.a) := default
  let W := sylowTwoAmbient (stabilizer Γ m ⊓ stabilizer Γ cp.a) T
  have hW := (h73.sylow_and_core m cp.a hmrev T).2.1
  have hQaW : q Γ cp.a ≤ W := by
    obtain ⟨_, sylow, hsylow⟩ := hW
    rw [q, Γ.twoCoreAt_def]
    change twoCoreIn (stabilizer Γ cp.a) ≤ W
    change (sylow : Subgroup (stabilizer Γ cp.a)).map (stabilizer Γ cp.a).subtype = W at hsylow
    rw [← hsylow]
    exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal sylow)
  have hCm : W ⊓ Subgroup.centralizer (z Γ m : Set H) = q Γ m := by
    rcases h73.centralizer_alternative m cp.a hmrev T with hleft | hright
    · exact hleft
    · exact (hmnoncentral (hright.1.trans_le (SevenSix.omegaOneCenter_le_centerAmbient _))).elim
  have hQaCa : q Γ cp.a ≤ Subgroup.centralizer (z Γ cp.a : Set H) := by
    rw [← h74.edge_centralizer]
    exact inf_le_right
  have hCeq : q Γ cp.a ⊓ Subgroup.centralizer (N : Set H) = q Γ cp.a ⊓ q Γ m := by
    dsimp only [N]
    rw [centralizer_sup]
    apply le_antisymm
    · intro element helement
      exact ⟨helement.1, hCm ▸ ⟨hQaW helement.1, helement.2.1⟩⟩
    · intro element helement
      have hmC : element ∈ Subgroup.centralizer (z Γ m : Set H) := by
        have hmW : element ∈ W ⊓ Subgroup.centralizer (z Γ m : Set H) := hCm ▸ helement.2
        exact hmW.2
      exact ⟨helement.1, hmC, hQaCa helement.1⟩
  have hKnorm : stabilizer Γ cp.a ≤
      Subgroup.normalizer ((q Γ cp.a ⊓ q Γ m : Subgroup H) : Set H) := by
    rw [← hCeq]
    exact (le_inf (SevenSix.stabilizer_le_normalizer_q Γ cp.a)
      (hNnorm.trans (normalizer_centralizer N))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hKmap : (q Γ cp.a ⊓ q Γ m).map conjugation.toMonoidHom = q Γ cp.a ⊓ q Γ m :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hKnorm ((stabilizer Γ cp.a).inv_mem actor.property))
  have hKeq : q Γ cp.a ⊓ q Γ cp.firstStep = q Γ cp.a ⊓ q Γ m := by
    apply Subgroup.map_injective (f := conjugation.toMonoidHom) conjugation.injective
    rw [Subgroup.map_inf _ _ _ conjugation.injective, hQa, hQm, hKmap]
  refine ⟨hlength, ?_⟩
  change NormalIn (q Γ cp.a ⊓ q Γ cp.firstStep) (stabilizer Γ cp.a)
  rw [hKeq]
  exact ⟨inf_le_left.trans (q_le_stabilizer Γ cp.a),
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_left.trans (q_le_stabilizer Γ cp.a))).mpr hKnorm⟩

public theorem eight_two_core_intersection_normal_of_backward_containment
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (m : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hgen : (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
      ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a)
    (hcontained : ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a') :
    1 < ctx.criticalPath.length ∧
      NormalIn (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
        (GAt ctx.Γ ctx.criticalPath.a) :=
  eight_two_core_intersection_normal_of_backward_containment_local
    ctx.toLocalContext hcenter m hm hgen hcontained

end Stellmacher.SectionEight
