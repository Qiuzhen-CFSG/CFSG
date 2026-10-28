module
public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Theory.GroupTheory.SpecificGroups.OddDihedralTwoNormalizer

/-!
# A backward module generates the middle vertex stabilizer

At critical length two in Stellmacher (8.2), take the supplied neighbors
m,n and the second generating equality Gm=(Gm intersect Gn) join Zfirst.
If Vn is outside Qm, then Vn and the original edge Ga intersect Gm generate
Gm. Every vertex and quotient refers to the original local context.

Critical minimality places Vn in Qn, hence in Gm. Its image in the actual
odd-dihedral core quotient of Gm is a nontrivial two-subgroup. The edge
Gm intersect Gn normalizes Vn, so its quotient image lies in that two-group's
self-normalizer. Thus this whole edge lies in Vn join Qm. The supplied second
generation yields Gm=(Vn join Zfirst) join Qm. Both Zfirst and Qm lie in the
original edge Ga intersect Gm, which proves the desired generation.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed p.38,
refs/latex/stellmacher-n-group.tex, after the third shifted critical pair.
The separate third-shift theorem supplies Vn not contained in Qm; no arbitrary
choice of a new Sylow subgroup or extra quotient-generation premise is used.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem normalizer_le_sup_core_of_odd_dihedral
    {P : Type*} [Group P] [Finite P]
    (hD : ∃ k : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ k)))
    (A : Subgroup P) (hAp : IsPGroup 2 A) (hout : ¬ A ≤ pCore 2 P) :
    Subgroup.normalizer (A : Set P) ≤ A ⊔ pCore 2 P := by
  let projection := QuotientGroup.mk' (pCore 2 P)
  have hne : A.map projection ≠ ⊥ := by
    intro hbot
    apply hout
    have hkernel := (Subgroup.map_eq_bot_iff A).mp hbot
    rwa [QuotientGroup.ker_mk'] at hkernel
  have hmap := Subgroup.le_normalizer_map (H := A) projection
  obtain ⟨k, ⟨model⟩⟩ := hD
  rw [odd_dihedral_two_subgroup_normalizer (3 ^ k) ((by decide : Odd 3).pow)
    model (A.map projection) (hAp.map projection) hne] at hmap
  have hpreimage := Subgroup.comap_mono (f := projection) hmap
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hpreimage
  exact le_sup_left.trans hpreimage

public theorem eight_two_backward_module_generates_middle_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : ctx.criticalPath.length = 2)
    (m n : ctx.Γ.Vertex)
    (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hn : n ∈ neighborhood ctx.Γ m)
    (hgen : (GAt ctx.Γ m ⊓ GAt ctx.Γ n) ⊔ ZAt ctx.Γ ctx.criticalPath.firstStep = GAt ctx.Γ m)
    (hVnot : ¬ VAt ctx.Γ n ≤ QAt ctx.Γ m) :
    VAt ctx.Γ n ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) = GAt ctx.Γ m := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ m
  let V := v Γ n
  let E := P ⊓ stabilizer Γ n
  change cp.length = 2 at hlen
  have hmn : m ∈ neighborhood Γ n :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hn))
  have ham : cp.a ∈ neighborhood Γ m :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm))
  have hQnP : q Γ n ≤ P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core n m hmn
      (default : Sylow 2 ↥(stabilizer Γ n ⊓ stabilizer Γ m))).2.2
  have hVQn : V ≤ q Γ n :=
    SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) n
  have hVP : V ≤ P := hVQn.trans hQnP
  have hQnp : IsPGroup 2 (q Γ n) := by
    rw [q, Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := stabilizer Γ n)).map (stabilizer Γ n).subtype
  let A := V.subgroupOf P
  let I := E.subgroupOf P
  have hAp : IsPGroup 2 A :=
    (hQnp.to_le hVQn).comap_of_injective P.subtype P.subtype_injective
  have hAout : ¬ A ≤ pCore 2 P := by
    intro hle
    apply hVnot
    have hmap := Subgroup.map_mono (f := P.subtype) hle
    rw [show A = V.subgroupOf P from rfl,
      Subgroup.map_subgroupOf_eq_of_le hVP] at hmap
    exact hmap.trans_eq (Γ.twoCoreAt_def m).symm
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_right.trans (stabilizer_le_normalizer_v Γ n)
  have hIA : I ≤ Subgroup.normalizer (A : Set P) :=
    (Subgroup.comap_mono hEV).trans (Subgroup.le_normalizer_comap P.subtype)
  have hIAQ : I ≤ A ⊔ pCore 2 P := hIA.trans
    (normalizer_le_sup_core_of_odd_dihedral
      (eight_two_dihedral_core_local ctx hcenter m) A hAp hAout)
  have hEVQ : E ≤ V ⊔ q Γ m := by
    have hmap := Subgroup.map_mono (f := P.subtype) hIAQ
    rw [Subgroup.map_sup,
      show I = E.subgroupOf P from rfl,
      show A = V.subgroupOf P from rfl,
      Subgroup.map_subgroupOf_eq_of_le (show E ≤ P from inf_le_left),
      Subgroup.map_subgroupOf_eq_of_le hVP] at hmap
    rw [q, Γ.twoCoreAt_def]
    exact hmap
  have hQmA : q Γ m ≤ stabilizer Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core m cp.a ham
      (default : Sylow 2 ↥(stabilizer Γ m ⊓ stabilizer Γ cp.a))).2.2
  have hQmP : q Γ m ≤ P := by
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQmEdge : q Γ m ≤ stabilizer Γ cp.a ⊓ P := le_inf hQmA hQmP
  have hQaP : q Γ cp.a ≤ P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a m hm
      (default : Sylow 2 ↥(stabilizer Γ cp.a ⊓ stabilizer Γ m))).2.2
  have hQaA : q Γ cp.a ≤ stabilizer Γ cp.a := by
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hZfirstVa : z Γ cp.firstStep ≤ v Γ cp.a := by
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨cp.firstStep, hfirst, rfl⟩
  have hZfirstQa : z Γ cp.firstStep ≤ q Γ cp.a := hZfirstVa.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.a)
  have hZfirstEdge : z Γ cp.firstStep ≤ stabilizer Γ cp.a ⊓ P :=
    hZfirstQa.trans (le_inf hQaA hQaP)
  change V ⊔ (stabilizer Γ cp.a ⊓ P) = P
  refine le_antisymm (sup_le hVP inf_le_right) ?_
  change E ⊔ z Γ cp.firstStep = P at hgen
  exact hgen.ge.trans (sup_le
    (hEVQ.trans (sup_le le_sup_left (hQmEdge.trans le_sup_right)))
    (hZfirstEdge.trans le_sup_right))

end Stellmacher.SectionEight
