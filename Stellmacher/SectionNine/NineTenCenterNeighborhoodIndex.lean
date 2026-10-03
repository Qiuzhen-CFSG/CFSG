module

public import Stellmacher.SectionNine.NineTenCenterCentralizingNeighbor
public import Stellmacher.SectionNine.NineTenCenterNormalizerIndex
public import Stellmacher.SectionNine.NineNineTerminalInputs
public import Theory.GroupTheory.TwoGroupIndexThree

/-!
# The index bound from the literal center commutator normalizer

Retain a critical path of length greater than three, its terminal
order-thirty-two wreath classification, its order-eight backward
intersection, and its own extraction coatom. Any two-subgroup in the
preterminal stabilizer centralizing R=[Z_initial,V_terminal] meets the
penultimate stabilizer with index at most two.

The actual R-centralizing neighbor mover transports the terminal normalizer
of R joined with its center to the preterminal one and preserves the
penultimate stabilizer. Their relative index remains three. The supplied
two-subgroup normalizes both R and the preterminal center, hence lies in
that transported normalizer. Its intersection index is bounded by three
and is a power of two, giving the asserted bound.

This is the upper-bound argument for Stellmacher (9.10)(7), printed p.58.
The exact-distance neighborhood is a consumer; the bound itself only needs
the stated containment, centralization, and two-group hypotheses.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_center_centralizing_two_subgroup_index_le_two
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (hcoatom : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.a')
      (VAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ ctx.criticalPath.a) 2)
    (W : Subgroup G) (hWtwo : IsPGroup 2 W)
    (hWpre : W ≤ GAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hWR : W ≤ Subgroup.centralizer
      ((⁅ZAt ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ : Subgroup G) : Set G)) :
    (GAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).relIndex W ≤ 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let R := ⁅ZAt Γ cp.a, VAt Γ cp.a'⁆
  let X := GAt Γ cp.a' ⊓ Subgroup.normalizer (R ⊔ ZAt Γ cp.a' : Subgroup G)
  let Y := GAt Γ preterminal ⊓ Subgroup.normalizer (R ⊔ ZAt Γ preterminal : Subgroup G)
  let P := GAt Γ penultimate
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hfirstNot : ¬ ZAt Γ cp.firstStep ≤ VAt Γ cp.a' := by
    intro hle
    have hbound := lemma_nine_nine_ambient ctx hle
    change 3 < cp.length at hb
    change cp.length ≤ 3 at hbound
    omega
  obtain ⟨actor, hactor, hactorNot⟩ := SetLike.not_le_iff_exists.mp cp.critical.2
  have hfirst := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  have hactorP : actor ∈ GAt Γ cp.a' := hfirst.2 (hfirst.1 hactor)
  obtain ⟨_, hactorIndex⟩ := nine_ten_transvection_of_coatom ctx hshort hfirstNot
    hcoatom actor hactor hactorNot
  have hindex := nine_ten_center_commutator_normalizer_index_three ctx hb
    hUcard hmodel ⟨actor, hactorP⟩ hactor hactorNot hactorIndex
  change P.relIndex X = 3 at hindex
  obtain ⟨y, hyP, hyR, hyt⟩ := nine_ten_center_commutator_centralizing_neighbor
    ctx hb hUcard hmodel hIcard hcoatom
  have hXmap : X.map (MulAut.conj y⁻¹).toMonoidHom = Y := by
    have hh := nine_nine_normalizer_conjugation Γ cp.a' R y hyR
    rw [hyt] at hh
    exact hh
  have hPmap : P.map (MulAut.conj y⁻¹).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer (P.inv_mem hyP))
  have hYindex : P.relIndex Y = 3 := by
    rw [← hXmap, ← hPmap,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hindex
  have hWRnormal : W ≤ Subgroup.normalizer (R : Set G) :=
    hWR.trans (Subgroup.centralizer_le_normalizer _)
  have hWZnormal : W ≤ Subgroup.normalizer (ZAt Γ preterminal : Set G) :=
    hWpre.trans (stabilizer_le_normalizer_z Γ preterminal)
  have hWY : W ≤ Y := by
    refine le_inf hWpre ?_
    intro mover hmover
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hRmap : R.map (MulAut.conj mover).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWRnormal hmover)
    have hZmap : (ZAt Γ preterminal).map (MulAut.conj mover).toMonoidHom =
        ZAt Γ preterminal :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWZnormal hmover)
    change (R ⊔ ZAt Γ preterminal).map (MulAut.conj mover).toMonoidHom =
      R ⊔ ZAt Γ preterminal
    rw [Subgroup.map_sup, hRmap, hZmap]
  exact Subgroup.two_group_relIndex_le_two_of_relIndex_three W P Y hWtwo hWY hYindex

end Stellmacher.SectionNine
