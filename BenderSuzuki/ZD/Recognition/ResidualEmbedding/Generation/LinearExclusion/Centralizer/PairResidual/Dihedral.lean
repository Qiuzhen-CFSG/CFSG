module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.PairResidual
public import Theory.GroupTheory.CyclicDihedralKernel
public import Theory.GroupTheory.CyclicSylowOuterKernel

/-!
# The pair residual with an odd-dihedral centralizer

For the actual proper linear residual subgroup L, the outer action of
N_G(L)/L has kernel isomorphic to J=C_G(L): the kernel is the image of J,
and the simple nonabelian group L has trivial intersection with J.
If J is odd-dihedral, a cyclic outer group makes the derived subgroup of
N_G(L)/L odd. The kernel on the two-point group D is D∩L, also odd,
so the derived subgroup of D is odd. Its even order then makes O²(D)
proper, by the same focal-transfer endpoint used after Lemma 15.7.

This supplies the contradiction in the odd-dihedral alternative of source
Lemma 15.3. The actual centralizer model is retained as the earlier source
input; no pair residual, complement, or quotient kernel is assumed.
Source: GLS, Volume 4, Chapter 2, Lemma 15.3, final paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

private theorem residual_disjoint_centralizer :
    Disjoint (residualGenerated M z t) (centralizer (residualGenerated M z t : Set G)) := by
  let L := residualGenerated M z t
  have hmodel : IsSimpleBenderGroup L := .isPSL2 ⟨n, d.parameter, ⟨d.model⟩⟩
  let := hmodel.isSimple
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hmodel.not_commutative fun x y => by
        have hx : x ∈ center L := h ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm).elim
  apply disjoint_def.mpr
  intro x hx hxJ
  have hxc : (⟨x, hx⟩ : L) ∈ center L :=
    mem_center_iff.mpr fun y => Subtype.ext (hxJ y y.property)
  rw [hz] at hxc
  exact congrArg Subtype.val (mem_bot.mp hxc)

private def outerKernelMap (_d : Context Z M z t n) :
    centralizer (residualGenerated M z t : Set G) →*
      (MulAut.outerAction ((residualGenerated M z t).subgroupOf
        (normalizer (residualGenerated M z t : Set G)))).ker := by
  let L := residualGenerated M z t
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let q := QuotientGroup.mk' A
  let J := centralizer (L : Set G)
  exact (q.comp (inclusion (centralizer_le_normalizer L))).codRestrict _ (fun j => by
    rw [outerAction_kernel]
    exact ⟨inclusion (centralizer_le_normalizer L) j, (by
      intro x hx
      exact Subtype.ext (j.property x hx)), rfl⟩)

private theorem outerKernelMap_bijective : Function.Bijective (outerKernelMap d) := by
  constructor
  · intro x y hxy
    have he : QuotientGroup.mk' ((residualGenerated M z t).subgroupOf
        (normalizer (residualGenerated M z t : Set G)))
        (inclusion (centralizer_le_normalizer (residualGenerated M z t)) x) =
      QuotientGroup.mk' ((residualGenerated M z t).subgroupOf
        (normalizer (residualGenerated M z t : Set G)))
        (inclusion (centralizer_le_normalizer (residualGenerated M z t)) y) :=
      congrArg Subtype.val hxy
    have hLN := QuotientGroup.eq_iff_div_mem.mp he
    have hL : (x : G) / (y : G) ∈ residualGenerated M z t := hLN
    have hJ : (x : G) / (y : G) ∈ centralizer (residualGenerated M z t : Set G) :=
      (centralizer _).div_mem x.property y.property
    apply Subtype.ext
    exact div_eq_one.mp (disjoint_def.mp (residual_disjoint_centralizer d) hL hJ)
  · rintro ⟨x, hx⟩
    rw [outerAction_kernel] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hcJ : (c : G) ∈ centralizer (residualGenerated M z t : Set G) := by
      intro l hl
      exact congrArg Subtype.val (hc ⟨l, (residualGenerated M z t).le_normalizer hl⟩ hl)
    exact ⟨⟨c, hcJ⟩, rfl⟩

private theorem normalizer_quotient_commutator_odd {k : ℕ} (hk : Odd k)
    (eJ : centralizer (residualGenerated M z t : Set G) ≃* DihedralGroup k) :
    Odd (Nat.card (commutator
      ((normalizer (residualGenerated M z t : Set G)) ⧸
        (residualGenerated M z t).subgroupOf (normalizer (residualGenerated M z t : Set G))))) := by
  let L := residualGenerated M z t
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let eA : A ≃* MatrixGroups.PSL2BinaryMatrixGroup n :=
    (subgroupOfEquivOfLe L.le_normalizer).trans d.model
  let : IsCyclic (MulAut.Outer (MatrixGroups.PSL2BinaryMatrixGroup n)) :=
    Theory.PSL2.outer_isCyclic (BinaryGaloisField n)
  let : IsCyclic (MulAut.Outer A) :=
    isCyclic_of_surjective (MulAut.outerCongr eA).symm.toMonoidHom
      (MulAut.outerCongr eA).symm.surjective
  let e : centralizer (L : Set G) ≃* (MulAut.outerAction A).ker :=
    MulEquiv.ofBijective (outerKernelMap d) (outerKernelMap_bijective d)
  exact (MulAut.outerAction A).odd_card_commutator_of_cyclic_dihedral_kernel hk
    (e.symm.trans eJ)

omit d in
private theorem odd_commutator_of_odd_kernel
    {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]
    (f : H →* Q) (hker : Odd (Nat.card f.ker))
    (hcomm : Odd (Nat.card (commutator Q))) : Odd (Nat.card (commutator H)) := by
  let c := commutator H
  let g : c →* Q := f.comp c.subtype
  have hgle : g.range ≤ commutator Q := by
    rintro _ ⟨x, rfl⟩
    have hx := mem_map_of_mem f x.property
    rw [map_commutator_eq] at hx
    exact commutator_mono le_top le_top hx
  have hgrange : Odd (Nat.card g.range) := Odd.of_dvd_nat hcomm (card_dvd_of_le hgle)
  let i : g.ker →* f.ker :=
    (c.subtype.comp g.ker.subtype).codRestrict _ (fun x => x.property)
  have hi : Function.Injective i := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun a : f.ker => (a : H)) hxy))
  have hgker : Odd (Nat.card g.ker) := Odd.of_dvd_nat hker (card_dvd_of_injective i hi)
  have hcard := g.ker.card_mul_index
  rw [index_ker] at hcard
  exact hcard ▸ hgker.mul hgrange

/-- The odd-dihedral centralizer alternative of source 15.3 already forces
an odd derived subgroup of the actual two-point stabilizer. -/
public theorem Context.pair_commutator_odd_of_dihedral {k : ℕ} (hk : Odd k)
    (eJ : centralizer (residualGenerated M z t : Set G) ≃* DihedralGroup k) :
    Odd (Nat.card (commutator (residualPairStabilizer M t))) := by
  let L := residualGenerated M z t
  let D := residualPairStabilizer M t
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let f : D →* N ⧸ A := (QuotientGroup.mk' A).comp (inclusion d.pair_normalizes)
  have hker : Odd (Nat.card f.ker) := by
    let i : f.ker →* (D ⊓ L : Subgroup G) :=
      (D.subtype.comp f.ker.subtype).codRestrict _ (fun x =>
        ⟨x.val.property, (QuotientGroup.eq_one_iff
          (inclusion d.pair_normalizes (x : D))).mp x.property⟩)
    have hi : Function.Injective i := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun a : (D ⊓ L : Subgroup G) => (a : G)) hxy))
    exact Odd.of_dvd_nat
      (pair_inf_proper_residualGenerated_odd d.minimal.disconnected d.reduction
        d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper)
      (card_dvd_of_injective i hi)
  exact odd_commutator_of_odd_kernel f hker (normalizer_quotient_commutator_odd d hk eJ)

/-- The source 15.3 pair residual, with no order-two restriction on J. -/
public theorem Context.pairResidual_of_dihedral {k : ℕ} (hk : Odd k)
    (eJ : centralizer (residualGenerated M z t : Set G) ≃* DihedralGroup k) :
    External.hallPResidual 2 (residualPairStabilizer M t) ≠ ⊤ := by
  let D := residualPairStabilizer M t
  have hodd := d.pair_commutator_odd_of_dihedral hk eJ
  have heven := d.even_pair
  rw [card_eq_card_quotient_mul_card_subgroup (commutator D), Nat.even_mul] at heven
  have hquot : Even (Nat.card (D ⧸ commutator D)) :=
    heven.resolve_right (Nat.not_even_iff_odd.mpr hodd)
  let S : Sylow 2 D := Classical.choice inferInstance
  have hf : ControlsFusionIn (⊤ : Subgroup D) (S : Subgroup D) := by
    apply ControlsFusionIn.of_conjugators
    intro x y _ _ hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    exact ⟨⟨g, mem_top g⟩, hg⟩
  have hcard : Nat.card ((⊤ : Subgroup D) ⧸ derivedSubgroup (⊤ : Subgroup D)) =
      Nat.card (D ⧸ commutator D) := by
    simp only [derivedSubgroup, derivedSeries_one]
    let e : (⊤ : Subgroup D) ≃* D := Subgroup.topEquiv
    apply Nat.card_congr (QuotientGroup.congr _ _ e ?_).toEquiv
    have hr : (e : (⊤ : Subgroup D) →* D).range = ⊤ :=
      MonoidHom.range_eq_top_of_surjective _ e.surjective
    rw [map_commutator_eq, hr]
    rfl
  exact (hallPResidual_lt_top_of_dvd_abelianization_of_controlsFusionIn
    (⊤ : Subgroup D) S le_top hf (hcard.symm ▸ hquot.two_dvd)).ne

end BenderSuzuki.ZD.LinearExclusion
