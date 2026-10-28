module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.HigherLinear
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Higher-linear residual comparison: all but the equal A₄ action case

The exact inner rows have residual orders 96 and 12 in dimension four,
and 21504 and 768 in dimension five. The last order comes from the corrected
cubic extension with an order-256 two-kernel; no elementary-kernel or splitting
assertion is used. Exact sequences and actual residual equivalences remain
explicit earlier table inputs, as does the earlier trivial-covering-kernel fact.

The graph residual A₆ is excluded because its order is divisible by five.
For the exceptional S₈ outer row, relative normality excludes the order-96
inner root residual: a normal A₄ would have two-power index in a two-perfect
group. This leaves equal ambient A₄ residuals in dimension four. Their actual
normalizer action is a further obligation; equality of their orders does not
exclude them. The two central images are kept in their respective component
quotients throughout the comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.4(1),(3),(8),(9), printed pp.1170–1171, and the proof of 16.4.11(2),
p.1193. The corrected PSL₅(2) kernel agrees with the expression on p.1200;
the false elementary-kernel row is documented in docs/quasithin-proof-basis.md.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic

abbrev A4 := alternatingGroup (Fin 4)
abbrev A6 := alternatingGroup (Fin 6)
abbrev C3 := Multiplicative (ZMod 3)

/-- An actual extension with the indicated two-kernel, without a splitting
or elementary-abelian assertion. The inclusion is the literal subgroup map. -/
structure TwoKernelExtension (X Y : Type*) [Group X] [Group Y] (k : ℕ) where
  kernel : Subgroup X
  sequence : GroupExtension kernel X Y
  inclusion_eq : sequence.inl = kernel.subtype
  kernel_card : Nat.card kernel = 2 ^ k

/-- The inner residual shapes in 16.1.4. The five-dimensional j₂ row uses
its corrected order-256 kernel, not the false elementary kernel on p.1171.
The three-dimensional quotient in the root row is the actual binary linear group. -/
inductive InnerRow (n : ℕ) (X : Type*) [Group X] : Prop
  | fourRoot (hn : n = 4) (row : Nonempty (TwoKernelExtension X C3 5))
  | fourJ2 (hn : n = 4) (row : Nonempty (X ≃* A4))
  | fiveRoot (hn : n = 5) (row : Nonempty (TwoKernelExtension X (LinearGroup 3) 7))
  | fiveJ2 (hn : n = 5) (row : Nonempty (TwoKernelExtension X C3 8))

/-- The two outer residual shapes. The exceptional A₄ row occurs only
in dimension four. Its permutation action is an additional, separate fact. -/
def OuterRow (n : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* A6) ∨ (n = 4 ∧ Nonempty (X ≃* A4))

private theorem a4_card : Nat.card A4 = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem a6_card : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem c3_card : Nat.card C3 = 3 := by
  simp [C3, Nat.card_eq_fintype_card]

private theorem linear_three_card : Nat.card (LinearGroup 3) = 168 := by
  calc
    Nat.card (LinearGroup 3) = Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
      (Nat.card_congr (matrixEquivLinear 3).toEquiv).symm
    _ = ∏ i : Fin 3, (Fintype.card (ZMod 2) ^ 3 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 3
    _ = 168 := by decide

/-- Exactness, rather than an extension label, gives the residual order. -/
theorem TwoKernelExtension.card {X Y : Type*} [Group X] [Group Y]
    [Finite X] (k : ℕ) (s : TwoKernelExtension X Y k) :
    Nat.card X = 2 ^ k * Nat.card Y := by
  have hk : s.sequence.rightHom.ker = s.kernel := by
    rw [← s.sequence.range_inl_eq_ker_rightHom, s.inclusion_eq, range_subtype]
  have hi : s.kernel.index = Nat.card Y := by
    rw [← hk, index_ker, s.sequence.rightHom.range_eq_top_of_surjective
      s.sequence.rightHom_surjective, card_top]
  simpa only [s.kernel_card, hi] using s.kernel.card_mul_index.symm

/-- Every inner row has order prime to five, including the corrected j₂ row. -/
theorem InnerRow.five_not_dvd {n : ℕ} {X : Type*} [Group X] [Finite X]
    (h : InnerRow n X) : ¬ 5 ∣ Nat.card X := by
  cases h with
  | fourRoot _ row =>
    obtain ⟨s⟩ := row
    rw [s.card, c3_card]
    norm_num
  | fourJ2 _ row =>
    obtain ⟨e⟩ := row
    rw [Nat.card_congr e.toEquiv, a4_card]
    norm_num
  | fiveRoot _ row =>
    obtain ⟨s⟩ := row
    rw [s.card, linear_three_card]
    norm_num
  | fiveJ2 _ row =>
    obtain ⟨s⟩ := row
    rw [s.card, c3_card]
    norm_num

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The actual source PSL quotient gives the eight-point component model
once the earlier covering result has removed its center. This uses the
canonical center/two-core identification and the checked PSL₄(2)–A₈ map. -/
noncomputable def componentAlternatingEquiv (d : Contrary T z L g R r)
    (hZ : center L = ⊥) (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2) :
    L ≃* alternatingGroup (Fin 8) := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      ((LiePreliminaries.centerQuotientEquivTwoCore (component_oddCore d)).trans
        (LiePreliminaries.higherLinearFourAlternatingEquiv hmodel))

omit [Finite G] in
private theorem conjugate_center_eq_bot (hZ : center L = ⊥) :
    center (L.conjBy g) = ⊥ := by
  let e : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  apply eq_bot_iff.mpr
  intro x hx
  have h := ((centerCongr e).symm ⟨x, hx⟩).property
  change e.symm x ∈ center L at h
  rw [hZ, mem_bot] at h
  exact e.symm.injective (h.trans e.symm.map_one.symm)

/-- Quotient images in the two different component quotients are compared
through the ambient residual. Only the inner covering kernel is removed. -/
theorem outer_card_dvd_inner (d : Contrary T z L g R r) (hZ : center L = ⊥) :
    Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z)) ∣
      Nat.card (centralImage L (residual L r)) := by
  have hd := card_dvd_of_surjective
    (centralImageMap ((residual_le (L.conjBy g) z).trans inf_le_left))
    (centralImageMap_surjective ((residual_le (L.conjBy g) z).trans inf_le_left))
  have hi := card_dvd_of_le d.residual_normal.1
  have he := Nat.card_congr
    (centralImageEquiv ((residual_le L r).trans inf_le_left) hZ).toEquiv
  exact he ▸ hd.trans hi

/-- All four inner rows exclude the graph A₆ residual. No identification
of the outer image in L/Z(L) with its image in L′/Z(L′) is made. -/
theorem graph_excluded (d : Contrary T z L g R r) (hZ : center L = ⊥)
    {n : ℕ} (hin : InnerRow n (centralImage L (residual L r)))
    (eout : centralImage (L.conjBy g) (residual (L.conjBy g) z) ≃* A6) : False := by
  have hd := outer_card_dvd_inner d hZ
  rw [Nat.card_congr eout.toEquiv, a6_card] at hd
  exact hin.five_not_dvd ((by decide : 5 ∣ 360).trans hd)

/-- The order-96 root residual cannot have a normal A₄: the quotient
would be a two-group, contradicting two-perfectness of the residual. -/
theorem four_root_excluded (d : Contrary T z L g R r) (hZ : center L = ⊥)
    (hin : TwoKernelExtension (centralImage L (residual L r)) C3 5)
    (eout : centralImage (L.conjBy g) (residual (L.conjBy g) z) ≃* A4) : False := by
  let X := residual L r
  let Y := residual (L.conjBy g) z
  have hX : Nat.card X = 96 := by
    rw [Nat.card_congr (centralImageEquiv
      ((residual_le L r).trans inf_le_left) hZ).toEquiv, hin.card, c3_card]
    norm_num
  have hY : Nat.card Y = 12 := by
    rw [Nat.card_congr ((centralImageEquiv
      ((residual_le (L.conjBy g) z).trans inf_le_left)
        (conjugate_center_eq_bot hZ)).trans eout).toEquiv, a4_card]
  let N := Y.subgroupOf X
  let : N.Normal := d.residual_normal.2.1
  have hN : Nat.card N = 12 :=
    (Nat.card_congr (subgroupOfEquivOfLe d.residual_normal.1).toEquiv).trans hY
  have hindex : N.index = 8 := by
    have hh := N.card_mul_index
    rw [hN, hX] at hh
    omega
  have hp : IsPGroup 2 (X ⧸ N) := IsPGroup.of_card (n := 3) (by
    rw [← index_eq_card, hindex]
    norm_num)
  have hperf : IsPPerfect 2 X :=
    isPPerfect_embedded_pResidual 2 (L ⊓ centralizer ({r} : Set G))
  have heq := hperf N inferInstance hp
  rw [heq, index_top] at hindex
  norm_num at hindex

/-- Comparing all numerical and normal-subgroup branches leaves exactly
the equal A₄ pair in dimension four. Excluding that pair still requires the
actual S₈ action; this theorem does not claim the full higher-linear exclusion. -/
theorem reduce_to_equal_a4 (d : Contrary T z L g R r) (hZ : center L = ⊥)
    {n : ℕ} (hin : InnerRow n (centralImage L (residual L r)))
    (hout : OuterRow n (centralImage (L.conjBy g) (residual (L.conjBy g) z))) :
    n = 4 ∧ Nonempty (centralImage L (residual L r) ≃* A4) ∧
      residual (L.conjBy g) z = residual L r := by
  change Nonempty _ ∨ _ at hout
  rcases hout with heout | ⟨hn, ⟨eout⟩⟩
  · obtain ⟨eout⟩ := heout
    exact (graph_excluded d hZ hin eout).elim
  have hi : Nonempty (centralImage L (residual L r) ≃* A4) := by
    cases hin with
    | fourRoot _ row =>
      obtain ⟨s⟩ := row
      exact (four_root_excluded d hZ s eout).elim
    | fourJ2 _ row => exact row
    | fiveRoot hn5 _ => omega
    | fiveJ2 hn5 _ => omega
  refine ⟨hn, hi, eq_of_le_of_card_ge d.residual_normal.1 ?_⟩
  obtain ⟨ein⟩ := hi
  have hcIn := Nat.card_congr ((centralImageEquiv
    ((residual_le L r).trans inf_le_left) hZ).trans ein).toEquiv
  have hcOut := Nat.card_congr ((centralImageEquiv
    ((residual_le (L.conjBy g) z).trans inf_le_left)
      (conjugate_center_eq_bot hZ)).trans eout).toEquiv
  exact le_of_eq (hcIn.trans hcOut.symm)

/-- Under the genuine earlier covering and table rows, dimension five is
excluded, using the corrected j₂ extension. No Frattini geometry is needed. -/
theorem five_excluded (d : Contrary T z L g R r) (hZ : center L = ⊥)
    (hin : InnerRow 5 (centralImage L (residual L r)))
    (hout : OuterRow 5 (centralImage (L.conjBy g) (residual (L.conjBy g) z))) : False := by
  have h := (reduce_to_equal_a4 d hZ hin hout).1
  omega

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear
