module

public import CFSG.Quasithin.ChapterA.Section01.PStructure
public import Theory.GroupAction.PerfectFrattiniAction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.SpecificGroups.GL2.ThreeSolvable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The actual perfect rank-two quotient action

For the p-group in A.1.29, A.1.24 bounds the Frattini quotient by p².
The induced conjugation action of H embeds its quotient by the relative
centralizer into GL₂(p), and perfectness forces determinant one. Burnside's
Frattini kernel theorem makes this action nontrivial when [P,H] is nontrivial.
Solvability of GL₂(3) excludes the small prime before any cover theorem is used.
No ambient normality assumption is placed on H.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.29, printed p.27. Recognition of the resulting perfect SL₂ subgroup is
separate from this reduction.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterA.RankActions
variable {G : Type*} [Group G] (P H : Subgroup G) [P.Normal]

/-- The actual conjugation action of H on the Frattini quotient of normal P. -/
@[expose] public def frattiniAction : H →* MulAut (P ⧸ frattini P) :=
  (quotientAut (frattini P)).comp ((MulAut.conjNormal : G →* MulAut P).comp H.subtype)
/-- The relative centralizer in H, defined as the kernel of its actual action. -/
public abbrev frattiniCentralizer : Subgroup H := (frattiniAction P H).ker

/-- Membership means fixing every coset of the specified Frattini quotient. -/
public theorem mem_frattiniCentralizer_iff (h : H) :
    h ∈ frattiniCentralizer P H ↔
      ∀ x : P, QuotientGroup.mk' (frattini P)
        ((MulAut.conjNormal (h : G)) x) = QuotientGroup.mk' (frattini P) x := by
  change frattiniAction P H h = 1 ↔ _
  constructor
  · intro hh x
    have hx := DFunLike.congr_fun hh (QuotientGroup.mk' (frattini P) x)
    simpa only [frattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
      MulAut.one_apply, Subgroup.coe_subtype] using hx
  · intro hh
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) x
    simpa only [frattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
      MulAut.one_apply, Subgroup.coe_subtype] using hh x

/-- Perfectness and the nontrivial commutator detect the Frattini action. -/
public theorem frattiniAction_ne_one [Finite G] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥) : frattiniAction P H ≠ 1 := by
  apply MonoidHom.frattini_comp_ne_one_of_isPerfect hP
  intro h
  apply hPH
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro h' hh x hx
  have he := DFunLike.congr_fun h ⟨h', hh⟩
  have hx' := congrArg (fun a : MulAut P => (a ⟨x, hx⟩ : G)) he
  change h' * x * h'⁻¹ = x at hx'
  exact (mul_inv_eq_iff_eq_mul.mp hx').symm

/-- The quotient by the relative centralizer is nontrivial. -/
public theorem frattiniQuotient_nontrivial [Finite G] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥) :
    Nontrivial (H ⧸ frattiniCentralizer P H) := by
  have hn : (frattiniAction P H).range ≠ ⊥ := by
    intro hz
    apply frattiniAction_ne_one P H hP hPH
    apply MonoidHom.ext
    intro x
    have hx : frattiniAction P H x ∈ (frattiniAction P H).range := ⟨x, rfl⟩
    rwa [hz, mem_bot] at hx
  let : Nontrivial (frattiniAction P H).range := (nontrivial_iff_ne_bot _).mpr hn
  exact (QuotientGroup.quotientKerEquivRange (frattiniAction P H)).surjective.nontrivial

omit [P.Normal] in
/-- A.1.24 bounds the order of the actual Frattini quotient by p². -/
public theorem frattini_card_le [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hP : IsPGroup p P) (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2) :
    Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
  rcases lemma_A_1_24 hp hP ho hc hr with ⟨hc, _⟩ | ⟨hc, he, _⟩
  · exact hc ▸ Nat.le_of_dvd (Nat.card_pos (α := P))
      (card_quotient_dvd_card (frattini P))
  · let : IsExtraspecial p P := he
    have hphi : Nat.card (frattini P) = p := by
      rw [IsExtraspecial.frattini_eq_center (p := p), IsExtraspecial.center_order_p p P]
    have hprod := (frattini P).index_mul_card
    change Nat.card (P ⧸ frattini P) * Nat.card (frattini P) = Nat.card P at hprod
    rw [hphi, hc, show 3 = 2 + 1 from rfl, pow_succ] at hprod
    exact (mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hprod).le

/-- The quotient action has a faithful two-dimensional matrix representation. -/
public theorem quotient_embeds_GL [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hP : IsPGroup p P) (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2) :
    ∃ f : (H ⧸ frattiniCentralizer P H) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod p), Function.Injective f := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨j, hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (P ⧸ frattini P) (frattini_card_le P hp hP ho hc hr)
  let e := QuotientGroup.quotientKerEquivRange (frattiniAction P H)
  exact ⟨j.comp ((frattiniAction P H).range.subtype.comp e.toMonoidHom),
    hj.comp (Subtype.val_injective.comp e.injective)⟩

/-- Perfectness forces determinant one in the faithful quotient action. -/
public theorem quotient_embeds_SL [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hP : IsPGroup p P) (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2)
    [Group.IsPerfect H] :
    ∃ f : (H ⧸ frattiniCentralizer P H) →*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p), Function.Injective f := by
  obtain ⟨f, hf⟩ := quotient_embeds_GL P H hp hP ho hc hr
  have hd (x : H ⧸ frattiniCentralizer P H) : (f x).det = 1 :=
    Abelianization.commutator_subset_ker (Matrix.GeneralLinearGroup.det.comp f)
      Group.IsPerfect.mem_commutator
  let g : (H ⧸ frattiniCentralizer P H) →*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun x => ⟨(f x : Matrix (Fin 2) (Fin 2) (ZMod p)), congrArg Units.val (hd x)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; exact congrArg Units.val (f.map_mul x y) }
  refine ⟨g, ?_⟩
  intro x y hxy
  apply hf
  exact Units.ext (congrArg Subtype.val hxy)

/-- The p = 3 case is impossible: GL₂(3) is solvable. -/
public theorem three_lt_of_perfect_action [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hP : IsPGroup p P) (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥) : 3 < p := by
  have hpge := (Fact.out : p.Prime).two_le
  suffices p ≠ 3 by omega
  rintro rfl
  obtain ⟨f, hf⟩ := quotient_embeds_GL P H hp hP ho hc hr
  let : Nontrivial (H ⧸ frattiniCentralizer P H) := frattiniQuotient_nontrivial P H hP hPH
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    Matrix.GeneralLinearGroup.three_isSolvable
  exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_isSolvable_injective hf)
end CFSG.Quasithin.ChapterA.RankActions
