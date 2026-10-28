module
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.Representation.BinaryOffender.GeneratingFiltration
public import CFSG.Quasithin.ChapterD.Section01.RankBounds

/-!
# Chief-series and rank filtrations for D.1

The public imports construct an actual H-chief series on a finite normal
p-subgroup, its elementary abelian irreducible quotient conjugation actions,
and the zero/one/multiple noncentral-factor alternatives. For elementary
abelian U, the literal chief quotients have equivariant linear coordinates.

This module applies fixed-codimension superadditivity to the count of those
noncentral factors, including equality on each factor. It also applies the
generating filtration to B-invariant subspaces of Additive U, identifies its
terminal kernel with C_B(U), and retains equality for any generator placed
first. The final application combines both estimates with the existing
numerical RankBounds theorem. Its explicit additional inputs are precisely
the local ratio estimates, the replacement estimate and the per-factor lower
bound; constructing those source-specific inputs belongs to D.1.3's owner.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.1.3(a)--(n), printed pp.173--175 (1 March 2004 manuscript).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD
open NoncentralChiefRefinement Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
variable {H : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [IsElementaryAbelian 2 U]

/-- Equation (n): the number is the count of actual noncentral factors of the chosen series. -/
theorem qrc_chief_factor_lower [Finite H] (s : SeriesOn U) (A : Subgroup H) (a : ℝ)
    (hlower : ∀ i, ¬ s.Central i → a ≤ fixedCodim (s.factorRepresentation i) A) :
    (s.noncentralCount : ℝ) * a ≤ fixedCodim (normalRepresentation U) A := by
  classical
  let I := Finset.univ.filter (fun i : Fin s.series.length => ¬ s.Central i)
  have hc : I.card = s.noncentralCount := by
    simp only [I, SeriesOn.noncentralCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hlow : (I.card : ℝ) * a ≤ ∑ i ∈ I, (fixedCodim (s.factorRepresentation i) A : ℝ) := by
    calc
      (I.card : ℝ) * a = ∑ _i ∈ I, a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hlower i (Finset.mem_filter.mp hi).2)
  have hsub : (∑ i ∈ I, (fixedCodim (s.factorRepresentation i) A : ℝ)) ≤
      ∑ i : Fin s.series.length, (fixedCodim (s.factorRepresentation i) A : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.cast_nonneg _)
  have hsum : (∑ i : Fin s.series.length, (fixedCodim (s.factorRepresentation i) A : ℝ)) ≤
      fixedCodim (normalRepresentation U) A := by
    exact_mod_cast s.sum_factor_fixedCodim_le A
  rw [hc] at hlow
  exact hlow.trans (hsub.trans hsum)

/-- Equality in the chief-factor sum forces equality on every noncentral factor. -/
theorem qrc_chief_factor_equality [Finite H] (s : SeriesOn U) (A : Subgroup H) (a : ℝ)
    (hlower : ∀ i, ¬ s.Central i → a ≤ fixedCodim (s.factorRepresentation i) A)
    (heq : (fixedCodim (normalRepresentation U) A : ℝ) = (s.noncentralCount : ℝ) * a) :
    ∀ i, ¬ s.Central i → (fixedCodim (s.factorRepresentation i) A : ℝ) = a := by
  classical
  let I := Finset.univ.filter (fun i : Fin s.series.length => ¬ s.Central i)
  have hc : I.card = s.noncentralCount := by
    simp only [I, SeriesOn.noncentralCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hupper : (∑ i ∈ I, (fixedCodim (s.factorRepresentation i) A : ℝ)) ≤
      (I.card : ℝ) * a := by
    calc
      _ ≤ ∑ i : Fin s.series.length, (fixedCodim (s.factorRepresentation i) A : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ fixedCodim (normalRepresentation U) A := by exact_mod_cast s.sum_factor_fixedCodim_le A
      _ = _ := by rw [heq, hc]
  intro i hi
  exact qrc_factor_ranks_eq I (fun i => (fixedCodim (s.factorRepresentation i) A : ℝ)) a
    (fun j hj => hlower j (Finset.mem_filter.mp hj).2) hupper i (Finset.mem_filter.mpr ⟨by simp, hi⟩)

/-- The original acting subgroup's literal kernel on U. -/
noncomputable def qrcActionKernel (B : Subgroup H) : Subgroup B :=
  ((normalRepresentation U).comp B.subtype).ker

instance qrcActionKernel_normal (B : Subgroup H) : (qrcActionKernel U B).Normal :=
  inferInstanceAs (((normalRepresentation U).comp B.subtype).ker).Normal

/-- This kernel is C_B(U), with B retained as the quotient's ambient group. -/
theorem qrcActionKernel_eq_centralizer (B : Subgroup H) :
    qrcActionKernel U B = (centralizer (U : Set H)).subgroupOf B := by
  ext b
  constructor
  · intro hb u hu
    have he := congrArg (fun f : Module.End (ZMod 2) (Additive U) =>
      ((f (Additive.ofMul ⟨u, hu⟩)).toMul : H)) (MonoidHom.mem_ker.mp hb)
    change (b : H) * u * (b : H)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hb
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    change (b : H) * (u.toMul : H) * (b : H)⁻¹ = (u.toMul : H)
    have he : (u.toMul : H) * (b : H) = (b : H) * (u.toMul : H) := hb u.toMul u.toMul.property
    rw [← he, mul_inv_cancel_right]

private theorem qrcActionKernel_eq_subspaceKernel (B : Subgroup H) :
    qrcActionKernel U B = subspaceKernel ((normalRepresentation U).comp B.subtype) ⊤ ⊤ := by
  ext b
  constructor
  · intro hb
    refine ⟨trivial, fun v _ => ?_⟩
    exact congrArg (fun f : Module.End (ZMod 2) (Additive U) => f v) (MonoidHom.mem_ker.mp hb)
  · rintro ⟨_, hb⟩
    apply MonoidHom.mem_ker.mpr
    exact LinearMap.ext (fun v => hb v trivial)

private theorem qrc_fixedCodim_restrict_top (B : Subgroup H) :
    fixedCodim ((normalRepresentation U).comp B.subtype) ⊤ =
      fixedCodim (normalRepresentation U) B := by
  have he : fixedSpace ((normalRepresentation U).comp B.subtype) ⊤ =
      fixedSpace (normalRepresentation U) B := by
    ext v
    constructor
    · intro hv b
      exact hv ⟨b, trivial⟩
    · intro hv b
      exact hv b
  unfold fixedCodim
  rw [he]

/-- D.1.3(j), for B-invariant generators of U. The actor rank is that of the
literal quotient B/C_B(U), and local denominators are the successive pointwise kernels. -/
theorem qrc_generating_bound [Finite H] (B : Subgroup H) [IsElementaryAbelian 2 B]
    (W : ℕ → Subrepresentation ((normalRepresentation U).comp B.subtype))
    (q : ℝ) (n : ℕ)
    (hgen : generatingSpan ((normalRepresentation U).comp B.subtype) W n = ⊤)
    (hlocal : ∀ i < n, q * (Nat.log 2
      ((generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ (i + 1)).relIndex
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i)) : ℝ) ≤
      fixedCodim (W i).toRepresentation
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i)) :
    q * (Nat.log 2 (Nat.card (B ⧸ qrcActionKernel U B)) : ℝ) ≤
      fixedCodim (normalRepresentation U) B := by
  let _ : IsElementaryAbelian 2 (⊤ : Subgroup B) :=
    IsElementaryAbelian.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.surjective
  have h := (generating_quotient_bound ((normalRepresentation U).comp B.subtype)
    W ⊤ q n hgen hlocal).1
  rw [← qrcActionKernel_eq_subspaceKernel U B, Subgroup.relIndex_top_right,
    Subgroup.index_eq_card, qrc_fixedCodim_restrict_top] at h
  exact h

/-- Equality in (j) gives equality for any chosen generator placed first.
In particular this applies to every nontrivially acted-on conjugate of V. -/
theorem qrc_generating_first_equality [Finite H] (B : Subgroup H) [IsElementaryAbelian 2 B]
    (W : ℕ → Subrepresentation ((normalRepresentation U).comp B.subtype))
    (q : ℝ) (n : ℕ) (hn : 0 < n)
    (hgen : generatingSpan ((normalRepresentation U).comp B.subtype) W n = ⊤)
    (hlocal : ∀ i < n, q * (Nat.log 2
      ((generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ (i + 1)).relIndex
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i)) : ℝ) ≤
      fixedCodim (W i).toRepresentation
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i))
    (heq : (fixedCodim (normalRepresentation U) B : ℝ) =
      q * (Nat.log 2 (Nat.card (B ⧸ qrcActionKernel U B)) : ℝ)) :
    (fixedCodim (W 0).toRepresentation ⊤ : ℝ) = q * (Nat.log 2
      (subspaceKernel ((normalRepresentation U).comp B.subtype) (W 0).toSubmodule ⊤).index : ℝ) := by
  let _ : IsElementaryAbelian 2 (⊤ : Subgroup B) :=
    IsElementaryAbelian.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.surjective
  have heq' : (fixedCodim ((normalRepresentation U).comp B.subtype) ⊤ : ℝ) =
      q * (Nat.log 2 ((subspaceKernel ((normalRepresentation U).comp B.subtype) ⊤ ⊤).relIndex ⊤) : ℝ) := by
    rwa [← qrcActionKernel_eq_subspaceKernel U B, Subgroup.relIndex_top_right,
      Subgroup.index_eq_card, qrc_fixedCodim_restrict_top]
  simpa only [Subgroup.relIndex_top_right] using generating_quotient_first_equality
    ((normalRepresentation U).comp B.subtype) W ⊤ q n hn hgen hlocal heq'

/-- Both actual filtrations feed the existing numerical elimination. The remaining
source inputs are the local quadratic-ratio estimates, replacement, and the
lower estimate on each noncentral chief factor. -/
theorem qrc_bound_from_filtrations [Finite H] (s : SeriesOn U) (A B : Subgroup H)
    [IsElementaryAbelian 2 B] (hBA : B ≤ A)
    (W : ℕ → Subrepresentation ((normalRepresentation U).comp B.subtype))
    (q a : ℝ) (n : ℕ) (hq : 1 < q) (ha : 0 < a) (hc : 1 < s.noncentralCount)
    (hgen : generatingSpan ((normalRepresentation U).comp B.subtype) W n = ⊤)
    (hlocal : ∀ i < n, q * (Nat.log 2
      ((generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ (i + 1)).relIndex
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i)) : ℝ) ≤
      fixedCodim (W i).toRepresentation
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i))
    (hreplacement : (fixedCodim (normalRepresentation U) A : ℝ) ≤
      a + (Nat.log 2 (Nat.card (B ⧸ qrcActionKernel U B)) : ℝ))
    (hlower : ∀ i, ¬ s.Central i → a ≤ fixedCodim (s.factorRepresentation i) A) : q ≤ 2 := by
  have hfix : fixedSpace (normalRepresentation U) A ≤ fixedSpace (normalRepresentation U) B := by
    intro v hv b
    exact hv ⟨b, hBA b.property⟩
  have hdim := Submodule.finrank_mono hfix
  have hA := fixedCodim_add_finrank (normalRepresentation U) A
  have hB := fixedCodim_add_finrank (normalRepresentation U) B
  have hmono : (fixedCodim (normalRepresentation U) B : ℝ) ≤
      fixedCodim (normalRepresentation U) A := by
    exact_mod_cast (show fixedCodim (normalRepresentation U) B ≤
      fixedCodim (normalRepresentation U) A by omega)
  exact qrc_rank_bound hq ha (by exact_mod_cast hc) hreplacement
    ((qrc_generating_bound U B W q n hgen hlocal).trans hmono)
    (qrc_chief_factor_lower U s A a hlower)

end CFSG.Quasithin.ChapterD
