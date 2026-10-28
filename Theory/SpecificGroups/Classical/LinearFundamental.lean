module

public import Theory.SpecificGroups.SL2.DefiningRank
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Theory.GroupTheory.PResidual.PrimeTo


/-!
# Fundamental and complementary blocks in special linear groups

Block diagonal special-linear matrices give commuting fundamental and
complementary subgroups. An identity block proves that each factor remains
faithful in the quotient by the full center. The joint map has exactly the
common-scalar kernel, and an off-block transvection proves properness.
In odd characteristic, commuting with minus one on the fundamental two-space
forces block diagonality; commuting with its transvections makes its block
scalar. This calculates the full centralizer in the covering SL group.

The additive row group on a complementary space embeds in the projective
centralizer and, in characteristic p, in its literal O^{p′} residual. Its
cardinality gives a defining-characteristic rank bound. In particular, over
a field of order p^e, residual rank at most one forces the ambient degree to
be three, or four with e = 1. This rank argument does not assume a residual
identification or a classification result.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma A.2.17, printed pp.38–39. The elementary
matrix constructions here use the existing Mathlib matrix API directly.
-/

public section

open Matrix
namespace Matrix.SpecialLinearGroup.LinearFundamental
variable {F : Type*} [Field F]
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

@[expose] noncomputable def block : SpecialLinearGroup m F × SpecialLinearGroup n F →*
    SpecialLinearGroup (m ⊕ n) F where
  toFun g := ⟨fromBlocks g.1.val 0 0 g.2.val, by
    rw [det_fromBlocks_zero₂₁, g.1.property, g.2.property, one_mul]⟩
  map_one' := Subtype.ext fromBlocks_one
  map_mul' g h := by
    apply Subtype.ext
    change fromBlocks (g.1.val * h.1.val) 0 0 (g.2.val * h.2.val) =
      fromBlocks g.1.val 0 0 g.2.val * fromBlocks h.1.val 0 0 h.2.val
    simp [fromBlocks_multiply]

@[simp] theorem block_coe (a : SpecialLinearGroup m F × SpecialLinearGroup n F) :
    (block a).val = fromBlocks a.1.val 0 0 a.2.val := rfl

theorem block_injective : Function.Injective (block (m := m) (n := n) (F := F)) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Prod.ext (Subtype.ext (congrArg toBlocks₁₁ h'))
    (Subtype.ext (congrArg toBlocks₂₂ h'))

@[expose] noncomputable def left : SpecialLinearGroup m F →* SpecialLinearGroup (m ⊕ n) F :=
  block.comp (MonoidHom.inl _ _)
@[expose] noncomputable def right : SpecialLinearGroup n F →* SpecialLinearGroup (m ⊕ n) F :=
  block.comp (MonoidHom.inr _ _)

@[expose] noncomputable def projectLeft : SpecialLinearGroup m F →*
    (SpecialLinearGroup (m ⊕ n) F ⧸ Subgroup.center _) :=
  (QuotientGroup.mk' _).comp left
@[expose] noncomputable def projectRight : SpecialLinearGroup n F →*
    (SpecialLinearGroup (m ⊕ n) F ⧸ Subgroup.center _) :=
  (QuotientGroup.mk' _).comp right

theorem projectLeft_injective [Nonempty n] :
    Function.Injective (projectLeft (m := m) (n := n) (F := F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hc : left (n := n) a ∈ Subgroup.center _ :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨j⟩ := ‹Nonempty n›
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hc (Sum.inr j)
  have hs' : (1 : Matrix (m ⊕ n) (m ⊕ n) F) = (left a).val := by
    simpa [left] using hs
  apply Subtype.ext
  ext i k
  have hh := congrArg (fun M => M (Sum.inl i) (Sum.inl k)) hs'
  simpa [left, Matrix.one_apply] using hh.symm

theorem projectRight_injective [Nonempty m] :
    Function.Injective (projectRight (m := m) (n := n) (F := F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hc : right (m := m) a ∈ Subgroup.center _ :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨j⟩ := ‹Nonempty m›
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hc (Sum.inl j)
  have hs' : (1 : Matrix (m ⊕ n) (m ⊕ n) F) = (right a).val := by
    simpa [right] using hs
  apply Subtype.ext
  ext i k
  have hh := congrArg (fun M => M (Sum.inr i) (Sum.inr k)) hs'
  simpa [right, Matrix.one_apply] using hh.symm

theorem left_right_commute (a : SpecialLinearGroup m F) (b : SpecialLinearGroup n F) :
    Commute (left a) (right b) := by
  change block (a, 1) * block (1, b) = block (1, b) * block (a, 1)
  rw [← map_mul, ← map_mul]
  simp

theorem projectLeft_projectRight_commute (a : SpecialLinearGroup m F)
    (b : SpecialLinearGroup n F) : Commute (projectLeft a) (projectRight b) :=
  (left_right_commute a b).map (QuotientGroup.mk' _)

@[expose] noncomputable def reindex (e : m ≃ n) : SpecialLinearGroup m F ≃*
    SpecialLinearGroup n F where
  toFun g := ⟨Matrix.reindex e e g.val, by rw [det_reindex_self]; exact g.property⟩
  invFun g := ⟨Matrix.reindex e.symm e.symm g.val, by
    rw [det_reindex_self]; exact g.property⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.reindex_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.reindex_apply]
  map_mul' g h := by
    apply Subtype.ext
    exact (reindexRingEquiv F e).map_mul g.val h.val

@[expose] noncomputable def rowHom (d : ℕ) : Multiplicative (Fin d → F) →*
    SpecialLinearGroup (Fin 1 ⊕ Fin d) F where
  toFun a := ⟨fromBlocks 1 (Matrix.of (fun _ j => a.toAdd j)) 0 1, by
    simp⟩
  map_one' := by
    apply Subtype.ext
    exact fromBlocks_one
  map_mul' a b := by
    apply Subtype.ext
    change fromBlocks 1 (Matrix.of (fun _ j => a.toAdd j + b.toAdd j)) 0 1 =
      fromBlocks 1 (Matrix.of (fun _ j => a.toAdd j)) 0 1 *
      fromBlocks 1 (Matrix.of (fun _ j => b.toAdd j)) 0 1
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]
    congr 1
    ext i j
    exact add_comm _ _

theorem rowHom_injective (d : ℕ) : Function.Injective (rowHom (F := F) d) := by
  intro a b h
  change a.toAdd = b.toAdd
  funext j
  exact congrArg (fun g : SpecialLinearGroup (Fin 1 ⊕ Fin d) F =>
    g.val (Sum.inl 0) (Sum.inr j)) h

theorem row_rank [Finite F] {p e d : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p ^ e) :
    e * d ≤ primeRank p (SpecialLinearGroup (Fin (1 + d)) F) := by
  let f := (reindex (F := F) (finSumFinEquiv (m := 1) (n := d))).toMonoidHom.comp
    (rowHom (F := F) d)
  have hp : ∀ a : Multiplicative (Fin d → F), a ^ p = 1 := by
    intro a
    change p • a.toAdd = 0
    ext j
    simp [nsmul_eq_mul]
  have hc : Nat.card (Multiplicative (Fin d → F)) = p ^ (e * d) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hcard, pow_mul]
  exact primeRank_ge_of_elementary_embedding hp hc f
    ((reindex finSumFinEquiv).injective.comp (rowHom_injective d))

@[expose] noncomputable def complementCentralizer : SpecialLinearGroup n F →*
    Subgroup.centralizer ((projectLeft (m := m) (n := n) (F := F)).range.carrier) :=
  (projectRight (m := m)).codRestrict _ fun b => by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact (projectLeft_projectRight_commute a b).eq

theorem complementCentralizer_injective [Nonempty m] :
    Function.Injective (complementCentralizer (m := m) (n := n) (F := F)) := by
  intro a b h
  exact projectRight_injective (congrArg Subtype.val h)

@[expose] noncomputable def residualRow (d p : ℕ) [CharP F p] :
    Multiplicative (Fin d → F) →*
      Subgroup.primeToResidual p
        (Subgroup.centralizer ((projectLeft (m := Fin 2) (n := Fin (1 + d))
          (F := F)).range.carrier)) :=
  let f := (complementCentralizer (m := Fin 2)).comp
    ((reindex finSumFinEquiv).toMonoidHom.comp (rowHom (F := F) d))
  f.codRestrict _ fun a => by
    apply Subgroup.mem_primeToResidual_of_pow (n := 1)
    rw [pow_one, ← map_pow]
    have ha : a ^ p = 1 := by
      change p • a.toAdd = 0
      ext j
      simp [nsmul_eq_mul]
    rw [ha, map_one]

theorem residualRow_injective (d p : ℕ) [CharP F p] :
    Function.Injective (residualRow (F := F) d p) := by
  intro a b h
  apply rowHom_injective d
  apply (reindex finSumFinEquiv).injective
  apply complementCentralizer_injective (m := Fin 2)
  exact congrArg Subtype.val h

theorem residual_row_rank [Finite F] {p e d : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p ^ e) :
    e * d ≤ primeRank p (Subgroup.primeToResidual p
      (Subgroup.centralizer ((projectLeft (m := Fin 2) (n := Fin (1 + d))
        (F := F)).range.carrier))) := by
  have hp : ∀ a : Multiplicative (Fin d → F), a ^ p = 1 := by
    intro a
    change p • a.toAdd = 0
    ext j
    simp [nsmul_eq_mul]
  have hc : Nat.card (Multiplicative (Fin d → F)) = p ^ (e * d) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hcard, pow_mul]
  exact primeRank_ge_of_elementary_embedding hp hc (residualRow d p)
    (residualRow_injective d p)


private theorem matrix_eq_zero_of_neg_eq {a b : Type*} (hF : (2 : F) ≠ 0)
    (M : Matrix a b F) (hM : -M = M) : M = 0 := by
  ext i j
  have h := congrArg (fun M : Matrix a b F => M i j) hM
  have hz : (2 : F) * M i j = 0 := by
    rw [two_mul]
    exact neg_eq_iff_add_eq_zero.mp h
  exact (mul_eq_zero.mp hz).resolve_left hF

/-- The full centralizer in the covering special linear group consists of a
scalar on the fundamental two-space and an arbitrary complementary block.
The determinant condition is already part of membership in SL. -/
theorem mem_coverCentralizer_iff (hF : (2 : F) ≠ 0)
    (g : SpecialLinearGroup (Fin 2 ⊕ n) F) :
    g ∈ Subgroup.centralizer (left (m := Fin 2) (n := n) (F := F)).range.carrier ↔
      ∃ (c : F) (D : Matrix n n F), g.val = fromBlocks (scalar (Fin 2) c) 0 0 D := by
  let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  constructor
  · intro hg
    have hz := congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hg)
      (left (-1)) ⟨-1, rfl⟩)
    change fromBlocks (-1 : Matrix (Fin 2) (Fin 2) F) 0 0 1 * g.val =
      g.val * fromBlocks (-1) 0 0 1 at hz
    rw [← fromBlocks_toBlocks g.val] at hz
    simp only [fromBlocks_multiply, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, Matrix.neg_mul, Matrix.one_mul, fromBlocks_inj] at hz
    have h12 := matrix_eq_zero_of_neg_eq hF _ hz.2.1
    have h21 := matrix_eq_zero_of_neg_eq hF _ hz.2.2.1.symm
    have he : g.val = fromBlocks g.val.toBlocks₁₁ 0 0 g.val.toBlocks₂₂ := by
      simpa only [h12, h21] using (fromBlocks_toBlocks g.val).symm
    obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_transvectionStruct
      (M := g.val.toBlocks₁₁) (fun t => by
        have ht := congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hg)
          (left t.toSpecialLinearGroup) ⟨t.toSpecialLinearGroup, rfl⟩)
        change fromBlocks t.toMatrix 0 0 1 * g.val =
          g.val * fromBlocks t.toMatrix 0 0 1 at ht
        rw [he] at ht
        have hh := congrArg toBlocks₁₁ ht
        change t.toMatrix * g.val.toBlocks₁₁ = g.val.toBlocks₁₁ * t.toMatrix
        simpa [fromBlocks_multiply] using hh)
    exact ⟨c, g.val.toBlocks₂₂, hc ▸ he⟩
  · rintro ⟨c, D, hg⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    apply Subtype.ext
    change fromBlocks a.val 0 0 1 * g.val = g.val * fromBlocks a.val 0 0 1
    rw [hg]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    congr 1
    exact (scalar_commute c (Commute.all c) a.val).symm.eq


@[expose] noncomputable def projectiveReindex (e : m ≃ n) :
    ProjectiveSpecialLinearGroup m F ≃* ProjectiveSpecialLinearGroup n F :=
  let f := reindex (F := F) e
  QuotientGroup.congr _ _ f (by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (Subgroup.centerCongr f ⟨a, ha⟩).property
    · intro hx
      exact ⟨f.symm x, ((Subgroup.centerCongr f).symm ⟨x, hx⟩).property,
        f.apply_symm_apply x⟩)

theorem projectBlock_eq_one_iff [Nonempty m]
    (a : SpecialLinearGroup m F) (b : SpecialLinearGroup n F) :
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (m ⊕ n) F)) (block (a, b)) = 1 ↔
      ∃ c : F, a.val = scalar m c ∧ b.val = scalar n c := by
  constructor
  · intro hh
    have h := (QuotientGroup.eq_one_iff _).mp hh
    obtain ⟨c, _, hc⟩ := SpecialLinearGroup.mem_center_iff.mp h
    refine ⟨c, ?_, ?_⟩
    · ext i j
      have h := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hc
      simpa [scalar_apply, diagonal_apply] using h.symm
    · ext i j
      have h := congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hc
      simpa [scalar_apply, diagonal_apply] using h.symm
  · rintro ⟨c, ha, hb⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    have hc : (block (a, b)).val = scalar (m ⊕ n) c := by
      rw [block_coe, ha, hb]
      ext i j
      cases i <;> cases j <;> simp [scalar_apply, diagonal_apply]
    rw [SpecialLinearGroup.mem_center_iff]
    refine ⟨c, ?_, hc.symm⟩
    have hd := (block (a, b)).property
    rw [hc] at hd
    simpa using hd

theorem linear_dimension_restriction [Finite F] {p e d : ℕ}
    [Fact p.Prime] [CharP F p] (hcard : Nat.card F = p ^ e) (he : 0 < e)
    (hr : primeRank p (Subgroup.primeToResidual p
      (Subgroup.centralizer ((projectLeft (m := Fin 2) (n := Fin (1 + d))
        (F := F)).range.carrier))) ≤ 1) :
    d = 0 ∨ d = 1 ∧ e = 1 := by
  have h := (residual_row_rank hcard).trans hr
  have hd : d ≤ 1 := by nlinarith
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exact Or.inl h0
  · have hd1 : d = 1 := by omega
    right
    refine ⟨hd1, ?_⟩
    rw [hd1, mul_one] at h
    omega

/-- An off-diagonal transvection is outside the fundamental block even after
passing to the central quotient. -/
theorem projectLeft_range_ne_top [Nonempty m] [Nonempty n] :
    (projectLeft (m := m) (n := n) (F := F)).range ≠ ⊤ := by
  classical
  obtain ⟨i⟩ := ‹Nonempty m›
  obtain ⟨j⟩ := ‹Nonempty n›
  let t : SpecialLinearGroup (m ⊕ n) F :=
    SpecialLinearGroup.transvection (i := Sum.inr j) (j := Sum.inl i) (by simp) 1
  intro ht
  have htmem : QuotientGroup.mk' (Subgroup.center _) t ∈
      (projectLeft (m := m) (n := n) (F := F)).range := ht ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := htmem
  have hz : t / left a ∈ Subgroup.center _ :=
    QuotientGroup.eq_iff_div_mem.mp ha.symm
  obtain ⟨c, _, hc⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  have hm : scalar (m ⊕ n) c * (left a).val = t.val := by
    rw [hc]
    exact congrArg Subtype.val (div_mul_cancel t (left a))
  have he := congrArg (fun M => M (Sum.inr j) (Sum.inl i)) hm
  simp [scalar_apply, diagonal_mul, left, t, SpecialLinearGroup.transvection_coe] at he

end Matrix.SpecialLinearGroup.LinearFundamental
