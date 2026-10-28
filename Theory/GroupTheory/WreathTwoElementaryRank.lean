module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary subgroups of a wreath product with a two-element top

A base subgroup embeds in the product of its two projections. An elementary
subgroup outside the base contains an involution conjugate to the pure swap;
its centralizer is the diagonal base times the swap. These two alternatives
give order bounds `2^(2r)` and `2^(r+1)` from a base two-rank bound `r`.

This is the elementary group calculation underlying the two A₅-factor
normalizer estimates in Aschbacher–Smith D.3.5, printed pp.195–196.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.WreathTwoElementaryRank
abbrev C2 := Multiplicative (ZMod 2)
@[expose] def turn : C2 := Multiplicative.ofAdd 1
theorem turn_ne_one : turn ≠ 1 := by decide
@[simp] theorem turn_inv : turn⁻¹ = turn := by decide
@[simp] theorem turn_mul_self : turn*turn = 1 := by decide
theorem index_cases (i : C2) : i = 1 ∨ i = turn := by revert i; decide
variable {D : Type*} [Group D]
abbrev W (D : Type*) [Group D] := RegularWreathProduct D C2
abbrev base (D : Type*) [Group D] : Subgroup (W D) := RegularWreathProduct.rightHom.ker

@[expose] def baseHom : D × D →* W D where
  toFun p := ⟨fun i => if i = 1 then p.1 else p.2,1⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i; simp
    · rfl
  map_mul' p q := by
    apply RegularWreathProduct.ext
    · funext i
      by_cases hi : i=1 <;> simp [hi]
    · rfl

theorem baseHom_injective : Function.Injective (baseHom : D × D →* W D) := by
  intro p q h
  apply Prod.ext
  · simpa [baseHom] using congrArg (fun w : W D => w.left 1) h
  · simpa [baseHom,turn_ne_one] using congrArg (fun w : W D => w.left turn) h

def baseEquiv : D × D ≃* base D :=
  MulEquiv.ofBijective (baseHom.codRestrict (base D) (fun _ => rfl))
    ⟨fun p q h => baseHom_injective (congrArg Subtype.val h), by
      rintro ⟨w,hw⟩
      refine ⟨(w.left 1,w.left turn),Subtype.ext ?_⟩
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · simp [baseHom]
        · simp [baseHom,turn_ne_one]
      · exact hw.symm⟩

theorem baseEquiv_coe (p : D × D) : (baseEquiv p : W D) = baseHom p := by rfl

private def diagonalPair : D × C2 →* W D where
  toFun a := ⟨fun _ => a.1,a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
private theorem diagonalPair_injective : Function.Injective (diagonalPair : D × C2 →* W D) := by
  intro a b h
  exact Prod.ext (congrArg (fun w => w.left 1) h) (congrArg RegularWreathProduct.right h)
private theorem diagonalPair_range :
    (diagonalPair : D × C2 →* W D).range =
      centralizer ({RegularWreathProduct.inl turn} : Set (W D)) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨a,rfl⟩
    apply RegularWreathProduct.ext
    · funext q; simp [diagonalPair]
    · simp [diagonalPair,mul_comm]
  · intro h
    refine ⟨(x.left 1,x.right),?_⟩
    apply RegularWreathProduct.ext
    · funext q
      rcases index_cases q with rfl | rfl
      · rfl
      · have he := congrArg (fun w => w.left 1) h
        simpa [diagonalPair] using he
    · rfl

def swapCentralizerEquiv :
    centralizer ({RegularWreathProduct.inl turn} : Set (W D)) ≃* D × C2 :=
  (MulEquiv.subgroupCongr diagonalPair_range.symm).trans
    (MonoidHom.ofInjective diagonalPair_injective).symm

theorem outside_involution_conjugate (x : W D)
    (hx : x.right ≠ 1) (hxx : x*x=1) : IsConj (RegularWreathProduct.inl turn) x := by
  have hr : x.right=turn := (index_cases x.right).resolve_left hx
  have he : x.left 1 * x.left turn = 1 := by
    have hh := congrArg (fun w : W D => w.left 1) hxx
    simpa [hr] using hh
  have hl : (x.left 1)⁻¹=x.left turn := (inv_eq_iff_mul_eq_one).mpr he
  let a : W D := ⟨fun i=>if i=1 then x.left 1 else 1,1⟩
  apply isConj_iff.mpr
  refine ⟨a,?_⟩
  apply RegularWreathProduct.ext
  · funext q
    rcases index_cases q with rfl | rfl
    · simp [a,turn_ne_one]
    · simp [a,turn_ne_one,hl]
  · simpa [a] using hr.symm

theorem outsideCentralizerEquiv (x : W D) (hx : x.right ≠ 1) (hxx : x*x=1) :
    Nonempty (centralizer ({x} : Set (W D)) ≃* D × C2) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (outside_involution_conjugate x hx hxx)
  have he : (MulAut.conj g) (RegularWreathProduct.inl turn) = x := hg
  exact ⟨(MulEquiv.subgroupCongr (congrArg (fun t : W D => centralizer ({t} : Set (W D))) he.symm)).trans
    ((Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.conj g) (RegularWreathProduct.inl turn)).symm.trans swapCentralizerEquiv)⟩

theorem c2_rank_le : primeRank 2 C2 ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le C2).mpr
  intro E _
  exact (card_le_card_group E).trans_eq (by simp [C2,Nat.card_eq_fintype_card])

variable [Finite D]
theorem elementary_card_le_of_le_base (E : Subgroup (W D)) (hE : IsElementaryAbelian 2 E)
    (hbase : E ≤ base D) {r : ℕ} (hr : primeRank 2 D ≤ r) : Nat.card E ≤ 2^(2*r) := by
  let f := baseEquiv.symm.toMonoidHom.comp (inclusion hbase)
  have hi : Function.Injective f := baseEquiv.symm.injective.comp (inclusion_injective hbase)
  have hbound := primeRank_le_of_injective 2 f hi
  rw [primeRank_prod_eq_add] at hbound
  have he : primeRank 2 E ≤ 2*r := by omega
  let := hE
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype Subtype.val_injective
  simpa only [card_top] using (primeRank_le_iff_elementary_card_le E).mp he ⊤ ht

theorem elementary_card_le_of_not_le_base (E : Subgroup (W D)) (hE : IsElementaryAbelian 2 E)
    (hbase : ¬ E ≤ base D) {r : ℕ} (hr : primeRank 2 D ≤ r) : Nat.card E ≤ 2^(r+1) := by
  obtain ⟨x,hx,hxb⟩ := SetLike.not_le_iff_exists.mp hbase
  have hxx : x*x=1 := by
    let := hE
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  obtain ⟨e⟩ := outsideCentralizerEquiv x hxb hxx
  have hEC : E ≤ centralizer ({x} : Set (W D)) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.is_comm.comm (⟨y,hy⟩ : E) ⟨x,hx⟩))
  let f := e.toMonoidHom.comp (inclusion hEC)
  have hi : Function.Injective f := e.injective.comp (inclusion_injective hEC)
  have hbound := primeRank_le_of_injective 2 f hi
  rw [primeRank_prod_eq_add] at hbound
  have hc := c2_rank_le
  have he : primeRank 2 E ≤ r+1 := by omega
  let := hE
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype Subtype.val_injective
  simpa only [card_top] using (primeRank_le_iff_elementary_card_le E).mp he ⊤ ht

theorem rank_bound {r : ℕ} (hr : primeRank 2 D ≤ r) (hrpos : 0 < r) :
    primeRank 2 (W D) ≤ 2*r := by
  apply (primeRank_le_iff_elementary_card_le (W D)).mpr
  intro E hE
  by_cases hb : E ≤ base D
  · exact elementary_card_le_of_le_base E hE hb hr
  · exact (elementary_card_le_of_not_le_base E hE hb hr).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
end Theory.GroupTheory.WreathTwoElementaryRank
