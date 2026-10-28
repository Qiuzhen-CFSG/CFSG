module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.Fusion
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Diagonal involutions in the crossing product

Multiplication identifies K × Kˣ with the actual commuting join. Separate
involution fusion in its two factors puts every nontrivial diagonal
involution in the original z-class. The source nonfusion of t and z then
excludes that class from tᴳ. Thus every conjugate of t lying in KKˣ lies
in one factor; the cases outside the product remain separate obligations.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.566.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]
namespace Incoming
variable (d : Incoming κ G p)

/-- A product of nontrivial involutions in both factors is in the z-class. -/
theorem diagonal_involution_conjugate {a b : G}
    (ha : a ∈ d.K) (hb : b ∈ conjugate d.K d.x)
    (hoa : orderOf a = 2) (hob : orderOf b = 2) : IsConj d.z (a * b) := by
  let L := conjugate d.K d.x
  let tx := d.x⁻¹ * d.t * d.x
  have htx : orderOf tx = 2 := by
    simpa only [tx, MulAut.conj_apply, inv_inv] using
      ((MulAut.conj d.x⁻¹).orderOf_eq d.t).trans d.t_order
  obtain ⟨k, hk, hka⟩ := involutions_conjugate_in_factor d.K d.model
    d.crossing_mark ha htx hoa
  let eL : L ≃* PSL(2, ZMod p) :=
    ((MulAut.conj d.x⁻¹).subgroupMap d.K).symm.trans d.model
  obtain ⟨l, hl, hlb⟩ := involutions_conjugate_in_factor L eL d.mark_mem hb d.t_order hob
  have hc : ∀ k : d.K, ∀ l : L, Commute (k : G) (l : G) := by
    intro k l
    exact (commutator_eq_bot_iff_le_centralizer.mp d.commuting k.property l l.property).symm
  let f : d.K × L →* G := d.K.subtype.noncommCoprod L.subtype hc
  have hp : IsConj ((⟨tx, d.crossing_mark⟩, ⟨d.t, d.mark_mem⟩) : d.K × L)
      (⟨a, ha⟩, ⟨b, hb⟩) := by
    apply isConj_iff.mpr
    refine ⟨(⟨k, hk⟩, ⟨l, hl⟩), ?_⟩
    apply Prod.ext
    · exact Subtype.ext hka
    · exact Subtype.ext hlb
  have hh := f.map_isConj hp
  change IsConj (tx * d.t) (a * b) at hh
  have he : d.z = tx * d.t := by
    rw [d.z_eq]
    exact (hc ⟨tx, d.crossing_mark⟩ ⟨d.t, d.mark_mem⟩).eq.symm
  rwa [← he] at hh

/-- Inside KKˣ, a conjugate of t lies in one factor: the diagonal case is
excluded by the original nonfusion of t and z. -/
theorem class_exclusion_in_pair {i : G} (hi : IsConj d.t i)
    (hiP : i ∈ d.K ⊔ conjugate d.K d.x) :
    i ∈ (d.K : Set G) ∪ conjugate d.K d.x := by
  let L := conjugate d.K d.x
  have hd : Disjoint d.K L :=
    disjoint_of_commuting_of_center_eq_bot d.commuting d.factor_center_eq_bot
  have hc : d.K ≤ centralizer (L : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp d.commuting
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting d.K L hd hc
  let ab := e.symm ⟨i, hiP⟩
  have hab : (ab.1 : G) * (ab.2 : G) = i := by
    rw [← he ab.1 ab.2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hiP⟩)
  have hi2 : i ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hi
    have ho : orderOf i = 2 := by
      rw [← hg]
      exact (MulAut.conj g).orderOf_eq d.t |>.trans d.t_order
    rw [← ho]
    exact pow_orderOf_eq_one i
  have hab2 : ab ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, e.apply_symm_apply]
    exact Subtype.ext hi2
  have ha2 : ab.1 ^ 2 = 1 := congrArg Prod.fst hab2
  have hb2 : ab.2 ^ 2 = 1 := congrArg Prod.snd hab2
  by_cases ha1 : ab.1 = 1
  · right
    rw [← hab, ha1]
    simp
  by_cases hb1 : ab.2 = 1
  · left
    rw [← hab, hb1]
    simp
  have haord : orderOf (ab.1 : G) = 2 := by
    rw [orderOf_coe]
    exact orderOf_eq_prime_iff.mpr ⟨ha2, ha1⟩
  have hbord : orderOf (ab.2 : G) = 2 := by
    rw [orderOf_coe]
    exact orderOf_eq_prime_iff.mpr ⟨hb2, hb1⟩
  have hz := d.diagonal_involution_conjugate ab.1.property ab.2.property haord hbord
  rw [hab] at hz
  exact (d.nonfusion (hi.trans hz.symm)).elim

end Incoming
end CFSG.Quasithin.Chapter2.PSL2PairSource

end
