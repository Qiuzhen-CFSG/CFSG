module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary

/-!
# The commuting clauses of F.8.1 and F.9.8 in Section 12.8

For the marked point of order two, a nontrivial intersection with any
subgroup is equivalent to containment. Thus F.8.1(a) and F.9.8(f) have
exactly the same meaning here. Their common commuting condition makes
the H-conjugate span abelian directly: all its generating conjugates
contain the point and commute with V. Conversely, the normalizer
transitivity supplied by 12.8.3 gives the commuting condition from
abelianness of the span.

This proves the commuting-clause portion of 12.8.6 with the actual right
conjugation convention. It does not claim the remaining generalized
Fitting, normal-core, residual, or amalgam hypotheses of F.8.1/F.9.8.
Source: Aschbacher–Smith, printed pp.316–321 and 850–851.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

public theorem point_ne_bot (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    F.Vi 1 ≠ ⊥ := by
  intro he
  have hc := F.card 1 hn
  simp [he] at hc

/-- The order-two point has nonzero intersection exactly with its overgroups. -/
public theorem point_inf_ne_bot_iff (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (A : Subgroup G) : F.Vi 1 ⊓ A ≠ ⊥ ↔ F.Vi 1 ≤ A := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  obtain ⟨u, _, hu⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hc
  constructor
  · intro h
    obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp h
    have hxn : (⟨x, x.property.1⟩ : F.Vi 1) ≠ 1 := by
      intro he
      have hxG : (x : G) = 1 := congrArg (fun a : F.Vi 1 => (a : G)) he
      exact hx (Subtype.ext hxG)
    intro y hy
    by_cases hy1 : y = 1
    · simpa only [hy1] using A.one_mem
    have hyn : (⟨y, hy⟩ : F.Vi 1) ≠ 1 := fun he => hy1 (congrArg Subtype.val he)
    have he : y = (x : G) :=
      congrArg (fun a : F.Vi 1 => (a : G)) ((hu _ hyn).trans (hu _ hxn).symm)
    exact he.symm ▸ x.property.2
  · intro h
    rw [inf_eq_left.mpr h]
    exact F.point_ne_bot hn

/-- The exact two commuting clauses agree when |V₁|=2. -/
public theorem f8a_iff_f9f (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    (∀ g : G, F.Vi 1 ⊓ conjugate V g ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥) ↔
      (∀ g : G, F.Vi 1 ≤ conjugate V g → ⁅V, conjugate V g⁆ = ⊥) := by
  simp only [F.point_inf_ne_bot_iff hn]

/-- F.9.8(f) alone makes the actual point-normalizer span abelian. -/
public theorem abelian_U_of_f9f (F : InvariantFlag T V n)
    (hcomm : ∀ g : G, F.Vi 1 ≤ conjugate V g → ⁅V, conjugate V g⁆ = ⊥) :
    IsMulCommutative F.U := by
  have hc : F.U ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨h, hh, v, hv, rfl⟩
    have hfix : (F.Vi 1).map (MulAut.conj h).toMonoidHom = F.Vi 1 :=
      mem_normalizer_iff_map_conj_eq.mp hh
    have hp : F.Vi 1 ≤ conjugate V h⁻¹ := by
      simpa only [conjugate, inv_inv] using hfix.symm.le.trans (map_mono (F.le_seed 1))
    have he := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hcomm h⁻¹ hp))
    apply he
    exact mem_map.mpr ⟨v, hv, by simp [MulAut.conj_apply]⟩
  apply le_centralizer_iff_isMulCommutative.mp
  exact le_centralizer_conjugateSpanBy_of_normalizes F.U V F.H
    (le_normalizer_conjugateSpanBy V F.H) hc

/-- Earlier normalizer transitivity supplies the converse commuting clause. -/
public theorem f9f_iff_abelian_U (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ a ∈ normalizer (V : Set G), (MulAut.conj a) z = x) :
    (∀ g : G, F.Vi 1 ≤ conjugate V g → ⁅V, conjugate V g⁆ = ⊥) ↔
      IsMulCommutative F.U := by
  refine ⟨F.abelian_U_of_f9f, ?_⟩
  intro h g hg
  apply (F.abelian_U_iff_intersections_commute hn z hz hne htrans).mp h g
  intro he
  apply F.point_ne_bot hn
  apply le_bot_iff.mp
  exact he ▸ le_inf (F.le_seed 1) hg

/-- The commuting clause is equivalent to abelianness of all source local spans. -/
public theorem f9f_iff_all_local_spans_abelian (F : InvariantFlag T V n)
    (hn : 1 ≤ n) (L M : Subgroup G) (hescape : ¬ F.H ≤ M)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ a ∈ normalizer (V : Set G), (MulAut.conj a) z = x) :
    (∀ g : G, F.Vi 1 ≤ conjugate V g → ⁅V, conjugate V g⁆ = ⊥) ↔
      ∀ J ∈ F.Hz L M, IsMulCommutative (F.UH J) :=
  (F.f9f_iff_abelian_U hn z hz hne htrans).trans
    (F.all_local_spans_abelian_iff hn L M hescape).symm

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
