module

public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Reduced commutator modules from coprime supplements

Let W be a reduced normal elementary abelian p-subgroup, and let X be
normal with G/X a p-group. Suppose Q lies in X, has order coprime to |W|,
and supplements C_X(W) in X. Coprime action decomposes W into [W,Q]
and its Q-fixed subgroup. Thus C_X([W,X]) centralizes W. The image of
C_G([W,X]) in G/C_G(W) is a normal p-subgroup, so reducedness kills it.
This identifies the two literal centralizers and proves [W,X] reduced.

The complement Q need not be normal, and no nontriviality or irreducibility
premise is required. Source application: Aschbacher--Smith, Lemma 3.2.13,
printed pp.584--585, with W=R₂(XT) and Q an odd Sylow subgroup of X.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- A coprime supplement inside X detects the full action on a reduced W
through the commutator [W,X], when G/X is a p-group. -/
theorem IsPReduced.centralizer_commutator_eq_of_coprime_supplement
    {W : Subgroup G} (hW : IsPReduced p W) (X Q : Subgroup G) [X.Normal]
    (hquot : IsPGroup p (G ⧸ X)) (hQX : Q ≤ X)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card W))
    (hgen : X ≤ centralizer (W : Set G) ⊔ Q) :
    centralizer ((⁅W, X⁆ : Subgroup G) : Set G) = centralizer (W : Set G) := by
  let := hW.normal
  let := hW.elementary
  let V := ⁅W, X⁆
  let C := centralizer (W : Set G)
  let D := centralizer (V : Set G)
  have hCD : C ≤ D := centralizer_le (commutator_le_left W X)
  have hsplit : W ≤ V ⊔ (W ⊓ centralizer (Q : Set G)) := by
    have hs := eq_commutator_sup_centralizer_of_solvable_coprime W Q
      (by rw [normalizer_eq_top]; exact le_top)
      (Group.isSolvable_of_comm fun x y : W => mul_comm x y) hcop
    calc
      W = ⁅W, Q⁆ ⊔ (W ⊓ centralizer (Q : Set G)) := hs
      _ ≤ _ := sup_le_sup (commutator_mono le_rfl hQX) le_rfl
  have hQC : Q ⊓ D ≤ C := by
    apply le_centralizer_iff.mp
    apply hsplit.trans
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · exact inf_le_right.trans (centralizer_le inf_le_left)
  have hXC : X ⊓ D ≤ C := by
    intro x hx
    obtain ⟨c, hc, q, hq, rfl⟩ := mem_sup_of_normal_left.mp (hgen hx.1)
    have hqD : q ∈ D := by
      simpa only [inv_mul_cancel_left] using D.mul_mem (D.inv_mem (hCD hc)) hx.2
    exact C.mul_mem hc (hQC ⟨hq, hqD⟩)
  let f := QuotientGroup.mk' C
  have hDp : IsPGroup p (D.map f) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro z
    obtain ⟨g, hg, hgz⟩ := z.property
    obtain ⟨n, hn⟩ := hquot.exists_pow_pow_eq_one (QuotientGroup.mk' X g)
    have hgX : g ^ p ^ n ∈ X :=
      (QuotientGroup.eq_one_iff _).mp (by
        change QuotientGroup.mk' X (g ^ p ^ n) = 1
        rw [map_pow]
        exact hn)
    refine ⟨n, Subtype.ext ?_⟩
    change (z : G ⧸ C) ^ p ^ n = 1
    rw [← hgz, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hXC ⟨hgX, D.pow_mem hg _⟩)
  have hDcore : D.map f ≤ pCore p (G ⧸ C) :=
    le_sSup ⟨Normal.map inferInstance f (QuotientGroup.mk'_surjective C), hDp⟩
  have hDzero : D.map f = ⊥ := by
    apply bot_unique
    exact hDcore.trans_eq hW.quotient_pCore_eq_bot
  have hDC : D ≤ C := by
    simpa only [f, QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hDzero
  exact le_antisymm hDC hCD

/-- The original commutator with a normal p-group-quotient subgroup is
reduced when that subgroup has a coprime supplement modulo C_G(W). -/
theorem IsPReduced.commutator_of_coprime_supplement
    {W : Subgroup G} (hW : IsPReduced p W) (X Q : Subgroup G) [X.Normal]
    (hquot : IsPGroup p (G ⧸ X)) (hQX : Q ≤ X)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card W))
    (hgen : X ≤ centralizer (W : Set G) ⊔ Q) :
    IsPReduced p ⁅W, X⁆ := by
  let := hW.normal
  let := hW.elementary
  refine ⟨inferInstance, IsElementaryAbelian.of_le (commutator_le_left W X), ?_⟩
  have he := hW.centralizer_commutator_eq_of_coprime_supplement X Q hquot hQX hcop hgen
  let e := QuotientGroup.quotientMulEquivOfEq he
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso p e]
  exact hW.quotient_pCore_eq_bot

end Theory.GroupTheory
