module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Unitary.Borel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Unitary.Model
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData

/-!
# Excluding the signed unitary alternative in the S₃ branch

Source 15.3.33(1) places the invariant unitary Borel B in M ∩ I. Hence B
normalizes the actual elementary plane V₂. For n ≥ 3 the root/torus
calculation kills V₂ ∩ L, since its order is at most four. Mutual
normalization then makes V₂ centralize B. Each element of V₂ induces an
involutory automorphism of L, so the Borel-fixer calculation makes V₂
centralize L. The earlier normalizer bound N_G(V₂) ≤ M contradicts L ≰ M.

The remaining endpoint PSU₃(2) is solvable and cannot be a component.
Consequently these local inputs force n = 2 for any unitary component;
this contradicts the signed alternative 2ⁿ ≡ −1 (mod 3). The source plane
information thus excludes this alternative before any inner action is
assumed. In particular no assertion about O²(Y₊ ∩ L) or about the
three-rank of a unitary Borel is needed.

The final wrapper retains the exact compatible quotient actor and the
actual model hypotheses from the signed alternative. The stronger degree
restriction uses the original component model and the actual plane action
alone. Source: Aschbacher--Smith, paragraph between 15.3.43(d) and (e),
printed p.1139, with 15.3.11(3) and 15.3.33(1).
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L W : Subgroup G}

private theorem small_plane_centralizes
    (h : LocalSetup Yplus S M I L) (horbit : L = localSpan L S)
    {n : ℕ} (hn : 3 ≤ n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (hWS : W ≤ S) (hW : IsElementaryAbelian 2 W) (hcard : Nat.card W ≤ 4)
    (hBW : borel L S ≤ normalizer (W : Set G)) : W ≤ centralizer (L : Set G) := by
  let := hW
  have hsq (w : G) (hw : w ∈ W) : w ^ 2 = 1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) (⟨w, hw⟩ : W))
  obtain ⟨P, hP⟩ := h.unitary_component_sylow
  have hPL : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hBN : (normalizer (P : Set L)).map L.subtype = borel L S := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [← hPL, ← subgroupOf_normalizer_eq inf_le_right, subgroupOf_map_subtype]
    exact inf_comm _ _
  have hsmall : W.subgroupOf L = ⊥ := by
    apply UnitaryModel.small_invariant_subgroup_eq_bot hn hm P
    · rw [← card_map_of_injective L.subtype_injective, subgroupOf_map_subtype]
      exact (Nat.card_le_card_of_injective
        (inclusion (inf_le_left : W ⊓ L ≤ W)) (inclusion_injective _)).trans hcard
    · intro w hw
      exact Subtype.ext (hsq w hw)
    · rw [← hPL]
      exact fun w hw => ⟨hWS hw, w.property⟩
    · apply le_normalizer_iff.mpr
      intro x hx w hw
      have hxB : (x : G) ∈ borel L S := hBN ▸ mem_map_of_mem L.subtype hx
      exact (mem_normalizer_iff.mp (hBW hxB) (w : G)).mp hw
  have hinter : W ⊓ L = ⊥ := by
    rw [← subgroupOf_map_subtype, hsmall, Subgroup.map_bot]
  have hWL : W ≤ normalizer (L : Set G) :=
    hWS.trans (le_sup_right.trans (h.join_normalizes horbit))
  have hcomm : ⁅W, borel L S⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hinter]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hBW)
      ((commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp hWL))
  have hfixB : W ≤ centralizer (borel L S : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  let := h.unitary_component_simple (by omega) hm
  intro w hw
  let z : normalizer (L : Set G) := ⟨w, hWL hw⟩
  let a : MulAut L := L.normalizerMonoidHom z
  have ha : a ^ 2 = 1 := by
    change (L.normalizerMonoidHom z) ^ 2 = 1
    rw [← map_pow, show z ^ 2 = 1 from Subtype.ext (hsq w hw), map_one]
  have he : a = 1 := UnitaryModel.borel_fixer_eq_one (by omega) hm P a ha (by
    intro b hb
    apply Subtype.ext
    change w * (b : G) * w⁻¹ = b
    exact mul_inv_eq_iff_eq_mul.mpr ((hfixB hw b
      (hBN ▸ mem_map_of_mem L.subtype hb)).symm))
  intro l hl
  have hh := congrArg (fun f : MulAut L => (f ⟨l, hl⟩ : G)) he
  change w * l * w⁻¹ = l at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- A unitary component admitting the genuine local invariant plane has
fixed-field degree two. No inner-action or intersection-residual premise occurs. -/
theorem LocalSetup.unitary_degree_eq_two
    (h : LocalSetup Yplus S M I L) (horbit : L = localSpan L S)
    (hWS : W ≤ S) (hW : IsElementaryAbelian 2 W) (hcard : Nat.card W = 4)
    (hWN : normalizer (W : Set G) ≤ M)
    (hMI : M ⊓ I ≤ normalizer (W : Set G))
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) : n = 2 := by
  have hn2 := h.unitary_degree_ge_two hn hm
  by_contra hne
  obtain ⟨_, _, hB⟩ := h.unitary_borel horbit hn hm
  have hc := small_plane_centralizes h horbit (by omega : 3 ≤ n) hm
    hWS hW hcard.le (hB.trans hMI)
  exact h.component_outside ((le_centralizer_iff.mp hc).trans
    ((Subgroup.centralizer_le_normalizer _).trans hWN))

/-- The signed unitary parameter is incompatible with the earlier plane-normalizer
controls. This stronger exclusion is independent of the chosen diagonal witness. -/
theorem LocalSetup.not_unitary_signed (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (hp : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (horbit : L = localSpan L d.S) {n : ℕ} (hn : 0 < n)
    (hmod : 2 ^ n % 3 = 2) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) : False := by
  have he := h.unitary_degree_eq_two horbit hp.second_le hp.second_elementary hp.second_card
    hp.second_normalizer hp.second_normalized hn hm
  norm_num [he] at hmod

/-- The exact unitary diagonal alternative between 15.3.43(d) and (e).
Its field, Frobenius involution, quotient equivalence and compatible actor
remain those in `UnitaryDiagonalOnTwoQuotient`; the stronger local degree
obstruction already rules out its component model. -/
theorem LocalSetup.not_unitary_diagonal (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (hp : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (horbit : L = localSpan L d.S) {y : G} (_hy : y ∈ d.Yplus)
    (_hy3 : orderOf y = 3) {n : ℕ} (hn : 0 < n) (hmod : 2 ^ n % 3 = 2)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (_hact : Candidates.UnitaryDiagonalOnTwoQuotient L y (2 ^ n)) : False :=
  LocalSetup.not_unitary_signed d h hp horbit hn hmod hm

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
