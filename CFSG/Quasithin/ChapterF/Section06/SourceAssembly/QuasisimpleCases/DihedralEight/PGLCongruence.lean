module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.PGLLocals

/-!
# The mod-24 parameter of the proper PSL2 component branch

The literal common Sylow intersects the original two-residual in a Sylow
four-group. It normalizes the exceptional vertex's cubic residual inside
that same component. Transporting both actual subgroups through the prime
PSL2 marking supplies the cubic-normalizer congruence, completing the
numerical restriction in F.6.18(5), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The source's actual cubic residual supplies the congruence premise. -/
theorem prime_mod24_of_proper_psl_residual_of_left_exceptional
    (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hproper : pResidual 2 G ≠ ⊤) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hm : ClassicalGroup.IsPSL (pResidual 2 G) 2 p)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  let R := pResidual 2 G
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let b : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let j : R ≃* PSL(2,ZMod p) := a.trans (Atlas.fieldEquivPSL 2 b)
  obtain ⟨T, hTs⟩ := h.intersection_sylow
  have hTc : Nat.card T = 8 := by simpa only [hTs] using hT
  obtain ⟨S, hS⟩ := h.subnormal_intersection_sylow R (inferInstance : R.Normal).isSubnormal
  let U := S.mapSurjective (f := j.toMonoidHom) j.surjective
  have hUc := (sylow_card_section_le T R j.toMonoidHom j.surjective U).trans hTc.le
  have hFp : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  have hU4 : Nat.card U = 4 := by
    rcases Theory.ClassicalSmallSylow.psl2_small_sylow_parameters hFp U hUc with
      ⟨h4, _⟩ | ⟨hU8, _⟩
    · exact h4
    · have hR8 : 8 ∣ Nat.card R := by
        rw [Nat.card_congr j.toEquiv, ← hU8]
        exact U.card_subgroup_dvd_card
      exact (hproper (normal_eq_top_of_sylow_eight_of_eight_dvd T hTc R
        (isPGroup_quotient_pResidual 2) hR8)).elim
  obtain ⟨m, hm, ⟨u⟩⟩ := psl2_odd_hasDihedralSylowTwo_model (ZMod p) hFp U
  have hc : 2 * 2 ^ m = 4 := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr u.toEquiv, hU4]
  have hm1 : m = 1 := by
    have hh : 2 ^ m ≤ 2 ^ 1 := by omega
    have hh' := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
    omega
  let : IsKleinFour U := {
    card_four := hU4
    exponent_two := by
      rw [Monoid.exponent_eq_of_mulEquiv u, hm1, DihedralGroup.exponent]
      decide }
  let A := (pResidual 2 G₁).map G₁.subtype
  have hAR : A ≤ R := map_pResidual_le 2 G₁.subtype
  let B := A.subgroupOf R
  have hB : Nat.card B = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv,
      card_map_of_injective G₁.subtype_injective, h.local_residual_order_three hbad]
  have hSN : (S : Subgroup R) ≤ normalizer (B : Set R) := by
    apply le_normalizer_iff.mpr
    intro s hs x hx
    change (s : G) * (x : G) * (s : G)⁻¹ ∈ A
    rw [hS] at hs
    exact (mem_normalizer_iff.mp (h.intersection_normalizes_left_residual hs) (x : G)).mp hx
  apply Theory.PSL2.prime_mod24_of_four_normalizes_cubic hp h8 (U : Subgroup PSL(2,ZMod p))
    (B.map j.toMonoidHom)
  · rw [card_map_of_injective j.injective, hB]
  · change (S : Subgroup R).map j.toMonoidHom ≤ _
    rw [← map_equiv_normalizer_eq B j]
    exact map_mono hSN

/-- The mixed-vertex source argument chooses the cubic residual and
therefore derives the entire prime congruence in row (5). -/
theorem prime_mod24_of_proper_psl_residual
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hproper : pResidual 2 G ≠ ⊤) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hm : ClassicalGroup.IsPSL (pResidual 2 G) 2 p) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  rcases mixed_vertices_of_proper_psl_residual h hcore hT hproper Fact.out hp
    (by decide : 1 ≤ 1) (by simpa using hm) with ⟨_, hb⟩ | ⟨_, hb⟩
  · exact prime_mod24_of_proper_psl_residual_of_left_exceptional h.symm
      (by simpa only [inf_comm G₂ G₁] using hT) hproper hp h8 hm hb
  · exact prime_mod24_of_proper_psl_residual_of_left_exceptional h hT hproper hp h8 hm hb

end CFSG.Quasithin.ChapterF.SourceAssembly
