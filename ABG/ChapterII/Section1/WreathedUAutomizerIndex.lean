module
public import ABG.ChapterII.Section1.WreathedUFrattiniAction

/-!
# The automizer of the wreathed abelian base

In a finite group with a chosen wreathed fusion frame, the automizer of its
actual abelian maximal subgroup U has order two or six. This is the first
normalizer calculation in the proof of Alperin--Brauer--Gorenstein, Chapter II,
Section 1, Proposition 2, article p.12 (`page-013.tex` of the transcription).
No fusion conclusion or tame-intersection hypothesis is assumed.

The faithful Frattini action theorem embeds the actual base automizer in the
six-element automorphism group of its Klein four quotient. Identify the base
with the presentation base through its actual Sylow inclusion. Normality puts
the Sylow subgroup in N(U), and the outer presentation involution exchanges
the two distinguished generators, so its induced automorphism is a nonidentity
involution. The automizer order is therefore even and divides six.
-/

open scoped IsMulCommutative

namespace ABG.Wreathed
variable {G : Type*} [Group G] [Finite G]

/-- The wreathed base normalizer induces either two or six automorphisms. -/
public theorem u_automizer_index
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) :
    automizerIndex U = 2 ∨ automizerIndex U = 6 := by
  obtain ⟨P⟩ := nonempty_presentation hf.1
  have hUS : U ≤ S := hf.2.1
  have hUP : U.subgroupOf (S : Subgroup G) = P.U := by
    exact (hf.2.2.2.2.1 P.U P.abelian_maximal_unique.1 P.U_isCoatom).symm
  have hnU : (U.subgroupOf (S : Subgroup G)).Normal := by
    rw [hUP]
    exact Subgroup.normal_of_index_eq_two P.index_U
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mp hnU
  obtain ⟨hfour, hfaith⟩ := u_frattini_action S n U V hf
  let := hfour
  let f := U.normalizerMonoidHom
  have hcard : Nat.card f.range = automizerIndex U := by
    rw [← Subgroup.index_ker, Subgroup.normalizerMonoidHom_ker]
    rfl
  have hdvd : automizerIndex U ∣ 6 := by
    rw [← hcard, ← IsKleinFour.card_mulAut (U ⧸ frattini U)]
    exact Subgroup.card_dvd_of_injective _ hfaith
  let i : S →* Subgroup.normalizer (U : Set G) := Subgroup.inclusion hSN
  let e : P.U ≃* U := (MulEquiv.subgroupCongr hUP.symm).trans
    (Subgroup.subgroupOfEquivOfLe hUS)
  let s : P.U := ⟨P.s, Subgroup.subset_closure (by simp)⟩
  let t : P.U := ⟨P.t, Subgroup.subset_closure (by simp)⟩
  have hzt : f (i P.z) (e s) = e t := by
    apply Subtype.ext
    change (P.z : G) * (P.s : G) * (P.z : G)⁻¹ = (P.t : G)
    have hz : P.z⁻¹ = P.z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using P.z_sq)
    have hzG : (P.z : G)⁻¹ = (P.z : G) := congrArg Subtype.val hz
    rw [hzG]
    exact congrArg Subtype.val (by simpa only [hz] using P.conj_s)
  have heven : 2 ∣ automizerIndex U := by
    let a : f.range := ⟨f (i P.z), ⟨i P.z, rfl⟩⟩
    have ha : orderOf a = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        change f (i P.z) ^ 2 = 1
        rw [← map_pow, ← map_pow, P.z_sq, map_one, map_one]
      · intro he
        have he' : f (i P.z) = 1 := congrArg Subtype.val he
        rw [he'] at hzt
        have hst : s = t := e.injective hzt
        exact P.base_frattini_structure.2 s t rfl rfl (congrArg _ hst)
    have hd := orderOf_dvd_natCard a
    rw [ha, hcard] at hd
    exact hd
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hdvd
  interval_cases h : automizerIndex U <;> simp_all
end ABG.Wreathed
