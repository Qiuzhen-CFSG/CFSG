module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Quotient
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.SourceInputs
public import Theory.Mathieu.M22.UniversalMultiplier.TwoRankSource.FourthPowers

/-!
# The two remaining M₂₂ covers on the original component

The literal quotient map has kernel O₂(L), and the centerless target makes
this kernel all of Z(L). The proved supplied-cover bounds leave orders one,
two and four. In order one the actual intersection consumers finish the
source conclusion. In orders two and four the unconditional I.2.2 hexad
recognition applies to the original L, quotient map and every native hexad.
In particular no local perfectness or alternating-cover input remains.

This is a reduction, not the exclusion of the last two alternatives. Their
ambient exclusion in Γ₀ remains necessary. The last lemma records the
nonsquare property of the binary covering center inside L; it makes no
claim about squares in the larger source Sylow S.

Source: Aschbacher–Smith I.2.2(6), printed pp.410,412; 1.1.5(3)(f),
printed p.502; and 2.3.9(7)(f), printed pp.525–526.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open ChapterI.Section02.ExceptionalCovers
open scoped Pointwise
variable {G : Type*} [Group G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The center of the original component is exactly the literal two-kernel. -/
theorem LocalSetup.mathieuTwentyTwo_center_eq (h : LocalSetup H L M S z)
    (e : (L ⧸ pCore 2 L) ≃* M22) : center L = pCore 2 L := by
  let f := h.componentQuotientCover e
  have hk := h.componentQuotientCover_ker e
  apply le_antisymm _ (hk ▸ f.ker_le_center)
  intro x hx
  have hc : f.toMonoidHom x ∈ center M22 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := f.surjective y
    simpa only [map_mul] using congrArg f.toMonoidHom (mem_center_iff.mp hx a)
  rw [m22_center_eq_bot, mem_bot] at hc
  exact hk ▸ (show x ∈ f.toMonoidHom.ker from hc)

/-- Reindex the same quotient by the now-proved equality of its kernels. -/
noncomputable def LocalSetup.mathieuTwentyTwo_centerQuotient
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22) :
    (L ⧸ center L) ≃* M22 :=
  (QuotientGroup.quotientMulEquivOfEq (h.mathieuTwentyTwo_center_eq e)).trans e

/-- The central quotient used by I.2.2 is the original map, pointwise. -/
theorem LocalSetup.mathieuTwentyTwo_centerQuotient_projection
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22) (x : L) :
    M22CentralCover.projection (h.mathieuTwentyTwo_centerQuotient e) x =
      e (QuotientGroup.mk' (pCore 2 L) x) := rfl

/-- Cyclicity of the supplied component kernel, without any multiplier lower bound. -/
theorem LocalSetup.mathieuTwentyTwo_core_isCyclic
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22) :
    IsCyclic (pCore 2 L) := by
  let := h.finite
  have hp : IsPGroup 2 (h.componentQuotientCover e).toMonoidHom.ker := by
    rw [h.componentQuotientCover_ker]
    exact pCore_isPGroup
  rw [← h.componentQuotientCover_ker e]
  exact M22UniversalMultiplier.TwoRankSource.twoPrimary_kernel_isCyclic
    (h.componentQuotientCover e) hp

/-- Only the binary and quartic kernels remain when this two-core is nontrivial. -/
theorem LocalSetup.mathieuTwentyTwo_core_card_cases
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22) :
    pCore 2 L = ⊥ ∨ Nat.card (pCore 2 L) = 2 ∨ Nat.card (pCore 2 L) = 4 := by
  let := h.finite
  have hp : IsPGroup 2 (h.componentQuotientCover e).toMonoidHom.ker := by
    rw [h.componentQuotientCover_ker]
    exact pCore_isPGroup
  have hd := M22UniversalMultiplier.TwoRankSource.twoPrimary_kernel_card_dvd_four
    (h.componentQuotientCover e) hp
  rw [h.componentQuotientCover_ker] at hd
  obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card (pCore 2 L) ∣ 2 ^ 2 from hd)
  interval_cases n
  · exact Or.inl (Subgroup.card_eq_one.mp hc)
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- Both recognized extensions refer to the original component, with all
earlier perfectness and A₆-cover inputs discharged. -/
theorem LocalSetup.mathieuTwentyTwo_nontrivial_hexad_models
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22)
    (hk : pCore 2 L ≠ ⊥) :
    (Nat.card (pCore 2 L) = 2 ∧ ∀ B, ∀ hB : B ∈ m22Blocks,
      Nonempty (M22Local.Binary.HexadRecognition (h.mathieuTwentyTwo_centerQuotient e) hB)) ∨
    (Nat.card (pCore 2 L) = 4 ∧ ∀ B, ∀ hB : B ∈ m22Blocks,
      Nonempty (M22Local.Quartic.HexadRecognition (h.mathieuTwentyTwo_centerQuotient e) hB)) := by
  let := h.finite
  let := h.quasisimple
  rcases h.mathieuTwentyTwo_core_card_cases e with he | he | he
  · exact (hk he).elim
  · refine Or.inl ⟨he, fun B hB => ?_⟩
    apply M22Local.Binary.exists_hexadRecognition_of_perfect
    simpa only [h.mathieuTwentyTwo_center_eq e] using he
  · refine Or.inr ⟨he, fun B hB => ?_⟩
    let : IsCyclic (center L) := by
      rw [h.mathieuTwentyTwo_center_eq e]
      exact h.mathieuTwentyTwo_core_isCyclic e
    apply M22Local.Quartic.exists_hexadRecognition_of_perfect
    simpa only [h.mathieuTwentyTwo_center_eq e] using he

/-- The split-kernel branch feeds the existing hexad intersection and its
literal E₁₆-by-A₆ extension, retaining the prescribed quotient map and action. -/
theorem mathieuTwentyTwo_cover_intersection_of_core_eq_bot
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m22)
    (hk : pCore 2 L = ⊥) :
    ∃ eL : L ≃* M22,
      (∀ x : L, eL x = d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)) ∧
      (∃ B ∈ m22Blocks,
        (M.subgroupOf L).map eL.toMonoidHom = MulAction.stabilizer M22 B) ∧
      AlternatingBySixteen (M.subgroupOf L) 6 := by
  let eL := twoCoreQuotientEquiv d.quotientIso hk
  exact ⟨eL, fun _ => rfl,
    mathieuTwentyTwo_intersection h eL d.action d.conjugation d.inner,
    mathieuTwentyTwo_extension h eL d.action d.conjugation d.inner⟩

/-- A nonidentity binary covering-center element has no square root in L.
The statement deliberately does not extend this to the larger ambient S. -/
theorem LocalSetup.mathieuTwentyTwo_binary_kernel_not_square
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22)
    (hc : Nat.card (pCore 2 L) = 2) (k : pCore 2 L) (hk : k ≠ 1) :
    ¬ ∃ x : L, x ^ 2 = k.val := by
  let := h.finite
  rintro ⟨x, hx⟩
  let eZ := h.mathieuTwentyTwo_centerQuotient e
  have hz : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq e] using hc
  have hp : M22CentralCover.projection eZ x ^ 2 = 1 := by
    rw [← map_pow, hx]
    apply (show k.val ∈ (M22CentralCover.projection eZ).ker ↔
      M22CentralCover.projection eZ k.val = 1 from Iff.rfl).mp
    rw [M22CentralCover.projection_ker, h.mathieuTwentyTwo_center_eq e]
    exact k.property
  have hs := M22CentralCover.square_eq_one eZ hz x hp
  exact hk (Subtype.ext (hx.symm.trans hs))

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
