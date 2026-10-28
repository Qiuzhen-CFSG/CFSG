module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction.CentralCoordinates
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.Reduction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiZeroQuotient
public import CFSG.Quasithin.ChapterC.Section01.SolvableShortAbelianCore.QuotientThree

/-!
# Transferring the sextet subgroup calculation to actual blocks

Every χ₀ block has simple quotient by O₂. A nontrivial quotient of that
simple group is therefore isomorphic to it. The native sextet calculation
needed here only concerns subnormal, two-perfect subgroups E: E is trivial,
or E/O₂(E) has order three and |E| > 12, or E/O₂(E) has order 1080.

Apply these alternatives to every coordinate of the central-orbit image
of a block. The cubic case would force the short group itself to have order
twelve, too small to surject onto E. The order-1080 case is incompatible
with all actual χ₀ quotient models. All coordinates consequently vanish,
making the block central, contrary to its nonzero commutator module.

The native subgroup alternatives are an explicit premise here, discharged
in `M24.BlockObstruction` by `M24LocalGeometry.subnormal_sextet_orders`.
The conditional theorem is applied to the literal component-quotient lifts.
Source: Aschbacher–Smith 2.3.9(7), printed p.526; C.1.7–13, pp.123–125;
GLS3 Table 5.3e for the sextet geometry.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
open Subgroup ChapterC Theory.GroupTheory Sporadic.Mathieu M24LocalGeometry

private theorem core_quotient_card_of_simple {B E : Type*} [Group B] [Group E] [Finite B]
    [IsSimpleGroup (B ⧸ pCore 2 B)] (f : B →* E) (hf : Function.Surjective f)
    (hne : 1 < Nat.card (E ⧸ pCore 2 E)) :
    Nat.card (B ⧸ pCore 2 B) = Nat.card (E ⧸ pCore 2 E) := by
  let : Finite E := Finite.of_surjective f hf
  have hm : (pCore 2 B).map f ≤ pCore 2 E :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  let t := (QuotientGroup.mk' (pCore 2 E)).comp f
  have hk : pCore 2 B ≤ t.ker := by
    intro b hb
    exact (QuotientGroup.eq_one_iff _).mpr (hm ⟨b, hb, rfl⟩)
  let q := QuotientGroup.lift (pCore 2 B) t hk
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E) y
    obtain ⟨b, rfl⟩ := hf e
    exact ⟨QuotientGroup.mk' (pCore 2 B) b, rfl⟩
  let : Nontrivial (E ⧸ pCore 2 E) := Finite.one_lt_card_iff_nontrivial.mp hne
  have hi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rcases (inferInstance : q.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hqone := MonoidHom.ker_eq_top_iff.mp ht
      obtain ⟨y, hy⟩ := exists_ne (1 : E ⧸ pCore 2 E)
      obtain ⟨b, rfl⟩ := hq y
      exact (hy (DFunLike.congr_fun hqone b)).elim
  exact Nat.card_congr (MulEquiv.ofBijective q ⟨hi, hq⟩).toEquiv

/-- The intrinsic native-local order calculation used by the sextet
obstruction. Orders are used only to exclude block quotients. -/
def SubnormalSextetOrders (P : Type*) [Group P] : Prop :=
  ∀ E : Subgroup P, E.IsSubnormal → IsPPerfect 2 E →
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 1080

private theorem no_chiZero_central_power {B P : Type*} [Group B] [Group P]
    (hB : IsChiZeroBlock B) (hP : SubnormalSextetOrders P) {n : ℕ}
    (q : B →* (Fin n → P)) (hqc : q.ker ≤ center B) (hqs : q.range.IsSubnormal) : False := by
  have hs := hB.chi.short
  let := hs.finite
  let := hB.quotient_simple
  have hzero (b : B) (i : Fin n) : q b i = 1 := by
    let ev := Pi.evalMonoidHom (fun _ : Fin n => P) i
    have hev : Function.Surjective ev := fun p => ⟨fun _ => p, rfl⟩
    let f := ev.comp q
    have hfsub : f.range.IsSubnormal := by
      rw [MonoidHom.range_comp]
      exact hqs.map hev
    have hfp : IsPPerfect 2 f.range := hs.twoPerfect.of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
    rcases hP f.range hfsub hfp with h1 | ⟨h3, hlarge⟩ | h1080
    · have hz : f.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact DFunLike.congr_fun (MonoidHom.range_eq_bot_iff.mp hz) b
    · have hqcard := core_quotient_card_of_simple f.rangeRestrict
        f.rangeRestrict_surjective (by rw [h3]; decide)
      have hBcard : Nat.card B = 12 := hs.card_eq_twelve_of_quotient_three (hqcard.trans h3)
      have hc := Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
      rw [hBcard] at hc
      omega
    · have hqcard := core_quotient_card_of_simple f.rangeRestrict
        f.rangeRestrict_surjective (by rw [h1080]; decide)
      exact (HeldCase.not_chiZero_of_quotient_card_1080 (hqcard.trans h1080) hB).elim
  have hcenter : (⊤ : Subgroup B) ≤ center B := by
    intro b _
    exact hqc (funext (hzero b))
  apply hs.blockU_ne_bot
  exact commutator_top_right_eq_bot_iff_le_center.mpr ((le_top : pCore 2 B ≤ ⊤).trans hcenter)

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The native subgroup calculation excludes all χ₀ blocks through the
actual central cover, including those moved by J(S). -/
theorem sextet_blockObstruction_of_orders (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (X : Sextet)
    (hinter : L ⊓ localOvergroup d ((S : Subgroup H).map H.subtype) (sextetStabilizer X) =
      lift d (sextetStabilizer X))
    (horders : SubnormalSextetOrders (sextetStabilizer X)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (localOvergroup d ((S : Subgroup H).map H.subtype) (sextetStabilizer X)) := by
  intro B hB _
  obtain ⟨n, q, hqc, hqs⟩ := block_central_coordinates h d (sextetStabilizer X) hinter B hB.1
  exact (no_chiZero_central_power hB.2 horders q hqc hqs).elim
end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

end
