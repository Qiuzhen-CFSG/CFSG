module
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.FullRankInvolutionCommutingAction

/-!
# Ambient layer control from a full-rank quotient involution

Let `P` normalize `U`, with a prescribed conjugation homomorphism `ρ` on
`W = U/(Z.subgroupOf U)`, where `W` is elementary abelian at two. Suppose
`Z ≤ A`, `U` normalizes `A`, and `Q ≤ P` centralizes `A`. If `x ∈ P ∩ A`
induces an involution whose fixed subgroup has order the square root of
`|W|`, then `[Q,U] ≤ A`.

The involution commutator lies in the quotient image `D` of `A ∩ U`:
its generators lift to commutators with powers of `x`, which lie in `A`
by normalization. The image of `Q` commutes with the involution and fixes
`D` pointwise. The full-rank commuting-action theorem therefore places
its action commutator in `D`. Since the quotient kernel lies in `A`,
pulling these commutators back proves the ambient containment. All
constructions retain the caller's exact normality instance and `ρ`.

This is the small-module branch of Stellmacher (9.1), Journal of Algebra
190 (1997), p.47, after the application of (1.3). The graph hypotheses
and the derivation of the full-rank equality belong to its caller.
-/
open scoped commutatorElement
namespace Subgroup
public theorem commutator_le_of_quotient_full_rank_involution
    {G : Type*} [Group G] [Finite G] (P U Z A Q : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G)) (hN : (Z.subgroupOf U).Normal)
    (hZA : Z ≤ A) (hUA : U ≤ normalizer (A : Set G))
    (hQP : Q ≤ P) (hQA : Q ≤ centralizer (A : Set G)) :
    let _ := hN
    ∀ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) →
      ∀ (x : P), (x : G) ∈ A →
      IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) →
      (ρ x ≠ 1 ∧ (ρ x)^2 = 1) →
      Nat.card (U ⧸ Z.subgroupOf U) =
        Nat.card (FixedPoints.subgroup (zpowers (ρ x)) (U ⧸ Z.subgroupOf U))^2 →
      ⁅Q,U⁆ ≤ A := by
  let _ := hN
  dsimp only
  intro ρ hρ x hx hW hxi hcard
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let f := QuotientGroup.mk' (Z.subgroupOf U)
  let D := (A.subgroupOf U).map f
  let B := (Q.subgroupOf P).map ρ
  let M := commutatorAction (zpowers (ρ x)) W
  have hpre : D.comap f = A.subgroupOf U := by
    apply comap_map_eq_self
    intro u hu
    exact hZA ((QuotientGroup.eq_one_iff u).mp hu)
  have hMD : M ≤ D := by
    change commutatorAction (zpowers (ρ x)) W ≤ D
    rw [commutatorAction_eq_closure]
    apply (closure_le (K := D)).mpr
    rintro _ ⟨a, w, rfl⟩
    have ha : (a : MulAut W) ∈ (zpowers x).map ρ := by
      rw [MonoidHom.map_zpowers]
      exact a.property
    obtain ⟨y, hy, hya⟩ := ha
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
    have hyA : (y : G) ∈ A :=
      (zpowers_le.mpr (show x ∈ A.subgroupOf P from hx)) hy
    let v : U := ⟨(y : G) * (u : G) * (y : G)⁻¹,
      (mem_normalizer_iff.mp (hPU y.property) u).mp u.property⟩
    have heq : (a : MulAut W) (f u) = f v := by rw [← hya]; exact hρ y u
    change (f u)⁻¹ * (a : MulAut W) (f u) ∈ D
    rw [heq, ← map_inv, ← map_mul]
    apply mem_map_of_mem
    change (u : G)⁻¹ * ((y : G) * (u : G) * (y : G)⁻¹) ∈ A
    have hh := A.mul_mem
      ((mem_normalizer_iff.mp (hUA (U.inv_mem u.property)) y).mp hyA)
      (A.inv_mem hyA)
    simpa only [inv_inv, mul_assoc] using hh
  have hBcomm : ∀ b ∈ B, Commute b (ρ x) := by
    rintro b ⟨q, hq, rfl⟩
    have hqx : Commute q x := by
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (hQA hq) x hx).symm
    exact hqx.map ρ
  have hBfix : ∀ b ∈ B, ∀ w ∈ D, b w = w := by
    rintro b ⟨q, hq, rfl⟩ w ⟨u, hu, rfl⟩
    rw [hρ]
    apply congrArg f
    apply Subtype.ext
    have hqu : (q : G) * (u : G) = (u : G) * (q : G) :=
      (mem_centralizer_iff.mp (hQA hq) u hu).symm
    change (q : G) * (u : G) * (q : G)⁻¹ = (u : G)
    rw [hqu, mul_assoc, mul_inv_cancel, mul_one]
  have hBD : commutatorAction B W ≤ D :=
    (commutatorAction_le_of_commuting_full_rank_involution (ρ x) hxi B hBcomm
      (fun b hb w hw => hBfix b hb w (hMD hw)) hcard).trans hMD
  rw [commutator_comm]
  apply commutator_le.mpr
  intro u hu q hq
  let qP : P := ⟨q, hQP hq⟩
  let v : U := ⟨u⁻¹, U.inv_mem hu⟩
  let w : U := ⟨q * u⁻¹ * q⁻¹,
    (mem_normalizer_iff.mp (hPU qP.property) u⁻¹).mp (U.inv_mem hu)⟩
  have hdisp : (f v)⁻¹ * ρ qP (f v) ∈ D := hBD (by
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨⟨ρ qP, mem_map_of_mem ρ hq⟩, f v, rfl⟩)
  have heq : ρ qP (f v) = f w := hρ qP v
  rw [heq, ← map_inv, ← map_mul] at hdisp
  have hmem : v⁻¹ * w ∈ A.subgroupOf U := hpre ▸ hdisp
  change (u⁻¹)⁻¹ * (q * u⁻¹ * q⁻¹) ∈ A at hmem
  simpa only [inv_inv, commutatorElement_def, mul_assoc] using hmem
end Subgroup
