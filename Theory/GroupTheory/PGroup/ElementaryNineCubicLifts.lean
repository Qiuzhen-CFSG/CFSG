module
public import Theory.GroupTheory.PGroup.SupercriticalCubic
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.Representation.CoprimeElementaryComplement
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Invariant cubic lifts of a normal elementary group of order nine

Split a stable cubic line by a coprime invariant complement. Lift both
lines inside the supplied normal two-perfect subgroup, retaining the full
two-group kernel. The kernel normalizes both lifts, so generation of the
image gives generation upstairs without assuming the kernel lies in either
lift.

Source: Aschbacher–Smith, 14.5.20, printed p.1019, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]

/-- A stable line in a normal elementary-nine image supplies two normalized
cubic generators of its original two-perfect lift. -/
theorem exists_cubic_lifts_of_normal_elementary_nine
    (q : D →* E) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (Y : Subgroup D) [Y.Normal] (hYp : IsPPerfect 2 Y)
    [IsElementaryAbelian 3 (Y.map q)] (hY : Nat.card (Y.map q) = 9)
    (S : Subgroup D) (hS : IsPGroup 2 S)
    (C : Subgroup E) (hCY : C ≤ Y.map q) (hC : Nat.card C = 3)
    (hSC : S.map q ≤ normalizer (C : Set E)) :
    ∃ A B : Subgroup D, A ⊔ B = Y ∧
      (IsPPerfect 2 A ∧ S ≤ normalizer (A : Set D) ∧
        A.map q = C ∧ (q.comp A.subtype).ker = pCore 2 A ∧
        Nat.card (A ⧸ pCore 2 A) = 3) ∧
      (IsPPerfect 2 B ∧ S ≤ normalizer (B : Set D) ∧
        (q.comp B.subtype).ker = pCore 2 B ∧
        Nat.card (B ⧸ pCore 2 B) = 3) := by
  let P := Y.map q
  let : P.Normal := (inferInstance : Y.Normal).map q hq
  let C₀ := C.subgroupOf P
  let α : S.map q →* MulAut P :=
    (MulAut.conjNormal : E →* MulAut P).comp (S.map q).subtype
  have hcop : Nat.Coprime 3 (Nat.card (S.map q)) := by
    obtain ⟨n,hn⟩ := (hS.map q).exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hstable : ∀ s : S.map q, ∀ x ∈ C₀, α s x ∈ C₀ := by
    intro s x hx
    exact (mem_normalizer_iff.mp (hSC s.property) x).mp hx
  obtain ⟨R,hcomp,hRstable⟩ :=
    IsElementaryAbelian.exists_invariant_complement α hcop C₀ hstable
  have hC₀ : Nat.card C₀ = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCY).toEquiv).trans hC
  have hR : Nat.card R = 3 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C₀ R
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hcomp.inf_eq_bot,hcomp.sup_eq_top,card_bot,card_top,one_mul,hC₀,hY] at hh
    omega
  let R₀ := R.map P.subtype
  have hR₀ : Nat.card R₀ = 3 := by rw [card_map_of_injective P.subtype_injective,hR]
  have hSR : S.map q ≤ normalizer (R₀ : Set E) := by
    apply le_normalizer_iff.mpr
    rintro s hs _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem P.subtype (hRstable ⟨s,hs⟩ x hx)
  have hgen : C ⊔ R₀ = Y.map q := by
    have hh := congrArg (Subgroup.map P.subtype) hcomp.sup_eq_top
    dsimp only [C₀, R₀, P] at hh ⊢
    simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hCY,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  obtain ⟨A,hAY,hAp,hAm,hAS,hkA,hAk,hAe⟩ :=
    exists_three_lift_within_normal q hk Y C (S.map q) hCY hSC
      (IsPGroup.of_card (n := 1) (by simpa using hC))
  obtain ⟨B,hBY,hBp,hBm,hBS,hkB,hBk,hBe⟩ :=
    exists_three_lift_within_normal q hk Y R₀ (S.map q) (map_subtype_le R) hSR
      (IsPGroup.of_card (n := 1) (by simpa using hR₀))
  have hAB : A ⊔ B = Y := by
    apply le_antisymm (sup_le hAY hBY)
    apply isPPerfect_le_of_map_le_of_kernel_normalizes q Y (A ⊔ B) hYp hk
      ((le_inf hkA hkB).trans (normalizer_inf_normalizer_le_normalizer_sup A B))
    rw [Subgroup.map_sup,hAm,hBm,hgen]
  exact ⟨A,B,hAB,⟨hAp,(le_comap_map q S).trans hAS,hAm,hAk,
      (Nat.card_congr hAe.some.toEquiv).trans hC⟩,
    ⟨hBp,(le_comap_map q S).trans hBS,hBk,
      (Nat.card_congr hBe.some.toEquiv).trans hR₀⟩⟩

end Subgroup
