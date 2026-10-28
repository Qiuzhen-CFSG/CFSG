module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LinearLocalRoots

/-!
# Radical normality from the actual linear local group

For the literal panel action, the image of U in the source local group is
a two-subgroup. A marking of that group by PSL₂(F), with the actual simple
root of order |F|, bounds this image by a Sylow subgroup of order |F|. The
known inclusion U ∩ Kᵢ ≤ U_{sᵢ} and the exact root/remainder index then force
equality. Thus the remainder lies in the full panel kernel and is normal
in the whole parabolic, as required by source (3G).

This proves the linear case of Fong–Seitz I (2B), printed p.9, on the same
quotient and panel used by the original source. The supplied local marking
is an isomorphism of the actual panel image, not an unrelated family tag.
No perfectness is required, so the proof includes F₂.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The canonical remainder lies in the kernel of the actual panel action. -/
theorem linear_remainder_le_kernel {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F))
    (hq : Nat.card (simpleRoot Q split i) = Nat.card F) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let f₀ : split.U →* localGroup Q split i :=
    (localAction Q split i).rangeRestrict.comp
      (inclusion (show split.U ≤ localClosure Q split i from le_sup_left))
  let f := μ.toMonoidHom.comp f₀
  have hk : f.ker = (localKernel Q i).subgroupOf split.U := by
    ext x
    change μ (f₀ x) = 1 ↔ _
    rw [μ.map_eq_one_iff]
    change (f₀ x : localGroup Q split i) = 1 ↔ _
    rw [Subtype.ext_iff]
    change localAction Q split i (inclusion le_sup_left x) = 1 ↔ _
    rw [localAction_eq_panelAction]
    change panelAction Q i split.U (split.U_le.trans (Q.tits.B_le_standardParabolic _)) x = 1 ↔ _
    exact Iff.of_eq (congrArg (fun H : Subgroup split.U => x ∈ H)
      (panelAction_ker Q i split.U (split.U_le.trans (Q.tits.B_le_standardParabolic _))))
  have hp : IsPGroup 2 f.range := split.isTwo.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨T,hT⟩ := hp.exists_le_sylow
  have hrange : Nat.card f.range ≤ Nat.card F := by
    have hcard : Nat.card T = Nat.card F := by
      exact (Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T).toEquiv).symm
    exact (card_le_of_le hT).trans_eq hcard
  let R := (simpleRemainder Q split i).subgroupOf split.U
  have hle : f.ker ≤ R := by
    rw [hk]
    exact fun x hx => unipotent_inf_kernel_le_remainder Q split i ⟨x.property,hx⟩
  have he : f.ker = R := by
    by_contra hne
    have ht := index_strictAnti (lt_of_le_of_ne hle hne)
    rw [index_ker] at ht
    change ((simpleRemainder Q split i).subgroupOf split.U).index < Nat.card f.range at ht
    rw [simpleRemainder_index,hq] at ht
    omega
  intro x hx
  have hx' : (⟨x,hx.1⟩ : split.U) ∈ f.ker := he.symm ▸ hx
  rw [hk] at hx'
  exact hx'

/-- The original (2B) equality, inside the same finite marked quotient. -/
theorem linear_remainder_eq_unipotent_inf_kernel {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F))
    (hq : Nat.card (simpleRoot Q split i) = Nat.card F) :
    simpleRemainder Q split i = split.U ⊓ localKernel Q i :=
  remainder_eq_unipotent_inf_kernel Q split i (linear_remainder_le_kernel Q split i μ hq)

/-- The full original parabolic normalizes its canonical remainder. -/
theorem linear_remainder_parabolic_normalizes {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F))
    (hq : Nat.card (simpleRoot Q split i) = Nat.card F) :
    Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
  remainder_parabolic_normalizes Q split i (linear_remainder_le_kernel Q split i μ hq)

/-- The precise radical-normality premise of source (3G). -/
theorem linear_remainder_normalizes {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F))
    (hq : Nat.card (simpleRoot Q split i) = Nat.card F) :
    split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
  (split.U_le.trans (Q.tits.B_le_standardParabolic _)).trans
    (linear_remainder_parabolic_normalizes Q split i μ hq)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
