module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.CentralExtensionPartialInversion

/-!
# The three-primary HS central-kernel exclusion

The commuting pair already used for the HS three-rank witness generates a
subgroup of order nine. Its nine normal forms are distinguished on letter zero.
The certified ambient order makes this subgroup Sylow. A word in the original
ATLAS generators inverts its first generator and fixes its second; partial
inversion makes all their lifts commute, and central Sylow transfer excludes
three from every finite perfect central kernel.

Packed permutations certify these exact words in the literal degree-100 carrier.
GAP only discovers candidate words; every equality is checked by Lean's kernel.
The retained data and reproduction instructions are in `source/`.
Sources: Aschbacher–Smith I.1.3(1), printed p.407, GLS3 §6.1, and ATLAS
HSG1-p100B0 (provenance in the imported carrier's source directory).
-/

namespace Theory.SpecificGroups.J2HSMultipliers.HS.Three
open Sporadic.LeechRelated.HS Subgroup
open Sporadic.LeechRelated.HS.OrderCertificate

private def a : Carrier := ⟨p0, a_eq_generator.symm ▸ subset_closure (by simp)⟩
private def b : Carrier := ⟨p1, b_eq_generator.symm ▸ subset_closure (by simp)⟩

private def xMap (i : Fin 100) : Fin 100 :=
  ⟨(3590466344902948551500625880980508819832494606187222822039878239244387711950573130115437290048217149180348662678481892044422835610802713319183385920130626599983898057698595368469169751438366140358681017099494366 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def xInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3766358194415054432431872030361567221117552467915209481939698628316670309266301918384587288391129662634053215462575692351710928147551825924256149324224257358047247188724763289543387824437679782136312604234444347 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem xLeft : ∀ i, xInvMap (xMap i) = i := by
  apply allFin
  decide +kernel
private def xPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm xMap xInvMap xLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin xLeft)
private def xWord : Carrier := (a * b ^ 2 * a * b ^ 3) ^ 2
private theorem xPerm_eq_word : xPerm = (xWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def x : Carrier := ⟨xPerm, xPerm_eq_word.symm ▸ xWord.property⟩

private def g : Carrier :=
  (a * b) * (a * b ^ 2) * (a * b) * (a * b) * (a * b ^ 2) * (a * b ^ 4)

private def yMap (i : Fin 100) : Fin 100 :=
  ⟨(3750349079305838044981121055900341228338299804456455649680193798848369789227233615685143693511724137060064160094318389888993767891278341523329488995755586067330966185527335840679170354236945173181370811915911439 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def yInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3579541364098713156572144741719664717027064103088755592230252357559572305570015909533178500481311184558028061656811304260057030694804190819984280386040191093377573034441814789461860292611312739880951217710458519 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem yLeft : ∀ i, yInvMap (yMap i) = i := by
  apply allFin
  decide +kernel
private def yPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm yMap yInvMap yLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin yLeft)
private def yWord : Carrier := g * x * g⁻¹
private theorem yPerm_eq_word : yPerm = (yWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def y : Carrier := ⟨yPerm, yPerm_eq_word.symm ▸ yWord.property⟩

private def rMap (i : Fin 100) : Fin 100 :=
  ⟨(1830790927395945178707283868770265931580633619336262934516955265137503563301917371421632795494123403353404114671296562388274892529542659812533757816023551401253418465480395034876141747041851728015770561797016757 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def rInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3125295502051631258727348161462525128304344946686392921466536045485526982817221282339233739399090969214800014303144976365347554373947351154267435927747263156679029217298420726377170406576317719725172030446135392 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem rLeft : ∀ i, rInvMap (rMap i) = i := by
  apply allFin
  decide +kernel
private def rPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm rMap rInvMap rLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin rLeft)
private def rWord : Carrier := b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b ^ 2) * a * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * (a⁻¹ ^ 2) * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b
private theorem rPerm_eq_word : rPerm = (rWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def r : Carrier := ⟨rPerm, rPerm_eq_word.symm ▸ rWord.property⟩

private theorem x_cube : x ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem xy_commute : x * y = y * x := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem r_inverts_x : r * x * r⁻¹ = x⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem r_fixes_y : r * y = y * r := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private def P : Subgroup Carrier := closure {x, y}
private theorem x_mem : x ∈ P := subset_closure (by simp)
private theorem y_mem : y ∈ P := subset_closure (by simp)
private def normalForm (t : Fin 9) : Carrier := x ^ (t.val % 3) * y ^ (t.val / 3)
private theorem normalForm_mem (t : Fin 9) : normalForm t ∈ P :=
  P.mul_mem (P.pow_mem x_mem _) (P.pow_mem y_mem _)
private def stepX (t : Fin 9) : Fin 9 :=
  ⟨((t.val % 3 + 1) % 3 + 3 * (t.val / 3)) % 9, Nat.mod_lt _ (by decide)⟩
private def stepY (t : Fin 9) : Fin 9 :=
  ⟨(t.val % 3 + 3 * ((t.val / 3 + 1) % 3)) % 9, Nat.mod_lt _ (by decide)⟩
private def stepInvX (t : Fin 9) : Fin 9 :=
  ⟨((t.val % 3 + 2) % 3 + 3 * (t.val / 3)) % 9, Nat.mod_lt _ (by decide)⟩
private def stepInvY (t : Fin 9) : Fin 9 :=
  ⟨(t.val % 3 + 3 * ((t.val / 3 + 2) % 3)) % 9, Nat.mod_lt _ (by decide)⟩

private theorem x_normalForm (t : Fin 9) : x * normalForm t = normalForm (stepX t) := by
  have h : ∀ s : Fin 9, ∀ i : Fin 100,
      (x * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepX s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem y_normalForm (t : Fin 9) : y * normalForm t = normalForm (stepY t) := by
  have h : ∀ s : Fin 9, ∀ i : Fin 100,
      (y * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepY s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem inv_x_normalForm (t : Fin 9) : x⁻¹ * normalForm t = normalForm (stepInvX t) := by
  have h : ∀ s : Fin 9, ∀ i : Fin 100,
      (x⁻¹ * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepInvX s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem inv_y_normalForm (t : Fin 9) : y⁻¹ * normalForm t = normalForm (stepInvY t) := by
  have h : ∀ s : Fin 9, ∀ i : Fin 100,
      (y⁻¹ * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepInvY s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem normalForm_cover {v : Carrier} (hv : v ∈ P) :
    ∃ t : Fin 9, normalForm t = v := by
  induction hv using Subgroup.closure_induction_left with
  | one => exact ⟨0, by simp [normalForm]⟩
  | mul_left a ha b _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases (show a = x ∨ a = y by simpa using ha) with rfl | rfl
    · exact ⟨stepX t, (x_normalForm t).symm⟩
    · exact ⟨stepY t, (y_normalForm t).symm⟩
  | inv_mul_cancel a ha b _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases (show a = x ∨ a = y by simpa using ha) with rfl | rfl
    · exact ⟨stepInvX t, (inv_x_normalForm t).symm⟩
    · exact ⟨stepInvY t, (inv_y_normalForm t).symm⟩

private theorem normalForm_injective : Function.Injective normalForm := by
  have h : ∀ s t : Fin 9,
      (normalForm s : Equiv.Perm (Fin 100)) 0 =
        (normalForm t : Equiv.Perm (Fin 100)) 0 → s = t := by
    apply allFin
    decide +kernel
  intro s t he
  exact h s t (congrArg (fun v : Carrier => (v : Equiv.Perm (Fin 100)) 0) he)

private theorem card_P : Nat.card P = 3 ^ 2 := by
  let f : Fin 9 → P := fun t => ⟨normalForm t, normalForm_mem t⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      exact normalForm_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨t, ht⟩ := normalForm_cover v.property
      exact ⟨t, Subtype.ext ht⟩
  simpa using (Nat.card_eq_of_bijective f hf).symm

/-- A marked Sylow pair and its certified ambient inverter. -/
public theorem exists_configuration :
    ∃ (Q : Sylow 3 Carrier) (x y r : Carrier),
      closure ({x, y} : Set Carrier) = (Q : Subgroup Carrier) ∧
      x ^ 3 = 1 ∧ Commute x y ∧ r * x * r⁻¹ = x⁻¹ ∧ Commute r y := by
  have hi : ¬ 3 ∣ P.index := by
    have h := P.card_mul_index
    rw [card_P, NormalizerIndex.card_carrier] at h
    have he : P.index = 4928000 := by omega
    rw [he]
    decide
  exact ⟨(IsPGroup.of_card card_P).toSylow hi, x, y, r,
    rfl, x_cube, xy_commute, r_inverts_x, r_fixes_y⟩

/-- Apply the marked local configuration to an arbitrary finite perfect central cover. -/
public theorem not_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ 3 ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, r, hQ, hx, hxy, hrx, hry⟩ := exists_configuration
  exact CentralExtension.not_dvd_card_kernel_of_partial_inversion f hf hk
    Q x y r hQ (by decide : Nat.Coprime 3 2) hx hxy hrx hry

end Theory.SpecificGroups.J2HSMultipliers.HS.Three
