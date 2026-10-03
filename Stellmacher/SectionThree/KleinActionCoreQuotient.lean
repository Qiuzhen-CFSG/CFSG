module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Data.Fintype.Perm

/-!
# Recognizing the core quotient from a Klein-four action

Let G be finite with a Sylow two-subgroup of order 128 and two-core of order
64. A homomorphism from G to the automorphism group of a Klein four group
whose kernel is precisely the two-core identifies the actual core quotient
with the symmetric group on three letters.

The action on the three nonidentity elements is faithful modulo the given
kernel. Lagrange's theorem makes the quotient order divide six; the Sylow
and core orders make it even. Order two would make G a two-group, forcing
its two-core to be all of G and contradicting the given orders. The action
therefore has order six and is onto the permutation group.

This supplies the final faithful-action step for the terminal core quotient
in Stellmacher (9.1), Journal of Algebra 190 (1997), p.48. The kernel equality
is an explicit input, supplied separately by the normal elementary-eight
argument; no local classification conclusion is assumed here.
-/

open scoped IsKleinFour

namespace Stellmacher.SectionThree

/-- A Klein-four action with kernel the two-core gives the actual S₃ quotient
when the Sylow two-subgroup has twice the order of the core. -/
public theorem quotient_s3_of_klein_action_kernel_eq_pCore
    {G W : Type*} [Group G] [Finite G] [Group W] [IsKleinFour W]
    (P : Sylow 2 G) (hP : Nat.card P = 128)
    (hQ : Nat.card (pCore 2 G) = 64)
    (ρ : G →* MulAut W) (hker : ρ.ker = pCore 2 G) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  classical
  let Q := pCore 2 G
  let _ := Fintype.ofFinite W
  let _ := MulDistribMulAction.compHom W ρ
  let points : SubMulAction G W := {
    carrier := ({1} : Set W)ᶜ
    smul_mem' := by
      intro g point hpoint
      change ρ g point ≠ 1
      exact fun heq => hpoint ((ρ g).injective
        (heq.trans (map_one (ρ g)).symm)) }
  let action : G →* Equiv.Perm points := MulAction.toPermHom G points
  have hkernel : action.ker = Q := by
    change action.ker = pCore 2 G
    rw [← hker]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hfix
      apply MulEquiv.ext
      intro w
      by_cases hw : w = 1
      · simp [hw]
      · exact congrArg (fun x : points => (x : W))
          (Equiv.congr_fun hfix ⟨w, hw⟩)
    · intro hfix
      ext w
      change ρ g (w : W) = (w : W)
      rw [hfix]
      rfl
  have hpoints : Nat.card points = 3 := by
    change Nat.card ↥(({1} : Set W)ᶜ) = 3
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    simp
  have hperm : Nat.card (Equiv.Perm points) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hpoints]
    decide
  let quotientAction := QuotientGroup.lift Q action hkernel.symm.le
  have hinjective : Function.Injective quotientAction :=
    (QuotientGroup.injective_lift_iff Q action hkernel.symm.le).mpr hkernel.symm
  have hdiv : Nat.card (G ⧸ Q) ∣ 6 := by
    rw [← hperm]
    exact Subgroup.card_dvd_of_injective quotientAction hinjective
  have horder : 64 * Nat.card (G ⧸ Q) = Nat.card G := by
    have hc := Q.card_mul_index
    rwa [Subgroup.index_eq_card, hQ] at hc
  have heven : 2 ∣ Nat.card (G ⧸ Q) := by
    have hpdiv := P.toSubgroup.card_subgroup_dvd_card
    rw [hP, ← horder] at hpdiv
    obtain ⟨k, hk⟩ := hpdiv
    exact ⟨k, by omega⟩
  have hnotTwo : Nat.card (G ⧸ Q) ≠ 2 := by
    intro htwo
    have hG : Nat.card G = 128 := by omega
    have hpG : IsPGroup 2 G := IsPGroup.of_card (n := 7) (by simpa using hG)
    have htop : (⊤ : Subgroup G) ≤ pCore 2 G :=
      le_sSup ⟨inferInstance, hpG.to_subgroup ⊤⟩
    have heq : Q = ⊤ := top_le_iff.mp htop
    have hcQ : Nat.card Q = Nat.card G := by rw [heq, Nat.card_congr Subgroup.topEquiv.toEquiv]
    change Nat.card Q = 64 at hQ
    omega
  have hcard : Nat.card (G ⧸ Q) = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hdiv
    interval_cases h : Nat.card (G ⧸ Q) <;> simp_all
  let pointEquiv : points ≃ Fin 3 :=
    (Finite.equivFin points).trans (finCongr hpoints)
  exact ⟨(MulEquiv.ofBijective quotientAction
    ((Nat.bijective_iff_injective_and_card quotientAction).mpr
      ⟨hinjective, hcard.trans hperm.symm⟩)).trans (Equiv.permCongrHom pointEquiv)⟩

end Stellmacher.SectionThree
