module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.FieldTheory.Finiteness

/-!
# Abelian binary MS cores: exponent and conditional model assembly

Write D = [O₂(J),L] and F = C_D(L). A surjective L-equivariant map
D → (F₂³)^m with kernel exactly F is the shared interface for two remaining
local arguments: recognizing the quotient, and controlling its fixed kernel.
Neither the existence of this map nor bounds on m and F are asserted here.

When D is abelian, squares define a homomorphism. An elementary quotient
puts its image in F, so the square map kills [D,L]=D. This proves exponent
two, including for the exceptional central extension of order sixteen.
Equivariance and the three-subgroups identity also show that the intrinsic
O₂(L) centralizes D, without imposing the false ambient centrality shortcut.
Finally |D| = 2^(3m)|F| and a basis of its binary vector space give actual
group models in dimensions 3, 4 and 6 under explicit bounds on m and F.

These are conditional reductions toward Aschbacher–Smith C.1.34(1),(2),(5),
combined manuscript (1 March 2004), printed pp.136–137. They do not replace
the binary MS93/DGS85 quotient recognition or its central-kernel argument.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup
open scoped IsMulCommutative commutatorElement
universe u
variable {J : Type u} [Group J]

/-- The literal subgroup of core elements fixed by conjugation by L. -/
abbrev coreFixed (L : Subgroup J) : Subgroup (commutatorCore L) :=
  (centralizer (L : Set J)).subgroupOf (commutatorCore L)

variable [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J} (h : Input κ L R)

/-- Component conjugation on the actual ambient commutator core. -/
def Input.coreConjugate (l : L) (d : commutatorCore L) : commutatorCore L :=
  ⟨(l : J) * (d : J) * (l : J)⁻¹, by
    let := h.component_normal
    exact (inferInstance : (commutatorCore L).Normal).conj_mem d d.property l⟩

@[simp] theorem Input.coreConjugate_val (l : L) (d : commutatorCore L) :
    (h.coreConjugate l d : J) = (l : J) * (d : J) * (l : J)⁻¹ := by rfl

/-- The component acts on D by its literal ambient conjugation. -/
def Input.coreConjugation : L →* MulAut (commutatorCore L) := by
  let := h.component_normal
  exact (MulAut.conjNormal : J →* MulAut (commutatorCore L)).comp L.subtype

/-- The action homomorphism agrees with the conjugate used by quotient models. -/
@[simp] theorem Input.coreConjugation_apply (l : L) (d : commutatorCore L) :
    h.coreConjugation l d = h.coreConjugate l d := by
  rfl

namespace AbelianCore

/-- An equivariant natural model of D/C_D(L). This is explicit intermediate
proof data, whose existence is not asserted here. The quotient isomorphism
may differ from the input marking, allowing the graph twist that interchanges
the natural and dual modules. All copies use the same marking. -/
structure NaturalQuotient (h : Input κ L R) (m : ℕ) where
  quotientEquiv : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  projection : commutatorCore L →* Multiplicative (Fin m → Fin 3 → ZMod 2)
  surjective : Function.Surjective projection
  kernel : projection.ker = coreFixed L
  equivariant : ∀ (l : L) (d : commutatorCore L) (i : Fin m),
    (projection (h.coreConjugate l d)).toAdd i =
      Representation.specialLinearNatural 3
        (quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ((projection d).toAdd i)

private theorem elementary_of_fixed_squares {G : Type*} [Group G]
    (D L : Subgroup G) [IsMulCommutative D]
    (hn : L ≤ normalizer D) (hgen : ⁅D,L⁆ = D)
    (hsq : ∀ x ∈ D, x ^ 2 ∈ centralizer (L : Set G)) : IsElementaryAbelian 2 D := by
  let K : Subgroup G := ((powMonoidHom 2 : D →* D).ker).map D.subtype
  have hDK : D ≤ K := by
    rw [← hgen]
    apply commutator_le.mpr
    intro x hx l hl
    have hm : ⁅x,l⁆ ∈ D :=
      (le_normalizer_iff_commutator_le_left.mp hn) (commutator_mem_commutator hx hl)
    have hc : x * ⁅x,l⁆ = ⁅x,l⁆ * x :=
      congrArg Subtype.val (mul_comm (⟨x,hx⟩ : D) ⟨⁅x,l⁆, hm⟩)
    have hh : ⁅x^2,l⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hsq x hx) l hl).symm
    have hp : ⁅x,l⁆ ^ 2 = 1 := by
      rwa [pow_two, commutatorElement_mul_left_eq_conj_mul, hc,
        mul_inv_cancel_right, ← pow_two] at hh
    exact ⟨⟨⁅x,l⁆,hm⟩, Subtype.ext hp, rfl⟩
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
  }
  intro x
  obtain ⟨y, hy, he⟩ := hDK x.property
  have heq : y = x := Subtype.ext he
  exact heq ▸ hy

private theorem elementary_model_of_card {G : Type*} [Group G] [Finite G]
    [IsElementaryAbelian 2 G] {d : ℕ} (hc : Nat.card G = 2 ^ d) :
    Nonempty (G ≃* Multiplicative (Fin d → ZMod 2)) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive G) = 2 ^ d := by
    have hs := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    change Nat.card G = _ at hs
    simpa only [Nat.card_zmod, hc] using hs.symm
  have hdim := Nat.pow_right_injective (by decide : 1 < 2) hpow
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hdim).equivFun.toAddEquiv.toMultiplicativeRight⟩

end AbelianCore

include h in
/-- Fixed squares vanish because D is abelian and [D,L]=D. In particular,
a central extension of an elementary group is not silently assumed elementary. -/
theorem Input.abelianCore_elementary_of_fixed_squares
    (hc : IsMulCommutative (commutatorCore L))
    (hsq : ∀ x ∈ commutatorCore L, x ^ 2 ∈ centralizer (L : Set J)) :
    IsElementaryAbelian 2 (commutatorCore L) := by
  let := hc
  let := h.component_normal
  apply AbelianCore.elementary_of_fixed_squares (commutatorCore L) L
    (by rw [normalizer_eq_top]; exact le_top) h.commutatorCore_idempotent hsq

/-- A natural quotient modulo the actual fixed subgroup has elementary core.
The square map lands in that fixed subgroup and kills all core commutators. -/
theorem Input.abelianCore_elementary_of_naturalQuotient
    (hc : IsMulCommutative (commutatorCore L)) {m : ℕ}
    (q : AbelianCore.NaturalQuotient h m) : IsElementaryAbelian 2 (commutatorCore L) := by
  apply h.abelianCore_elementary_of_fixed_squares hc
  intro x hx
  have hs : (⟨x,hx⟩ : commutatorCore L) ^ 2 ∈ q.projection.ker := by
    change q.projection ((⟨x,hx⟩ : commutatorCore L) ^ 2) = 1
    rw [map_pow, pow_two]
    change (q.projection ⟨x,hx⟩).toAdd + (q.projection ⟨x,hx⟩).toAdd = 0
    funext i j
    exact CharTwo.add_self_eq_zero _
  rw [q.kernel] at hs
  exact hs

/-- The intrinsic two-core of L centralizes D once its fixed quotient is
natural. The three-subgroups identity lifts trivial quotient action to D.
This does not claim that the whole ambient O₂(J) centralizes D. -/
theorem Input.abelianCore_componentCore_centralizes_of_naturalQuotient
    (hc : IsMulCommutative (commutatorCore L)) {m : ℕ}
    (q : AbelianCore.NaturalQuotient h m) :
    commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J) := by
  let N := (pCore 2 L).map L.subtype
  have hNL : ⁅N,L⁆ = commutatorCore L := by
    rw [h.commutatorCore_eq_internal, map_commutator,
      ← MonoidHom.range_eq_map, L.range_subtype]
  have hND : ⁅N,commutatorCore L⁆ ≤ centralizer (L : Set J) := by
    apply commutator_le.mpr
    intro n hn d hd
    obtain ⟨nL, hnL, rfl⟩ := hn
    let dD : commutatorCore L := ⟨d,hd⟩
    have heq : q.projection (h.coreConjugate nL dD) = q.projection dD := by
      apply Multiplicative.toAdd.injective
      funext i
      have hn1 : QuotientGroup.mk' (pCore 2 L) nL = 1 :=
        (QuotientGroup.eq_one_iff nL).mpr hnL
      rw [q.equivariant, hn1, map_one, map_one]
      rfl
    have hker : h.coreConjugate nL dD * dD⁻¹ ∈ q.projection.ker := by
      change q.projection (h.coreConjugate nL dD * dD⁻¹) = 1
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    rw [q.kernel] at hker
    exact hker
  have hDN : ⁅⁅commutatorCore L,N⁆,L⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rwa [commutator_comm] at hND
  have hDD : ⁅⁅N,L⁆,commutatorCore L⁆ = ⊥ := by
    rw [hNL]
    exact commutator_self_eq_bot_iff.mpr hc
  have hx := commutator_commutator_eq_bot_of_rotate hDN hDD
  rw [commutator_comm L (commutatorCore L), h.commutatorCore_idempotent] at hx
  exact commutator_eq_bot_iff_le_centralizer.mp hx

/-- The natural quotient marking induces a genuine SL₃(2) action on the
whole abelian core. Triviality of O₂(L) on D is proved above, not an input. -/
noncomputable def AbelianCore.NaturalQuotient.action {m : ℕ} (q : NaturalQuotient h m)
    (hc : IsMulCommutative (commutatorCore L)) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* MulAut (commutatorCore L) :=
  (QuotientGroup.lift (pCore 2 L) h.coreConjugation (by
    intro n hn
    change h.coreConjugation n = 1
    ext d
    change (n : J) * (d : J) * (n : J)⁻¹ = (d : J)
    have hdc := h.abelianCore_componentCore_centralizes_of_naturalQuotient hc q
    rw [hdc d.property n (mem_map_of_mem L.subtype hn), mul_inv_cancel_right])).comp
      q.quotientEquiv.symm.toMonoidHom

/-- The descended action retains the original component-conjugation formula. -/
theorem AbelianCore.NaturalQuotient.action_component {m : ℕ} (q : NaturalQuotient h m)
    (hc : IsMulCommutative (commutatorCore L)) (l : L) (d : commutatorCore L) :
    AbelianCore.NaturalQuotient.action h q hc
        (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) d =
      h.coreConjugate l d := by
  simp only [AbelianCore.NaturalQuotient.action, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact h.coreConjugation_apply l d

/-- Every descended matrix acts on the quotient by the stated natural action. -/
theorem AbelianCore.NaturalQuotient.action_equivariant {m : ℕ} (q : NaturalQuotient h m)
    (hc : IsMulCommutative (commutatorCore L))
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (d : commutatorCore L) (i : Fin m) :
    (q.projection (AbelianCore.NaturalQuotient.action h q hc g d)).toAdd i =
      Representation.specialLinearNatural 3 g ((q.projection d).toAdd i) := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
  have he : q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
    rw [hl, MulEquiv.apply_symm_apply]
  rw [← he, q.action_component]
  exact q.equivariant l d i

/-- Exact order of D from a surjective natural model and its literal kernel. -/
theorem AbelianCore.NaturalQuotient.card {m : ℕ} (q : NaturalQuotient h m) :
    Nat.card (commutatorCore L) = 2 ^ (3 * m) * Nat.card (coreFixed L) := by
  have hindex : q.projection.ker.index = Nat.card (Multiplicative (Fin m → Fin 3 → ZMod 2)) := by
    rw [index_ker, q.projection.range_eq_top_of_surjective q.surjective, Nat.card_congr topEquiv.toEquiv]
  have hs := index_mul_card q.projection.ker
  rw [hindex, q.kernel] at hs
  have hmodel : Nat.card (Multiplicative (Fin m → Fin 3 → ZMod 2)) = 2 ^ (3 * m) := by
    change Nat.card (Fin m → Fin 3 → ZMod 2) = _
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_mul]
  rw [hmodel] at hs
  exact hs.symm

/-- Conditional assembly of the abelian elementary models. The natural
quotient and the two fixed-kernel bounds are still independent proof obligations;
this theorem does not assert the abelian branch of C.1.34. -/
theorem Input.abelianCore_model_of_naturalQuotient
    (hc : IsMulCommutative (commutatorCore L)) {m : ℕ}
    (q : AbelianCore.NaturalQuotient h m) (hm : m = 1 ∨ m = 2)
    (hfixed : Nat.card (coreFixed L) ≤ 2)
    (hdouble : m = 2 → Nat.card (coreFixed L) = 1) :
    ∃ d : ℕ, (d = 3 ∨ d = 4 ∨ d = 6) ∧
      Nonempty (commutatorCore L ≃* Multiplicative (Fin d → ZMod 2)) := by
  let := h.abelianCore_elementary_of_naturalQuotient hc q
  have hc := q.card
  rcases hm with rfl | rfl
  · have hp : 0 < Nat.card (coreFixed L) := Nat.card_pos
    have hd : Nat.card (coreFixed L) = 1 ∨ Nat.card (coreFixed L) = 2 := by omega
    rcases hd with hd | hd
    · refine ⟨3, Or.inl rfl, AbelianCore.elementary_model_of_card ?_⟩
      simpa [hd] using hc
    · refine ⟨4, Or.inr (Or.inl rfl), AbelianCore.elementary_model_of_card ?_⟩
      simpa [hd] using hc
  · refine ⟨6, Or.inr (Or.inr rfl), AbelianCore.elementary_model_of_card ?_⟩
    simpa [hdouble rfl] using hc

end CFSG.Quasithin.ChapterC.BinaryMS
