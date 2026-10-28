module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Automizer transport and the non-FF obstruction

The image of an elementary abelian subgroup `A ≤ N_G(V)` in `Aut_G(V)`
has rank `m(A/C_A(V))`, and its fixed-space codimension on `V` is
`m(V/C_V(A))`. We identify the kernel with the relative centralizer and
identify the fixed vectors with `C_V(A)` before comparing these ranks.

An ambient group automorphism induces both a multiplicative equivalence of
actual automizers and an equivariant linear equivalence of their binary
modules. Thus the FF condition and the parameters `m` and `s` are invariant
under conjugation. Under mutual normalization, absence of offenders on both
conjugate modules would give two opposing strict inequalities. This proves
E.3.11 without invoking centralizer rigidity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.11,
printed p. 232 (PDF p. 243). The rank bridges also support E.3.10.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE

variable {G : Type*} [Group G]

/-- The induced action is trivial precisely when the acting subgroup centralizes `V`. -/
theorem inducedAutomizer_eq_bot_iff {V A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) :
    inducedAutomizer V A = ⊥ ↔ A ≤ centralizer (V : Set G) := by
  rw [inducedAutomizer, Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict,
    Subgroup.normalizerMonoidHom_ker]
  constructor
  · intro h a ha
    exact h (show (⟨a, hA ha⟩ : normalizer (V : Set G)) ∈ A.subgroupOf _ from ha)
  · intro h a ha
    exact h ha

/-- An elementary abelian actor has an elementary abelian image in the automizer. -/
theorem inducedAutomizer_elementary (V A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (V : Set G)) :
    IsElementaryAbelian 2 (inducedAutomizer V A) := by
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hA
  exact IsElementaryAbelian.map _

/-- The rank of the induced image is the binary logarithm of `|A : C_A(V)|`. -/
theorem rank_inducedAutomizer (V A : Subgroup G)
    (hA : A ≤ normalizer (V : Set G)) :
    rank (inducedAutomizer V A) = subgroupCorank A (A ⊓ centralizer (V : Set G)) := by
  unfold rank inducedAutomizer subgroupCorank
  rw [← Subgroup.relIndex_ker, MonoidHom.ker_rangeRestrict,
    Subgroup.normalizerMonoidHom_ker, Subgroup.relIndex_subgroupOf hA,
    Subgroup.inf_relIndex_left]

/-- Fixed vectors of the induced image are exactly the elements of `C_V(A)`. -/
theorem mem_fixedSpace_inducedAutomizer (V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hA : A ≤ normalizer (V : Set G)) (v : Additive V) :
    v ∈ fixedSpace (automizerRepresentation V) (inducedAutomizer V A) ↔
      (v.toMul : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro h a ha
    have hv := h ⟨V.normalizerMonoidHom.rangeRestrict ⟨a, hA ha⟩,
      ⟨⟨a, hA ha⟩, ha, rfl⟩⟩
    have hv' : a * (v.toMul : G) * a⁻¹ = (v.toMul : G) :=
      congrArg (fun w : Additive V => (w.toMul : G)) hv
    exact mul_inv_eq_iff_eq_mul.mp hv'
  · intro h a
    obtain ⟨b, hb, hab⟩ := a.property
    change automizerRepresentation V (a : Automizer V) v = v
    rw [← hab]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (b : G) * (v.toMul : G) * (b : G)⁻¹ = (v.toMul : G)
    rw [h b hb, mul_inv_cancel_right]

/-- The actual bijection between fixed vectors and the relative centralizer in `V`. -/
noncomputable def fixedSpaceCentralizerEquiv (V A : Subgroup G)
    [IsElementaryAbelian 2 V] (hA : A ≤ normalizer (V : Set G)) :
    fixedSpace (automizerRepresentation V) (inducedAutomizer V A) ≃
      (centralizer (A : Set G)).subgroupOf V where
  toFun v := ⟨v.val.toMul, (mem_fixedSpace_inducedAutomizer V A hA v.val).mp v.property⟩
  invFun v := ⟨Additive.ofMul v.val,
    (mem_fixedSpace_inducedAutomizer V A hA _).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fixed codimension agrees with the source quotient rank `m(V/C_V(A))`. -/
theorem fixedCodim_inducedAutomizer [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] (hA : A ≤ normalizer (V : Set G)) :
    fixedCodim (automizerRepresentation V) (inducedAutomizer V A) =
      subgroupCorank V (V ⊓ centralizer (A : Set G)) := by
  let C := (centralizer (A : Set G)).subgroupOf V
  let F := fixedSpace (automizerRepresentation V) (inducedAutomizer V A)
  have hc : Nat.card F = Nat.card C := Nat.card_congr (fixedSpaceCentralizerEquiv V A hA)
  have h1 := Submodule.card_eq_card_quotient_mul_card F
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hq : Nat.card (Additive V ⧸ F) = Nat.card (V ⧸ C) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
    calc
      _ = Nat.card (Additive V) := by rw [← hc, mul_comm, ← h1]
      _ = Nat.card V := rfl
      _ = _ := h2
  have hv := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V ⧸ F)
  rw [Nat.card_zmod] at hv
  unfold subgroupCorank
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex, Subgroup.index_eq_card, ← hq, hv,
    Nat.log_pow (by decide)]
  rfl

private theorem automizer_map_eq (V : Subgroup G) (e : G ≃* G) :
    (V.normalizerMonoidHom.range).map (MulAut.congr (e.subgroupMap V)).toMonoidHom =
      (V.map e.toMonoidHom).normalizerMonoidHom.range := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨⟨e n, le_normalizer_map e.toMonoidHom ⟨n, n.property, rfl⟩⟩, ?_⟩
    ext v
    change e (n : G) * (v : G) * (e (n : G))⁻¹ =
      e ((n : G) * e.symm (v : G) * (n : G)⁻¹)
    simp only [map_mul, map_inv, e.apply_symm_apply]
  · rintro _ ⟨n, rfl⟩
    have hn : e.symm (n : G) ∈ normalizer (V : Set G) := by
      have : (n : G) ∈ (normalizer (V : Set G)).map e.toMonoidHom := by
        rw [Subgroup.map_equiv_normalizer_eq]
        exact n.property
      obtain ⟨x, hx, hx'⟩ := this
      rw [← hx']
      change e.symm (e x) ∈ normalizer (V : Set G)
      rw [e.symm_apply_apply]
      exact hx
    refine ⟨V.normalizerMonoidHom ⟨e.symm n, hn⟩, ⟨⟨e.symm n, hn⟩, rfl⟩, ?_⟩
    ext v
    change e (e.symm (n : G) * e.symm (v : G) * (e.symm (n : G))⁻¹) =
      (n : G) * (v : G) * (n : G)⁻¹
    simp only [map_mul, map_inv, e.apply_symm_apply]

/-- An ambient automorphism transports the actual image of the normalizer action. -/
noncomputable def automizerMapEquiv (V : Subgroup G) (e : G ≃* G) :
    Automizer V ≃* Automizer (V.map e.toMonoidHom) :=
  ((MulAut.congr (e.subgroupMap V)).subgroupMap _).trans
    (MulEquiv.subgroupCongr (automizer_map_eq V e))

/-- The automizer equivalence intertwines conjugation on the two subgroup types. -/
theorem automizerMapEquiv_apply (V : Subgroup G) (e : G ≃* G)
    (a : Automizer V) (v : V) :
    (automizerMapEquiv V e a).val (e.subgroupMap V v) = e.subgroupMap V (a.val v) := by
  change e.subgroupMap V (a.val ((e.subgroupMap V).symm (e.subgroupMap V v))) = _
  rw [MulEquiv.symm_apply_apply]
end CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.ChapterE.AutomizerFF
variable {X Y W Z : Type*} [Group X] [Group Y]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup Z] [Module (ZMod 2) Z]
variable (ρ : Representation (ZMod 2) X W) (σ : Representation (ZMod 2) Y Z)
  (e : X ≃* Y) (f : W ≃ₗ[ZMod 2] Z)
  (he : ∀ x w, f (ρ x w) = σ (e x) (f w))

include he

private theorem fixedSpace_map :
    ∀ A : Subgroup X, (fixedSpace ρ A).map f.toLinearMap =
      fixedSpace σ (A.map e.toMonoidHom) := by
  intro A
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩ b
    obtain ⟨a, ha, hab⟩ := b.property
    change σ (b : Y) (f w) = f w
    rw [← hab]
    change σ (e a) (f w) = f w
    rw [← he]
    exact congrArg f (hw ⟨a, ha⟩)
  · intro hz
    refine ⟨f.symm z, ?_, f.apply_symm_apply z⟩
    intro a
    apply f.injective
    change f (ρ (a : X) (f.symm z)) = f (f.symm z)
    rw [he, f.apply_symm_apply]
    exact hz ⟨e a, ⟨a, a.property, rfl⟩⟩

private theorem fixedCodim_map [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) Z]
    (A : Subgroup X) : fixedCodim σ (A.map e.toMonoidHom) = fixedCodim ρ A := by
  have hd := f.finrank_eq
  have hf := f.finrank_map_eq (fixedSpace ρ A)
  rw [fixedSpace_map ρ σ e f he A] at hf
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank σ (A.map e.toMonoidHom)
  omega

private theorem isFFModule_transfer [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) Z]
    (h : IsFFModule ρ) : IsFFModule σ := by
  obtain ⟨A, hA, hineq⟩ := h
  let _ : IsElementaryAbelian 2 A := hA.2
  refine ⟨A.map e.toMonoidHom, ⟨?_, IsElementaryAbelian.map _⟩, ?_⟩
  · exact fun h => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A e.injective).mp h)
  · rw [fixedCodim_map ρ σ e f he, rank,
      Subgroup.card_map_of_injective e.injective]
    exact hineq

private theorem isFFModule_iff [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) Z] :
    IsFFModule ρ ↔ IsFFModule σ := by
  refine ⟨isFFModule_transfer ρ σ e f he, isFFModule_transfer σ ρ e.symm f.symm ?_⟩
  intro y z
  apply f.injective
  simp only [f.apply_symm_apply, he, e.apply_symm_apply]

private theorem moduleM_eq [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) Z] :
    moduleM ρ = moduleM σ := by
  unfold moduleM
  congr 1
  rw [f.finrank_eq]
  congr 1
  ext n
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨e t, ?_, ?_⟩
    · simpa only [e.orderOf_eq] using ht
    · simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] using
        fixedCodim_map ρ σ e f he (Subgroup.zpowers t)
  · rintro ⟨t, ht, rfl⟩
    refine ⟨e.symm t, ?_, ?_⟩
    · simpa only [e.symm.orderOf_eq] using ht
    · have h := fixedCodim_map ρ σ e f he (Subgroup.zpowers (e.symm t))
      rw [MonoidHom.map_zpowers] at h
      simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using h.symm
end CFSG.Quasithin.ChapterE.AutomizerFF

namespace CFSG.Quasithin.ChapterE

variable {G : Type*} [Group G]
variable (V : Subgroup G) [IsElementaryAbelian 2 V] (e : G ≃* G)
  [IsElementaryAbelian 2 (V.map e.toMonoidHom)]

/-- The binary linear equivalence induced by the ambient automorphism on `V`. -/
noncomputable def automizerModuleEquiv :
    Additive V ≃ₗ[ZMod 2] Additive (V.map e.toMonoidHom) := by
  let f : Additive V →+ Additive (V.map e.toMonoidHom) :=
    (e.subgroupMap V).toMonoidHom.toAdditive
  exact LinearEquiv.ofBijective (f.toZModLinearMap 2) (e.subgroupMap V).bijective

/-- The actual automizer representations are equivariant for the two equivalences. -/
theorem automizerRepresentation_equivariant (a : Automizer V) (v : Additive V) :
    automizerModuleEquiv V e (automizerRepresentation V a v) =
      automizerRepresentation (V.map e.toMonoidHom) (automizerMapEquiv V e a)
        (automizerModuleEquiv V e v) := by
  exact congrArg Additive.ofMul (automizerMapEquiv_apply V e a v.toMul).symm

/-- The genuine offender definition, and hence the FF condition, is invariant. -/
theorem automizer_isFFModule_map_equiv [Finite G] :
    IsFFModule (automizerRepresentation (V.map e.toMonoidHom)) ↔
      IsFFModule (automizerRepresentation V) :=
  (AutomizerFF.isFFModule_iff _ _ (automizerMapEquiv V e) (automizerModuleEquiv V e)
    (automizerRepresentation_equivariant V e)).symm

/-- The local involution fixed-space parameter is invariant under ambient automorphisms. -/
theorem localM_map_equiv [Finite G] : localM (V.map e.toMonoidHom) = localM V :=
  (AutomizerFF.moduleM_eq _ _ (automizerMapEquiv V e) (automizerModuleEquiv V e)
    (automizerRepresentation_equivariant V e)).symm

/-- The combined parameter `s = min(r,m)` is invariant under ambient automorphisms. -/
theorem globalS_map_equiv [Finite G] : globalS (V.map e.toMonoidHom) = globalS V := by
  simp only [globalS, globalR_map_equiv, localM_map_equiv]
end CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.ChapterE

variable {G : Type*} [Group G]

/-- A nontrivial commutator forces a nontrivial induced automizer. -/
theorem inducedAutomizer_ne_bot_of_commutator_ne_bot {V A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hVA : ⁅V, A⁆ ≠ ⊥) :
    inducedAutomizer V A ≠ ⊥ := by
  intro h
  apply hVA
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mpr ((inducedAutomizer_eq_bot_iff hA).mp h))

/-- On a non-FF module, every nontrivial elementary abelian action has image rank
strictly smaller than its fixed codimension. -/
theorem centralizerCorank_lt_of_not_isFFModule [Finite G]
    (V A : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hA : A ≤ normalizer (V : Set G)) (hVA : ⁅V, A⁆ ≠ ⊥) :
    subgroupCorank A (A ⊓ centralizer (V : Set G)) <
      subgroupCorank V (V ⊓ centralizer (A : Set G)) := by
  rw [← rank_inducedAutomizer V A hA, ← fixedCodim_inducedAutomizer V A hA]
  apply Nat.lt_of_not_ge
  intro h
  exact hFF ⟨inducedAutomizer V A,
    ⟨inducedAutomizer_ne_bot_of_commutator_ne_bot hA hVA,
      inducedAutomizer_elementary V A hA⟩, h⟩

/-- Aschbacher–Smith E.3.11: a noncentralizing conjugate of a non-FF internal
module cannot normalize it mutually. The nontriviality of `V` from the source
setup already follows from the nontrivial commutator hypothesis. -/
theorem lemma_E_3_11 [Finite G] (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g : G) (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  intro hV
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hFFW : ¬ IsFFModule (automizerRepresentation W) := by
    intro h
    exact hFF ((automizer_isFFModule_map_equiv V (MulAut.conj g)).mp h)
  have h1 := centralizerCorank_lt_of_not_isFFModule V W hFF hg hcomm
  have h2 := centralizerCorank_lt_of_not_isFFModule W V hFFW hV
    (by rwa [commutator_comm])
  exact Nat.lt_asymm h1 h2
end CFSG.Quasithin.ChapterE
