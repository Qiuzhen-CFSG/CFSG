module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineTensor
public import Theory.GroupTheory.PrimeRankZero

/-!
# Excluding the original doubled six-letter action

The second projection of an irreducible tensor action cannot be a two-group:
a fixed vector in its two-dimensional factor would give a proper invariant
four-space. Thus its S₃ projection contains a cubic. Squaring a lift and
removing its marked A₆ coordinate constructs a pure cubic in the image.
The actual A₆ × C₃ subgroup then has three-rank at least three, contradicting
the source bound inherited by H/O₂(H) from its original SQTK cover.

This uses the literal ambient embedding and never infers action recognition
from group orders. It closes the six-letter row of the marked fixed-line
constituent reduction. Source: Aschbacher--Smith G.11.7--8 and 14.4.2,
printed pp.366--368,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSix
open BinaryPermutation
variable {D W U : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem second_not_two_group {n : ℕ}
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin n)) U)
    (hd : finrank (ZMod 2) U = 4)
    (j : D →* Equiv.Perm (Fin n) × Equiv.Perm (Fin 3))
    (t : W ≃ₗ[ZMod 2] (U ⊗[ZMod 2] core (Fin 3)))
    (ht : ∀ a w, t (ρ a w) = ThreeTensor.action σ (j a) (t w)) :
    ¬ IsPGroup 2 ((MonoidHom.snd _ _).comp j).range := by
  intro hp
  let K := ((MonoidHom.snd _ _).comp j).range
  have hn : (⊤ : Submodule (ZMod 2) (core (Fin 3))) ≠ ⊥ := by
    have hh : finrank (ZMod 2) (core (Fin 3)) = 2 := by
      rw [finrank_core]; norm_num
    intro he
    have hh0 := congrArg (fun S : Submodule (ZMod 2) (core (Fin 3)) => finrank (ZMod 2) S) he
    simp only [finrank_top,finrank_bot] at hh0
    omega
  obtain ⟨z,_,hz,hzf⟩ := PermutedSupports.exists_nonzero_fixed (coreRepresentation (Fin 3))
    K hp ⊤ hn (le_subspaceStabilizer _ _ (by intro a ha w hw; trivial))
  have hzf' (a : D) : coreRepresentation (Fin 3) (j a).2 z = z := hzf ⟨_,⟨a,rfl⟩⟩
  let b : U →ₗ[ZMod 2] U ⊗[ZMod 2] core (Fin 3) :=
    (TensorProduct.mk (ZMod 2) U (core (Fin 3))).flip z
  let f : IntertwiningMap (σ.comp ((MonoidHom.fst _ _).comp j)) ρ := {
    toLinearMap := t.symm.toLinearMap.comp b
    isIntertwining' := by
      intro a
      ext u
      apply t.injective
      change t (t.symm (σ (j a).1 u ⊗ₜ[ZMod 2] z)) = t (ρ a (t.symm (u ⊗ₜ[ZMod 2] z)))
      rw [t.apply_symm_apply,ht,t.apply_symm_apply,ThreeTensor.action_tmul,hzf'] }
  have hw : finrank (ZMod 2) W = 8 := by
    rw [t.finrank_eq,Module.finrank_tensorProduct,hd,finrank_core]
    norm_num
  have hf : f = 0 := (IsIrreducible.surjective_or_eq_zero f).resolve_left (by
    intro hs
    have hb := LinearMap.finrank_le_finrank_of_surjective hs
    change finrank (ZMod 2) W ≤ finrank (ZMod 2) U at hb
    omega)
  have hzval : ∃ i, z.val i ≠ 0 := by
    by_contra! hh
    exact hz (Subtype.ext (funext hh))
  obtain ⟨i,hi⟩ := hzval
  have hi1 : z.val i = 1 := by
    have hh : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact hh _ hi
  let q : (U ⊗[ZMod 2] core (Fin 3)) →ₗ[ZMod 2] U :=
    (TensorProduct.rid (ZMod 2) U).toLinearMap.comp
      (TensorProduct.map LinearMap.id ((LinearMap.proj i).comp (core (Fin 3)).subtype))
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨u,hu⟩ := exists_ne (0 : U)
  have hf0 : t.symm (u ⊗ₜ[ZMod 2] z) = 0 := congrArg (fun a : IntertwiningMap
    (σ.comp ((MonoidHom.fst _ _).comp j)) ρ => a u) hf
  have ht0 : u ⊗ₜ[ZMod 2] z = 0 := by
    have hh := congrArg t hf0
    simpa only [t.apply_symm_apply,map_zero] using hh
  have hq := congrArg q ht0
  change z.val i • u = 0 at hq
  rw [hi1,one_smul] at hq
  exact hu hq

omit [FiniteDimensional (ZMod 2) W] in
private theorem six_three_rank
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (H : Subgroup D)
    (hm : FixedLineActions.PermutationTensorEmbedding ρ H
      (naturalRepresentation (Fin 6))) : 3 ≤ primeRank 3 D := by
  obtain ⟨e,j,t,hj,ht,hmark⟩ := hm
  let K := ((MonoidHom.snd _ _).comp j).range
  have hn := second_not_two_group ρ (naturalRepresentation (Fin 6))
    (by simpa using finrank_natural_even (Fin 6) (by decide)) j t ht
  have hex : ∃ a : D, (j a).2 ^ 3 = 1 ∧ (j a).2 ≠ 1 := by
    by_contra! hh
    apply hn
    intro k
    refine ⟨1,?_⟩
    apply Subtype.ext
    change k.val ^ 2 = 1
    obtain ⟨a,hka⟩ := k.property
    change (j a).2 = k.val at hka
    rw [← hka]
    have hsmall : ∀ s : Equiv.Perm (Fin 3), s ^ 2 = 1 ∨ (s ^ 3 = 1 ∧ s ≠ 1) := by
      decide +kernel
    exact (hsmall (j a).2).resolve_right (fun he => he.2 (hh a he.1))
  obtain ⟨a,ha3,ha1⟩ := hex
  let s := (j a).2 ^ 2
  have hs3 : s ^ 3 = 1 := by
    rw [show s ^ 3 = ((j a).2 ^ 3) ^ 2 by simp only [s,← pow_mul],ha3,one_pow]
  have hs1 : s ≠ 1 := by
    intro he
    have ho := orderOf_dvd_of_pow_eq_one ha3
    have ht := orderOf_dvd_of_pow_eq_one he
    have hh := Nat.dvd_gcd ho ht
    norm_num at hh
    exact ha1 hh
  have hpure : (1,s) ∈ j.range := by
    have heven : (j a).1 ^ 2 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_pow]
      exact Int.units_sq _
    obtain ⟨b,hb⟩ := e.surjective ⟨(j a).1 ^ 2,heven⟩
    refine ⟨(b : D)⁻¹ * a^2,?_⟩
    rw [map_mul,map_inv,map_pow,hmark,hb]
    exact Prod.ext (inv_mul_cancel _) (one_mul _)
  let C := zpowers s
  have hC : ∀ c : C, (1,c.val) ∈ j.range := by
    intro c
    obtain ⟨i,hi⟩ := c.property
    have hp : ((1 : Equiv.Perm (Fin 6)),s) ^ i = (1,c.val) := by
      apply Prod.ext
      · simp
      · exact hi
    rw [← hp]
    exact j.range.zpow_mem hpure i
  let k : alternatingGroup (Fin 6) × C →* Equiv.Perm (Fin 6) × Equiv.Perm (Fin 3) :=
    (alternatingGroup (Fin 6)).subtype.prodMap C.subtype
  have hk : Function.Injective k := by
    intro a b he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  let f : alternatingGroup (Fin 6) × C →* j.range := k.codRestrict j.range (by
    rintro ⟨b,c⟩
    obtain ⟨d,hd⟩ := e.surjective b
    have hb : (b.val,1) ∈ j.range := ⟨d,(hmark d).trans (by rw [hd])⟩
    exact j.range.mul_mem hb (hC c))
  have hf : Function.Injective f := by
    intro a b he
    exact hk (congrArg Subtype.val he)
  have hle := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have heq : primeRank 3 j.range = primeRank 3 D :=
    (Theory.GroupTheory.primeRank_equiv 3 (MonoidHom.ofInjective hj)).symm
  have hca : Nat.card C = 3 := by rw [Nat.card_zpowers,orderOf_eq_prime hs3 hs1]
  have hc : 1 ≤ primeRank 3 C := by
    have hh := (PrimeRank.eq_zero_iff_not_dvd_card (G := C) (p := 3))
    by_contra hn
    have hz : primeRank 3 C = 0 := by omega
    exact hh.mp hz (by rw [hca])
  rw [primeRank_prod_eq_add,heq,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide)] at hle
  norm_num at hle
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSix

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual six-letter tensor embedding contradicts the original odd-rank
bound. Irreducibility forces a pure cubic in its second factor. -/
theorem source_six_tensor_embedding_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (H : Subgroup F.TerminalHdot)
    (hm : FixedLineActions.PermutationTensorEmbedding F.terminalRepresentation H
      (BinaryPermutation.naturalRepresentation (Fin 6))) : False := by
  let := chosen.elementary
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  let := hyp.irreducible_of_not_solvable hns
  have hl := FixedLineSix.six_three_rank F.terminalRepresentation H hm
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have htwo : IsPGroup 2 F.terminalHatAction.ker := hk ▸ pCore_isPGroup
  have hu : primeRank 3 F.TerminalHdot ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ htwo).trans
      ((Chapter14.Section03.NonabelianSource.Recognition.pointNormalizer_sqtk
        d.qtke F (by decide)).stronglyQuasithin 3 Nat.prime_three (by decide))
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
