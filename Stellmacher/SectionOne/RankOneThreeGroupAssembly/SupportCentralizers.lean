module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaCounting
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaNormalization

/-!
# Support cardinality and odd-core centralizers

The coprime fixed/commutator splitting turns support containment into centralization of the fixed part of the odd core. Multiplication corresponds to exclusive-or, while independent factors give the exact power-of-three commutator count.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- If the commutator support of `B` is contained in that of `A`, then `B`
centralizes the `A`-fixed part of the odd core.  Coprime action makes the
`A`-fixed and `A`-commutator parts disjoint; the commutator of the fixed part
with `B` lies in both. -/
private theorem le_centralizer_oddCore_fixed_of_commutator_le
    {G : Type u} [Group G] [Finite G]
    (S A B : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hAS : A ≤ S) (hBS : B ≤ S) (hAcard : Nat.card A = 2)
    (hWthree : IsPGroup 3 (oddCore G))
    (hWcomm : IsMulCommutative (oddCore G))
    (hcommLe : ⁅oddCore G, B⁆ ≤ ⁅oddCore G, A⁆) :
    B ≤ Subgroup.centralizer
      ((oddCore G ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  let W : Subgroup G := oddCore G
  let C : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G)
  let D : Subgroup G := ⁅W, A⁆
  let hWnormal : W.Normal := by
    dsimp only [W, oddCore]
    exact pPrimeCore_normal
  let _ : W.Normal := hWnormal
  have hAnormW : A ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_of_normal
  let hconj : MulDistribMulAction A W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAnormW
  let _ : MulDistribMulAction A W := hconj
  have hcop : Nat.Coprime (Nat.card A) (Nat.card W) := by
    obtain ⟨n, hn⟩ := hWthree.exists_card_eq
    rw [hAcard, hn]
    exact Nat.Coprime.pow 1 n (by decide : Nat.Coprime 2 3)
  have hcompl : IsCompl (FixedPoints.subgroup A W)
      (commutatorAction A W) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm fun x y => hWcomm.is_comm.comm x y)
      hcop hWcomm
  have hfix : FixedPoints.subgroup A W =
      (subgroupCentralizerIn W A).subgroupOf W :=
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn W A hAnormW
  have hfixMap : (FixedPoints.subgroup A W).map W.subtype = C := by
    rw [hfix, Subgroup.map_subgroupOf_eq_of_le]
    · rfl
    · exact inf_le_left
  have hcommMap : (commutatorAction A W).map W.subtype = D :=
    commutatorAction_subgroup_conj_map_eq_commutator W A hAnormW
  have hdisj : Disjoint C D := by
    rw [← hfixMap, ← hcommMap]
    exact Subgroup.disjoint_map W.subtype_injective hcompl.disjoint
  have hSnormA : S ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs a ha
    have hsa : (s : G) * (a : G) = (a : G) * (s : G) := by
      exact congrArg Subtype.val
        (hS.toIsMulCommutative.is_comm.comm ⟨s, hs⟩ ⟨a, hAS ha⟩)
    rw [hsa]
    simpa [mul_assoc] using ha
  have hSnormCent : S ≤ Subgroup.normalizer
      (Subgroup.centralizer (A : Set G) : Set G) :=
    hSnormA.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (A : Set G))).mp inferInstance)
  have hSnormC : S ≤ Subgroup.normalizer C :=
    (le_inf Subgroup.le_normalizer_of_normal hSnormCent).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcommCLeC : ⁅C, B⁆ ≤ C :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hBS.trans hSnormC)
  have hcommCLeD : ⁅C, B⁆ ≤ D :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans hcommLe
  have hcommBot : ⁅C, B⁆ = ⊥ := by
    apply le_antisymm
    · exact (le_inf hcommCLeC hcommCLeD).trans hdisj.le_bot
    · exact bot_le
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  simpa only [Subgroup.commutator_comm] using hcommBot

/-- Support containment is the character-theoretic form of the commutator
inclusion required by `le_centralizer_oddCore_fixed_of_commutator_le`. -/
public theorem zpowers_le_centralizer_oddCore_fixed_of_support_subset
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hWthree : IsPGroup 3 (oddCore G))
    (a z : S) (hane : a ≠ 1)
    (hsubset : omegaSupport (G := G) (V := V) S hnorm z ⊆
      omegaSupport (G := G) (V := V) S hnorm a) :
    Subgroup.zpowers (z : G) ≤ Subgroup.centralizer
      ((oddCore G ⊓ Subgroup.centralizer
        (Subgroup.zpowers (a : G) : Set G) : Subgroup G) : Set G) := by
  have hAcard : Nat.card (Subgroup.zpowers (a : G)) = 2 := by
    have ha2 : (a : G) ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (hS.exponent_dvd_p) a)
    rw [Nat.card_zpowers, orderOf_eq_prime ha2]
    exact fun ha1 => hane (Subtype.ext ha1)
  have hcommLe : ⁅oddCore G, Subgroup.zpowers (z : G)⁆ ≤
      ⁅oddCore G, Subgroup.zpowers (a : G)⁆ := by
    rw [commutator_oddCore_zpowers_eq_iSup_support
      S hnorm hcoreEq hdecomp z,
      commutator_oddCore_zpowers_eq_iSup_support
        S hnorm hcoreEq hdecomp a]
    refine iSup_le ?_
    intro F
    exact le_iSup (fun K : {K : Subgroup G //
      K ∈ omegaSupport (G := G) (V := V) S hnorm a} =>
        (K : Subgroup G)) ⟨(F : Subgroup G), hsubset F.property⟩
  have hWcomm : IsMulCommutative (oddCore G) := by
    rw [hcoreEq]
    exact oneOmegaGenerated_isMulCommutative hdecomp
  exact le_centralizer_oddCore_fixed_of_commutator_le
    S (Subgroup.zpowers (a : G)) (Subgroup.zpowers (z : G)) hS
      ((Subgroup.zpowers_le).mpr a.property)
      ((Subgroup.zpowers_le).mpr z.property) hAcard hWthree hWcomm hcommLe

/-- Multiplication in the elementary abelian Sylow subgroup acts on omega
supports by symmetric difference.  Each factor character has codomain
`Aut(C3)`, which has order two. -/
public theorem omegaSupport_mul
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (x y : S) (F : Subgroup G) :
    F ∈ omegaSupport (G := G) (V := V) S hnorm (x * y) ↔
      (F ∈ omegaSupport (G := G) (V := V) S hnorm x ∧
        F ∉ omegaSupport (G := G) (V := V) S hnorm y) ∨
      (F ∈ omegaSupport (G := G) (V := V) S hnorm y ∧
        F ∉ omegaSupport (G := G) (V := V) S hnorm x) := by
  classical
  by_cases hF : oneOmega (G := G) (V := V) F
  · rw [mem_omegaSupport_iff S hnorm (x * y) F hF,
      mem_omegaSupport_iff S hnorm x F hF,
      mem_omegaSupport_iff S hnorm y F hF]
    let χ := omegaFactorCharacter S F (hnorm F hF)
    have hcard : Nat.card (MulAut F) = 2 := oneOmega_mulAut_card F hF
    rw [show omegaFactorCharacter S F (hnorm F hF) (x * y) = χ x * χ y by
      exact map_mul χ x y]
    rw [mul_ne_one_iff_exclusive_of_natCard_eq_two hcard]
    simp only [χ, not_ne_iff, and_comm]
  · have hnotmem (z : S) :
        F ∉ omegaSupport (G := G) (V := V) S hnorm z := by
      intro hz
      rw [omegaSupport, Finset.mem_filter] at hz
      exact hF ((mem_oneOmegaFinset_iff (G := G) (V := V) F).mp hz.1)
    simp [hnotmem]

public theorem omegaSupport_mul_eq_symmDiff
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] [DecidableEq (Subgroup G)]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (x y : S) :
    omegaSupport (G := G) (V := V) S hnorm (x * y) =
      omegaSupport (G := G) (V := V) S hnorm x ∆
        omegaSupport (G := G) (V := V) S hnorm y := by
  ext F
  rw [omegaSupport_mul S hnorm x y F]
  simp only [Finset.mem_symmDiff]

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
