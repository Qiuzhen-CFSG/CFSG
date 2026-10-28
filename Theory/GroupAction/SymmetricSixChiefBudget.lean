module
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.BinaryOffender.FixedSubgroupIndex
public import Theory.GroupAction.NoncentralTwoChiefLength
public import Theory.GroupAction.FixedIndexNormalSections
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.GroupAction.SubgroupConjugation

/-!
# A nonabelian chief-factor budget above S₆

For a finite group mapping onto S₆ with a two-group kernel, each noncentral
binary chief factor has fixed index at least four under any actor whose
image contains an even involution. Only each individual chief factor is
linearized. Its irreducible action kills the normal two-kernel; triviality
on A₆ would force the entire irreducible action to be trivial.

The fixed-index inequality for invariant normal sections applies to the
original, possibly nonabelian two-group. Two noncentral chief factors
therefore force index at least sixteen, so index at most eight allows at
most one. All maps, actors and chief quotients remain the literal ones.

Source application: Meierfrankenfeld--Stellmacher (1993), (5.2)(i), printed
p.914, the unique-chief-factor deduction before radius centrality.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace NoncentralChiefRefinement.SymmetricSixBudget
variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem even_nontrivial (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    [IsIrreducible ρ] (hne : ρ ≠ 1) :
    ∃ g : alternatingGroup (Fin 6), ρ g ≠ 1 := by
  by_contra hn
  push Not at hn
  have hk : alternatingGroup (Fin 6) ≤ ρ.ker := fun g hg => hn ⟨g,hg⟩
  let σ := quotientOfLEKer ρ (alternatingGroup (Fin 6)) hk
  let : IsIrreducible σ := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  have hp : IsPGroup 2 ((Equiv.Perm (Fin 6)) ⧸ alternatingGroup (Fin 6)) := by
    have hu : IsPGroup 2 ℤˣ := by
      intro x
      refine ⟨1, ?_⟩
      rcases Int.units_eq_one_or x with rfl | rfl <;> norm_num
    exact hu.of_injective (QuotientGroup.kerLift (Equiv.Perm.sign (α := Fin 6)))
      (QuotientGroup.kerLift_injective _)
  have htriv := normal_p_subgroup_le_ker σ (⊤ : Subgroup _) (hp.to_subgroup ⊤)
  have hs : σ = 1 := MonoidHom.ext (fun g => htriv (mem_top g))
  apply hne
  exact congrArg (fun τ : Representation (ZMod 2) (_ ⧸ alternatingGroup (Fin 6)) V =>
    τ.comp (QuotientGroup.mk' _)) hs

theorem simple_fixedCodim_lower (q : H →* Equiv.Perm (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q) :
    2 ≤ fixedCodim ρ A := by
  have hk : q.ker ≤ ρ.ker := normal_p_subgroup_le_ker ρ q.ker hp
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let σ := (quotientOfLEKer ρ q.ker hk).comp e.symm.toMonoidHom
  have he (h : H) : σ (q h) = ρ h := by
    change quotientOfLEKer ρ q.ker hk (e.symm (q h)) = _
    have hh : e.symm (q h) = QuotientGroup.mk' q.ker h := e.symm_apply_eq.mpr rfl
    rw [hh]
    rfl
  have hcomp : σ.comp q = ρ := MonoidHom.ext he
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q hq σ).mp
    (hcomp ▸ (inferInstance : IsIrreducible ρ))
  have hnσ : σ ≠ 1 := by
    intro hs
    apply hne
    rw [← hcomp, hs]
    rfl
  have hlow := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    σ (even_nontrivial σ hnσ) a ha heven haA
  have hfixed : fixedSpace ρ A = fixedSpace σ (A.map q) := by
    ext v
    constructor
    · intro hv g
      obtain ⟨x,hx,hxg⟩ := g.property
      change σ g.val v = v
      rw [← hxg, he]
      exact hv ⟨x,hx⟩
    · intro hv g
      have ht := hv ⟨q g, mem_map_of_mem q g.property⟩
      change σ (q g) v = v at ht
      rwa [he] at ht
  change 2 ≤ Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ A)
  rw [hfixed]
  exact hlow

section GroupModule
variable {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    [MulDistribMulAction H W] [Nontrivial W]

theorem simple_group_fixedIndex_lower (q : H →* Equiv.Perm (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hirr : ∀ D : Subgroup W, (∀ h : H, ∀ w : W, w ∈ D → h • w ∈ D) →
      D = ⊥ ∨ D = ⊤)
    (hne : ¬ ∀ h : H, ∀ w : W, h • w = w) : 4 ≤ (FixedPoints.subgroup A W).index := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := H) (G := W) (p := 2)
  let : IsIrreducible ρ := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, ?_⟩
    intro U
    let D : Subgroup W := AddSubgroup.toSubgroup' U.toSubmodule.toAddSubgroup
    rcases hirr D (fun h w hw => U.apply_mem_toSubmodule h hw) with hd | hd
    · left
      apply bot_unique
      intro v hv
      have hh : v.toMul ∈ D := hv
      rw [hd, Subgroup.mem_bot] at hh
      exact hh
    · right
      apply top_unique
      intro v _
      have hv : v.toMul ∈ D := by rw [hd]; trivial
      exact hv
  have hnρ : ρ ≠ 1 := by
    intro he
    apply hne
    intro h w
    exact congrArg (fun τ : Representation (ZMod 2) H (Additive W) => τ h (Additive.ofMul w)) he
  have hl := simple_fixedCodim_lower q hq hp ρ hnρ A a ha heven haA
  have hf : fixedSpace (ρ.comp A.subtype) ⊤ = fixedSpace ρ A := by
    ext v
    constructor
    · intro hv g
      exact hv ⟨g, mem_top g⟩
    · intro hv g
      exact hv g.val
  have hc := fixed_subgroup_index (ρ.comp A.subtype)
  rw [fixedCodim, hf] at hc
  have hg : AddSubgroup.toSubgroup' (fixedSpace ρ A).toAddSubgroup =
      FixedPoints.subgroup A W := by
    ext w
    rfl
  rw [hg] at hc
  rw [hc]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl
end GroupModule
end NoncentralChiefRefinement.SymmetricSixBudget

open Subgroup
namespace NoncentralChiefRefinement.SymmetricSixBudget
variable {H : Type*} [Group H] [Finite H]

noncomputable def sectionIndex (A : Subgroup H) (B C : NormalNode H) : ℕ :=
  letI : MulDistribMulAction H (Section B C) :=
    MulDistribMulAction.compHom _ (sectionAction B C)
  (FixedPoints.subgroup A (Section B C)).index

theorem sectionIndex_mul_lower_le (A : Subgroup H) (B C : NormalNode H) (hBC : B ≤ C) :
    sectionIndex A B C * (centralizer (A : Set H)).relIndex B.val ≤
      (centralizer (A : Set H)).relIndex C.val := by
  let N := B.val.subgroupOf C.val
  have hN : IsInvariant A C.val N := ⟨fun a c =>
    mem_normalizer_iff.mp (le_normalizer_of_normal (H := B.val) a.property) c⟩
  let := hN
  let μ : MulDistribMulAction A (C.val ⧸ N) := quotientMulDistribMulAction N hN
  let := μ
  have hi := FixedPoints.quotient_index_mul_kernel_index_le N hN
  have he : (FixedPoints.subgroup A N).index =
      (FixedPoints.subgroup A B.val).index := by
    exact FixedPoints.index_eq_of_equivariant (subgroupOfEquivOfLe hBC)
      (fun a n => rfl)
  have hfix (D : NormalNode H) : FixedPoints.subgroup A D.val =
      (centralizer (A : Set H)).subgroupOf D.val := by
    ext d
    constructor
    · intro hd
      apply mem_centralizer_iff.mpr
      intro a ha
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hd ⟨a,ha⟩))
    · intro hd a
      apply Subtype.ext
      change a.val * d.val * a.val⁻¹ = d.val
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hd a a.property)
  have hs : (FixedPoints.subgroup A (C.val ⧸ N)).index = sectionIndex A B C := by
    let ν : MulDistribMulAction H (Section B C) :=
      MulDistribMulAction.compHom _ (sectionAction B C)
    let := ν
    apply FixedPoints.index_eq_of_equivariant (MulEquiv.refl _)
    intro a x
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective N x
    rfl
  rw [he, hs, hfix B, hfix C] at hi
  exact hi

variable {U : Subgroup H} [U.Normal]

theorem two_noncentral_index_lower (s : SeriesOn U) (A : Subgroup H)
    (hlower : ∀ i, ¬ s.Central i → 4 ≤ sectionIndex A (s.lower i) (s.upper i))
    (i j : Fin s.series.length) (hij : i < j) (hi : ¬ s.Central i) (hj : ¬ s.Central j) :
    16 ≤ (centralizer (A : Set H)).relIndex U := by
  let w (B : Subgroup H) := (centralizer (A : Set H)).relIndex B
  have hmono {B C : Subgroup H} (hBC : B ≤ C) : w B ≤ w C :=
    (centralizer (A : Set H)).relIndex_le_of_le_right hBC
      (Subgroup.FiniteIndex.index_ne_zero (H := (centralizer (A : Set H)).subgroupOf C))
  have hpos (B : Subgroup H) : 1 ≤ w B :=
    Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
      (H := (centralizer (A : Set H)).subgroupOf B))
  have hstep (k : Fin s.series.length) (hk : ¬s.Central k) :
      4 * w (s.lower k).val ≤ w (s.upper k).val :=
    (Nat.mul_le_mul_right _ (hlower k hk)).trans
      (sectionIndex_mul_lower_le A (s.lower k) (s.upper k) (s.series.isChief k).lt.le)
  have h1 : 4 ≤ w (s.upper i).val := by
    have := hstep i hi
    have := hpos (s.lower i).val
    omega
  have h2 : w (s.upper i).val ≤ w (s.lower j).val := by
    apply hmono
    exact s.series.strictMono.monotone (show i.succ ≤ j.castSucc by simpa using hij)
  have h3 := hstep j hj
  have h4 := hmono (s.upper_le j)
  change 16 ≤ w U
  omega

theorem count_le_one_of_index (s : SeriesOn U) (A : Subgroup H)
    (hlower : ∀ i, ¬ s.Central i → 4 ≤ sectionIndex A (s.lower i) (s.upper i))
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8) : s.noncentralCount ≤ 1 := by
  by_contra hn
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  rcases lt_or_gt_of_ne hij with hij | hij
  · have := two_noncentral_index_lower s A hlower i j hij hi hj
    omega
  · have := two_noncentral_index_lower s A hlower j i hij hj hi
    omega
end NoncentralChiefRefinement.SymmetricSixBudget

namespace NoncentralChiefRefinement.SymmetricSixBudget
open Subgroup
variable {H : Type*} [Group H] [Finite H]

/-- An index-eight actor above an even involution of S₆ permits at most one
noncentral chief factor in an arbitrary normal two-subgroup. -/
theorem noncentralCount_le_one (q : H →* Equiv.Perm (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : IsPGroup 2 U)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (s : SeriesOn U) : s.noncentralCount ≤ 1 := by
  apply count_le_one_of_index s A _ hindex
  intro i hi
  let := s.factor_elementary hU i
  let := s.factor_nontrivial i
  let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
  let := μ
  exact simple_group_fixedIndex_lower q hq hp A a ha heven haA
    (s.factor_irreducible i) (fun ht => hi ((s.central_iff_action i).mpr ht))

/-- The source form: the original normal subgroup lies in the literal
normal two-kernel of the S₆ projection. No elementary-abelian premise occurs. -/
theorem noncentralCount_le_one_of_le_ker (q : H →* Equiv.Perm (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (s : SeriesOn U) : s.noncentralCount ≤ 1 :=
  noncentralCount_le_one q hq hp U
    (hp.of_injective (inclusion hU) (inclusion_injective hU)) A a ha heven haA hindex s

/-- The chief-series alternative used in the source: either every factor is
central, or one and only one actual factor is noncentral. -/
theorem central_or_unique_noncentral (q : H →* Equiv.Perm (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : IsPGroup 2 U)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (s : SeriesOn U) : (∀ i, s.Central i) ∨ (∃! i, ¬s.Central i) := by
  have h := noncentralCount_le_one q hq hp U hU A a ha heven haA hindex s
  rcases Nat.eq_zero_or_pos s.noncentralCount with hz | hz
  · exact Or.inl (s.noncentralCount_eq_zero_iff.mp hz)
  · exact Or.inr (s.noncentralCount_eq_one_iff.mp (by omega))
end NoncentralChiefRefinement.SymmetricSixBudget
