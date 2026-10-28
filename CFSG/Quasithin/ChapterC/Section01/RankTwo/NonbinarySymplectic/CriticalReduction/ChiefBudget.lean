module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.NaturalRecognition
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.SmallCodimension
public import Theory.GroupAction.SymmetricSixChiefBudget

/-!
# A nonbinary symplectic chief-factor budget

An elementary actor of image order at least q² has fixed index at least q²
on every noncentral binary chief factor. A contrary factor would be an
FF-module; the proved Chapter B classification and the original symplectic
order identify the literal natural action, where small codimension forces
root rank at most the field degree. Irreducibility kills the normal
two-kernel. The fixed-index inequality for normal sections therefore
excludes two noncentral factors under a q³ budget, without requiring the
whole radius or its seed quotient to be abelian.

`RadiusChief` applies the bound to the actual characteristic replacement.
Source: Meierfrankenfeld--Stellmacher (1993), (1.4) and (5.2)(i), p.914.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {G F W : Type*} [Group G] [Finite G] [IsSimpleGroup G] [IsQuasisimple G]
  [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [CharP F 2] in
/-- A large elementary actor moves at least q² vectors on each nontrivial
irreducible binary module for the nonbinary symplectic group. -/
theorem irreducible_large_actor_fixedCodim_ge
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hG : Nat.card G = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hlarge : 2*n ≤ rank A) :
    2*n ≤ fixedCodim ρ A := by
  by_contra! hsmall
  have hA : A ≠ ⊥ := by intro he; rw [he,Representation.BinaryOffender.rank_bot] at hlarge; omega
  have hoff : IsOffender ρ A := ⟨⟨hA,inferInstance⟩,by omega⟩
  have hf : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    rcases ρ.normal_ker.eq_bot_or_eq_top with hh | hh
    · exact hh
    · apply (hne ?_).elim
      apply MonoidHom.ext
      intro g
      exact (show g ∈ ρ.ker from hh.symm ▸ mem_top g)
  have hfit : generalizedFitting G = ⊤ := generalizedFitting_eq_top_of_quasisimple
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hi : IsIrreducible (ρ.comp (⊤ : Subgroup G).subtype) :=
    (irreducible_comp_surjective_iff (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
      topEquiv.surjective ρ).mpr inferInstance
  obtain ⟨B,_,hB⟩ := hoff.exists_bestOffender ρ
  have hs := ChapterB.SourceClassification.actionCase_of_bestOffender hsq hfit inferInstance hf hi hB
  obtain ⟨E,hE,⟨e⟩⟩ := irreducible_card_sp_natural ρ ⊤ (offenderSubgroup ρ) F hF hn
    ((Nat.card_congr (topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv).trans hG) hs
  let f : G ≃* Sp E.Carrier := topEquiv.symm.trans e.groupEquiv
  have he (g : G) (w : W) : e.linearEquiv (ρ g w) =
      SymplecticConjugatePair.binaryNatural (f g) (e.linearEquiv w) :=
    e.intertwines (topEquiv.symm g) w
  have hd := fixedCodim_map_equivariant ρ SymplecticConjugatePair.binaryNatural
    f.toMonoidHom e.linearEquiv he A
  have hAe : IsElementaryTwo (A.map f.toMonoidHom) := by
    refine ⟨?_,IsElementaryAbelian.map f.toMonoidHom⟩
    intro hz
    apply hA
    exact (map_eq_bot_iff_of_injective A f.injective).mp hz
  have hlo := SymplecticConjugatePair.NaturalBounds.natural_small_codim_rank_le
    (show Nat.card E.Carrier=2^n by rw [E.card_eq,hE]) (by omega) hAe (by omega)
  rw [rank_map_injective f.toMonoidHom f.injective] at hlo
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic


namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H G F W : Type*} [Group H] [Finite H] [Group G] [Finite G]
  [IsSimpleGroup G] [IsQuasisimple G] [Field F] [Finite F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Irreducible chief actions kill the normal two-kernel, retaining the
image of the literal actor in the symplectic quotient. -/
theorem irreducible_fixedCodim_ge_of_two_kernel
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hG : Nat.card G = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q)) : 2*n ≤ fixedCodim ρ A := by
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
    rw [←hcomp,hs]
    rfl
  have hA : A.map q ≠ ⊥ := by
    intro hz
    rw [hz,card_bot,hF,←pow_mul] at hlarge
    have hh : 1 < 2^(n*2) := one_lt_pow₀ (by decide) (by omega)
    omega
  have hc := (show IsElementaryTwo (A.map q) from ⟨hA,inferInstance⟩).card_eq_two_pow_rank
  have hr : 2*n ≤ rank (A.map q) := by
    rw [hc,hF,←pow_mul] at hlarge
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hlarge
    omega
  have hl := irreducible_large_actor_fixedCodim_ge hF hn hG hsq σ hnσ (A.map q) hr
  rw [←hcomp]
  change 2*n ≤ Module.finrank (ZMod 2) (W ⧸ fixedSpace (σ.comp q) A)
  rw [fixedSpace_comp_map]
  exact hl

section GroupModule
variable {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
  [MulDistribMulAction H U] [Nontrivial U]

/-- Each noncentral chief factor costs at least q² in the actual fixed index. -/
theorem simple_group_fixedIndex_ge_square
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hG : Nat.card G = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hirr : ∀ D : Subgroup U, (∀ h : H, ∀ u : U, u ∈ D → h • u ∈ D) → D = ⊥ ∨ D = ⊤)
    (hne : ¬ ∀ h : H, ∀ u : U, h • u = u) :
    Nat.card F^2 ≤ (FixedPoints.subgroup A U).index := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := H) (G := U) (p := 2)
  let : IsIrreducible ρ := by
    rw [Representation.IsIrreducible,isSimpleOrder_iff]
    refine ⟨inferInstance,?_⟩
    intro X
    let D : Subgroup U := AddSubgroup.toSubgroup' X.toSubmodule.toAddSubgroup
    rcases hirr D (fun h u hu => X.apply_mem_toSubmodule h hu) with hd | hd
    · left
      apply bot_unique
      intro v hv
      have hh : v.toMul ∈ D := hv
      rw [hd,Subgroup.mem_bot] at hh
      exact hh
    · right
      apply top_unique
      intro v _
      have hv : v.toMul ∈ D := by rw [hd]; trivial
      exact hv
  have hnρ : ρ ≠ 1 := by
    intro he
    apply hne
    intro h u
    exact congrArg (fun τ : Representation (ZMod 2) H (Additive U) => τ h (Additive.ofMul u)) he
  have hl := irreducible_fixedCodim_ge_of_two_kernel hF hn hG hsq q hq hp ρ hnρ A hlarge
  have hf : fixedSpace (ρ.comp A.subtype) ⊤ = fixedSpace ρ A := by
    ext v
    exact ⟨fun hv g => hv ⟨g,mem_top g⟩,fun hv g => hv g.val⟩
  have hc := fixed_subgroup_index (ρ.comp A.subtype)
  rw [fixedCodim,hf] at hc
  have hg : AddSubgroup.toSubgroup' (fixedSpace ρ A).toAddSubgroup = FixedPoints.subgroup A U := by
    ext u
    rfl
  rw [hg] at hc
  rw [hc,hF,←pow_mul]
  dsimp only [fixedCodim] at hl
  exact Nat.pow_le_pow_right (by decide) (by omega)
end GroupModule
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open NoncentralChiefRefinement SymmetricSixBudget
variable {H G F : Type*} [Group H] [Finite H] [Group G] [Finite G]
  [IsSimpleGroup G] [IsQuasisimple G] [Field F] [Finite F]

private theorem two_factor_index_lower {U : Subgroup H} [U.Normal]
    (s : SeriesOn U) (A : Subgroup H) (k : ℕ)
    (hlower : ∀ i, ¬s.Central i → k ≤ sectionIndex A (s.lower i) (s.upper i))
    (i j : Fin s.series.length) (hij : i < j) (hi : ¬s.Central i) (hj : ¬s.Central j) :
    k*k ≤ (centralizer (A : Set H)).relIndex U := by
  let w (B : Subgroup H) := (centralizer (A : Set H)).relIndex B
  have hmono {B C : Subgroup H} (hBC : B ≤ C) : w B ≤ w C :=
    (centralizer (A : Set H)).relIndex_le_of_le_right hBC index_ne_zero_of_finite
  have hpos (B : Subgroup H) : 1 ≤ w B := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hstep (r : Fin s.series.length) (hr : ¬s.Central r) :
      k * w (s.lower r).val ≤ w (s.upper r).val :=
    (Nat.mul_le_mul_right _ (hlower r hr)).trans
      (sectionIndex_mul_lower_le A (s.lower r) (s.upper r) (s.series.isChief r).lt.le)
  have h1 : k ≤ w (s.upper i).val := by
    have hh := hstep i hi
    have hp := hpos (s.lower i).val
    nlinarith
  have h2 : w (s.upper i).val ≤ w (s.lower j).val := by
    apply hmono
    exact s.series.strictMono.monotone (show i.succ ≤ j.castSucc by simpa using hij)
  have h3 := hstep j hj
  have h4 := hmono (s.upper_le j)
  change k*k ≤ w U
  nlinarith

/-- The source q³ fixed-index budget permits at most one noncentral chief
factor, without assuming that the normal two-group is abelian. -/
theorem symplectic_noncentralCount_le_one
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hG : Nat.card G = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : IsPGroup 2 U)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hindex : (centralizer (A : Set H)).relIndex U ≤ Nat.card F^3)
    (s : SeriesOn U) : s.noncentralCount ≤ 1 := by
  have hlower (i : Fin s.series.length) (hi : ¬s.Central i) :
      Nat.card F^2 ≤ sectionIndex A (s.lower i) (s.upper i) := by
    let := s.factor_elementary hU i
    let := s.factor_nontrivial i
    let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
    let := μ
    exact simple_group_fixedIndex_ge_square hF hn hG hsq q hq hp A hlarge
      (s.factor_irreducible i) (fun ht => hi ((s.central_iff_action i).mpr ht))
  by_contra hnot
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  have hl : (Nat.card F^2)*(Nat.card F^2) ≤ (centralizer (A : Set H)).relIndex U := by
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact two_factor_index_lower s A _ hlower i j hh hi hj
    · exact two_factor_index_lower s A _ hlower j i hh hj hi
  have hq : 1 < Nat.card F := by
    rw [hF]
    exact one_lt_pow₀ (by decide) (by omega)
  have hgt : Nat.card F^3 < (Nat.card F^2)*(Nat.card F^2) := by
    have hh := Nat.pow_lt_pow_right hq (show 3<4 by decide)
    nlinarith
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
