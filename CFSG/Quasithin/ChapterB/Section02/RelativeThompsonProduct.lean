module

public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonPlane
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Centralizer
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.FixedComplement
public import Theory.GroupTheory.NormalSymmetricThree

/-!
# The centralizer product of a single relative Thompson factor

The stable Thompson family selects an actual natural binary plane in the
solvable FF decomposition. The normal S₃ image splits off its centralizer;
that centralizer fixes the selected plane. Lifting this decomposition through
the literal action quotient gives G=I C_G([V,I]). The natural-plane fixed
complement also proves [V,I] intersects C_G(I) trivially.

These statements retain the original normal span I=⟨J(R)^G⟩ and quotient
kernel C_G(V). They feed the actual C_G(z) application in Chapter13's
Solvable/LocalProduct/NormalizerProduct. The source single-factor selection
and noncentrality remain separate inputs at this level.
Source: Aschbacher–Smith B.1.8, B.2.10 and 13.4.8, pp.70,77,905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

private theorem stable_symmetricThree_factor
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W}
    (d : ThreeConjugates.SolvableFFStructure ρ)
    (hfaith : Function.Injective ρ)
    (P : Set (Subgroup H)) (hP : IsStable ρ P)
    (hmodel : Nonempty ((generatedBy P ⊤) ≃* Equiv.Perm (Fin 3))) :
    ∃ i, d.factor i = generatedBy P ⊤ := by
  obtain ⟨i,hi⟩ := d.toSolvableFFFactors.stableFactorSet_nonempty hfaith d.ratio_one hP
  have he := d.toSolvableFFFactors.stable_generatedBy_eq hfaith d.ratio_one hP
  have hle : d.factor i ≤ generatedBy P ⊤ := by
    rw [he]
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  obtain ⟨e⟩ := hmodel
  have hcard : Nat.card (generatedBy P ⊤) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  exact ⟨i, eq_of_le_of_card_ge hle (by rw [hcard, d.toSolvableFFFactors.factor_card])⟩

theorem relative_thompson_span_centralizer_product
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 H = ⊥)
    (hmodel : Nonempty (((conjugateSpanBy (elementaryAbelianMaxJ R) ⊤).map q) ≃*
      Equiv.Perm (Fin 3))) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) ⊤
    I ⊔ centralizer ((⁅V,I⁆ : Subgroup G) : Set G) = ⊤ := by
  let := hsolv
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) ⊤
  let N := I.map q
  have hs := lemma_B_2_10_relative V R hVR q hq hker hJ
  have hfaith : Function.Injective ρ :=
    NormalElementaryQuotient.representation_injective V q hq hker
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ
    (Group.isSolvable_of_surjective hq) hcore hfaith hs.1
  have he := relative_thompson_span_image V R hVR q hq hker hJ
  obtain ⟨i,hi⟩ := stable_symmetricThree_factor d hfaith _ hs.2.1 (he ▸ hmodel)
  have hiN : d.factor i = N := hi.trans he.symm
  let : N.Normal := by
    change (I.map q).Normal
    rw [he]
    exact (relativeMaxOffenderImages_generated_facts V R hVR q hq hker hJ).1
  have hcent : (centralizer (N : Set H)).comap q ≤ centralizer ((⁅V,I⁆ : Subgroup G) : Set G) := by
    intro c hc v hv
    have hv' : Additive.ofMul (⟨v,(commutator_le_left V I) hv⟩ : V) ∈
        subspaceCommutator ρ ⊤ (d.factor i) := by
      rw [hiN, ← NormalElementaryQuotient.commutatorSpace_eq V q hq hker I]
      exact hv
    have hf := d.toSolvableFFFactors.centralizer_fixes_support i (q c)
      (hiN.symm ▸ hc) hv'
    have hh := congrArg (fun a : Additive V => (a.toMul : G)) hf
    rw [NormalElementaryQuotient.representation_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨e⟩ := hmodel
  obtain ⟨f,hf⟩ := NormalSymmetricThree.exists_product_equiv N e
  apply top_unique
  intro g _
  let a := f.symm (q g)
  obtain ⟨x,hx,hxa⟩ := a.1.property
  have heq : q x * a.2.val = q g := by
    rw [hxa, ← hf]
    exact f.apply_symm_apply (q g)
  have hc : q (x⁻¹ * g) ∈ centralizer (N : Set H) := by
    rw [map_mul,map_inv,← heq,inv_mul_cancel_left]
    exact a.2.property
  have hh := (I ⊔ centralizer ((⁅V,I⁆ : Subgroup G) : Set G)).mul_mem
    (mem_sup_left hx) (mem_sup_right (hcent hc))
  simpa only [mul_inv_cancel_left] using hh

theorem relative_thompson_span_moved_disjoint
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 H = ⊥)
    (hmodel : Nonempty (((conjugateSpanBy (elementaryAbelianMaxJ R) ⊤).map q) ≃*
      Equiv.Perm (Fin 3))) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) ⊤
    Disjoint (⁅V,I⁆ : Subgroup G) (centralizer (I : Set G)) := by
  let := hsolv
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) ⊤
  have hs := lemma_B_2_10_relative V R hVR q hq hker hJ
  have hfaith : Function.Injective ρ :=
    NormalElementaryQuotient.representation_injective V q hq hker
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ
    (Group.isSolvable_of_surjective hq) hcore hfaith hs.1
  have he := relative_thompson_span_image V R hVR q hq hker hJ
  obtain ⟨i,hi⟩ := stable_symmetricThree_factor d hfaith _ hs.2.1 (he ▸ hmodel)
  have hiN : d.factor i = I.map q := hi.trans he.symm
  apply disjoint_def.mpr
  intro v hv hc
  let w : Additive V := Additive.ofMul ⟨v,(commutator_le_left V I) hv⟩
  have hw : w ∈ subspaceCommutator ρ ⊤ (d.factor i) := by
    rw [hiN, ← NormalElementaryQuotient.commutatorSpace_eq V q hq hker I]
    exact hv
  have hc' : w ∈ fixedSpace ρ (d.factor i) := by
    rw [hiN]
    exact (NormalElementaryQuotient.mem_fixedSpace_image V q hq hker I w).mpr hc
  have hh : w = 0 := (Submodule.disjoint_def.mp
    (d.toSolvableFFFactors.support_complement i).disjoint) w hw hc'
  exact congrArg (fun x : Additive V => (x.toMul : G)) hh

end CFSG.Quasithin.ChapterB
