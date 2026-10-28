module
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import BenderSuzuki.External.Suzuki.VI.theorem_2_3
public import FeitThompson.BGsection3.lemma_3_1
public import Mathlib.GroupTheory.PGroup

/-!
# The field-two unitary cover obstruction

The actual PSU3(2) action on nine isotropic points has a point stabilizer
of order eight acting regularly on the other points. Its Frobenius kernel
has order nine and is abelian. The free orbit of a nontrivial kernel
weight therefore forces every faithful binary representation to have
dimension at least eight. No perfectness or simplicity is used.

The SU3 scalar kernel has order dividing three. Consequently an action
of degree below eight with kernel contained in that scalar subgroup is
faithful. The marked quadrangle application uses this on the actual
six-dimensional Frattini section to select the full SU3(2) cover.
The full special group has order 216, including its scalar subgroup of
order three. The factor 27 then excludes faithful binary degrees below six
by the general linear group order formula. This supplies the remaining
minimum degree needed for the literal section's irreducibility.

Sources: Fong--Seitz I (4D), (6A)(c), pp.21--23,37; Huppert II.10.12;
Suzuki, Group Theory II, VI.2.3 (Frobenius kernel theorem).
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure

private theorem regular_stabilizer_TI
    {G Ω : Type*} [Group G] (a : G →* Equiv.Perm Ω) (p : Ω)
    (R : Subgroup G)
    (hR : R = (MulAction.stabilizer (Equiv.Perm Ω) p).comap a)
    (hreg : ∀ x y : Ω, x ≠ p → y ≠ p → ∃! r : R, a r x = y) :
    ∀ g : G, g ∉ R → Disjoint R (R.conjBy g) := by
  intro g hg
  have hgp : a g p ≠ p := by
    intro he
    apply hg
    rw [hR]
    exact he
  rw [disjoint_def]
  intro x hx hxg
  obtain ⟨y,hy,rfl⟩ := hxg
  have hyp : a y p = p := by
    have hh := hR ▸ hy
    exact hh
  have hfix : a ((MulAut.conj g) y) (a g p) = a g p := by
    simp only [MulAut.conj_apply,map_mul,map_inv]
    change a g (a y ((a g).symm (a g p))) = a g p
    rw [Equiv.symm_apply_apply,hyp]
  have he := (hreg (a g p) (a g p) hgp hgp).unique
    (y₁ := (⟨_,hx⟩ : R)) (y₂ := 1) hfix (by simp)
  exact congrArg Subtype.val he

/-- Every faithful binary representation of the actual PSU3(2) has degree at least eight. -/
theorem small_projective_unitary_degree
    {E V : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hσ : Function.Injective σ) : 8 ≤ Module.finrank (ZMod 2) V := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ J.specialToProjective_surjective
  have hf : Nat.card {x : E // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hE) (by simpa using hconj)
  obtain ⟨_,a,p,_,_,_,hroot,_,hcard,_⟩ := huppert_II_10_12 J 2 hE hf hJ
  obtain ⟨R,H,_,_,_,_,hRH,_,hR,_,_,hH,hreg,_⟩ := hroot
  have hHb : H = ⊥ := card_eq_one.mp (by simpa using hH)
  rw [hHb,sup_bot_eq] at hRH
  have hR8 : Nat.card R = 8 := by simpa using hR
  have hG72 : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 72 := by
    simpa using hcard
  obtain ⟨K,hK⟩ := Suzuki.VI.suzuki_ch6_theorem_2_3 R
    (by intro he; simp [he] at hR8)
    (by intro he; rw [he,card_top,hG72] at hR8; contradiction)
    (regular_stabilizer_TI a p R hRH hreg)
  let : K.Normal := hK.normal
  have hK9 : Nat.card K = 9 := by
    have hc := hK.isComplement'.card_mul_card
    rw [hR8,hG72] at hc
    omega
  let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hK.kernel_ne_bot
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsMulCommutative K := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3) (by simpa using hK9)
  have hd := Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field σ K R
    hσ (by rw [hK9]; decide) le_normalizer_of_normal (by
      intro r hr k hk
      apply Subtype.ext
      have hc := (lemma_3_1 K R hK.kernel_ne_bot hK.complement_ne_bot
        hK.normal hK.isComplement').mp hK r hr
      apply mem_bot.mp
      rw [←hc]
      refine ⟨k.property,mem_centralizer_singleton_iff.mpr ?_⟩
      exact (mul_inv_eq_iff_eq_mul.mp hk).symm)
  rwa [hR8] at hd

/-- In degree below eight a special-unitary action with only a possible
scalar kernel is faithful, also in the nonperfect field-two case. -/
theorem small_unitary_faithful_of_scalar_kernel
    {E V : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) J.specialSubgroup V)
    (hk : σ.ker ≤ J.specialToProjective.ker)
    (hd : Module.finrank (ZMod 2) V < 8) : Function.Injective σ := by
  apply σ.ker_eq_bot_iff.mp
  by_contra hk0
  have hkc : Nat.card σ.ker = 3 := by
    have hv := (card_dvd_of_le hk).trans J.card_specialToProjective_ker_dvd_three
    exact ((Nat.dvd_prime Nat.prime_three).mp hv).resolve_left
      (fun he => hk0 (card_eq_one.mp he))
  have heq : σ.ker = J.specialToProjective.ker := eq_of_le_of_card_ge hk (by
    rw [hkc]
    exact Nat.le_of_dvd (by decide) J.card_specialToProjective_ker_dvd_three)
  let eπ := QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
    J.specialToProjective_surjective
  let ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V :=
    (QuotientGroup.lift J.specialToProjective.ker σ heq.ge).comp eπ.symm.toMonoidHom
  have hρ (g : J.specialSubgroup) : ρ (J.specialToProjective g) = σ g := by
    have he : eπ.symm (J.specialToProjective g) =
        QuotientGroup.mk' J.specialToProjective.ker g := eπ.symm_apply_eq.mpr rfl
    change QuotientGroup.lift J.specialToProjective.ker σ heq.ge
      (eπ.symm (J.specialToProjective g)) = σ g
    rw [he]
    rfl
  have hf : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    apply bot_unique
    intro g hg
    obtain ⟨x,rfl⟩ := J.specialToProjective_surjective g
    change ρ (J.specialToProjective x) = 1 at hg
    exact heq.le (by rwa [hρ] at hg)
  exact (not_le_of_gt hd) (small_projective_unitary_degree J hE hconj hJ ρ hf)

/-- The full special actor at fixed-field order two has order 216; its
scalar subgroup of order three is retained in this count. -/
theorem small_special_unitary_card
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    Nat.card J.specialSubgroup = 216 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ J.specialToProjective_surjective
  have hT : Nat.card (HermitianForm.BorelTorus.specialTorus J hJ) = 3 := by
    rw [HermitianForm.BorelTorus.special_card,hE]
    norm_num
  have hPT : HermitianForm.BorelTorus.projectiveTorus J hJ = ⊥ := card_eq_one.mp
    (by simpa using HermitianForm.BorelTorus.projective_card J hJ hE hconj)
  have hle : HermitianForm.BorelTorus.specialTorus J hJ ≤ J.specialToProjective.ker := by
    rintro _ ⟨a,rfl⟩
    have ha : hermitianTorusPSU J hJ a = 1 := mem_bot.mp
      (hPT ▸ (show hermitianTorusPSU J hJ a ∈ HermitianForm.BorelTorus.projectiveTorus J hJ
        from ⟨a,rfl⟩))
    apply Subtype.ext
    rw [J.specialToProjective_apply_val]
    change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J a) = 1
    simpa only [hermitianTorusPSU_val,Subgroup.coe_one] using congrArg Subtype.val ha
  have hk : Nat.card J.specialToProjective.ker = 3 := by
    have hlow := card_le_of_le hle
    rw [hT] at hlow
    exact Nat.le_antisymm (Nat.le_of_dvd (by decide)
      J.card_specialToProjective_ker_dvd_three) hlow
  have hf : Nat.card {x : E // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hE) (by simpa using hconj)
  have hp : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 72 := by
    simpa using Representation.SU3.BinaryDegree.card_projective J hE hf
  have he := J.specialToProjective.ker.card_mul_index
  rw [hk,index_ker,MonoidHom.range_eq_top.mpr J.specialToProjective_surjective,
    card_top,hp] at he
  exact he.symm

/-- The factor 27 in the full special actor's order forces binary degree six. -/
theorem small_special_unitary_faithful_degree
    {E V : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) J.specialSubgroup V) (hσ : Function.Injective σ) :
    6 ≤ Module.finrank (ZMod 2) V := by
  have hdiv := Representation.card_dvd_card_GL_of_injective σ hσ
  rw [small_special_unitary_card J hE hconj hJ,Matrix.card_GL_field] at hdiv
  simp only [ZMod.card] at hdiv
  by_contra! hd
  have hdvd : 27 ∣ ∏ i : Fin (Module.finrank (ZMod 2) V),
      (2 ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) :=
    (by decide : 27 ∣ 216).trans hdiv
  generalize Module.finrank (ZMod 2) V = d at hd hdvd
  interval_cases d <;> norm_num [Fin.prod_univ_succ] at hdvd

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
