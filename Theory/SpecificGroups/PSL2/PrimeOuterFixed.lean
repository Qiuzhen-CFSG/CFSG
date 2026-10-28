module

public import Theory.SpecificGroups.PGL2.OuterInvolutionCentralizer
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Odd dihedral fixed subgroups of prime-field outer involutions

Prime-field coverage realizes every automorphism by the actual PGL₂
conjugation action. Its fixed subgroup maps bijectively to the intersection
of the canonical PSL₂ image with the PGL₂ element centralizer. The reflected
torus model therefore gives a nonabelian odd dihedral fixed subgroup for
every outer involution. Transport through a supplied PSL₂ model and the
literal normalizer action identifies the original relative centralizer.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.567.
-/

public section

open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem pgl_fixed_equiv (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hc : 3 < Nat.card F) (a : PGL2 F) :
    Nonempty ((pgl2InnerAutPSL2 F hF hc a).fixedSubgroup ≃*
      ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
        centralizer ({a} : Set (PGL2 F)) : Subgroup (PGL2 F))) := by
  let α := pgl2InnerAutPSL2 F hF hc a
  let j : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  let f := j.comp α.fixedSubgroup.subtype
  have hf : Function.Injective f :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp Subtype.val_injective
  have he : f.range = j.range ⊓ centralizer ({a} : Set (PGL2 F)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨⟨y, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
      have hy := congrArg j ((MulAut.mem_fixedSubgroup _ _).mp y.property)
      rw [toPGL_pgl2InnerAutPSL2_apply] at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm
    · rintro ⟨⟨y, rfl⟩, hy⟩
      refine ⟨⟨y, (MulAut.mem_fixedSubgroup _ _).mpr ?_⟩, rfl⟩
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [toPGL_pgl2InnerAutPSL2_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hy).symm
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr he)⟩

/-- The fixed subgroup of any outer involution of an actual prime-field
PSL₂ model is odd dihedral, with nontrivial rotation subgroup. -/
theorem prime_outer_fixed_dihedral {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {Q : Type*} [Group Q] (eQ : Q ≃* PSL(2, ZMod p))
    (α : MulAut Q) (hsq : α ^ 2 = 1)
    (hout : α ∉ (MulAut.conj : Q →* MulAut Q).range) :
    ∃ n : ℕ, Odd n ∧ 1 < n ∧ Nonempty (α.fixedSubgroup ≃* DihedralGroup n) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hF : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hodd, by decide, by simp⟩
  let hc : 3 < Nat.card (ZMod p) := by simpa using hp
  let f := pgl2InnerAutPSL2 (ZMod p) hF hc
  obtain ⟨a, ha⟩ := prime_card_pgl_coverage (p := p) (ZMod p) (by simp) hF hc
    (MulAut.congr eQ α)
  have hasq : a ^ 2 = 1 := by
    apply pgl2InnerAutPSL2_injective (ZMod p) hF hc
    rw [map_pow, ha, ← map_pow, hsq, map_one, map_one]
  have haout : a ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := ZMod p)).range := by
    rintro ⟨q, rfl⟩
    have hh : MulAut.congr eQ α = MulAut.conj q := by
      rw [← ha]
      exact pgl2InnerAutPSL2_toPGL (ZMod p) hF hc q
    obtain ⟨b, hb⟩ := (MulAut.congr_inner_iff eQ α).mp ⟨q, hh⟩
    exact hout ⟨b, hb.symm⟩
  have hane : a ≠ 1 := fun h => haout (h ▸ (MonoidHom.range _).one_mem)
  obtain ⟨n, hn, hlarge, ⟨eD⟩⟩ := Theory.PGL2.outer_involution_centralizer_dihedral
    (ZMod p) hF hc a ⟨hane, hasq⟩ haout
  obtain ⟨eC⟩ := pgl_fixed_equiv (ZMod p) hF hc a
  refine ⟨n, hn, hlarge, ⟨(MulAut.fixedSubgroupCongr eQ α).trans ?_⟩⟩
  rw [← ha]
  exact eC.trans eD

/-- For a literal normalizer action, the same model describes the original
relative centralizer, with no change of quotient or ambient subgroup. -/
theorem prime_outer_relative_centralizer_dihedral
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (K : Subgroup G) (eK : K ≃* PSL(2, ZMod p))
    (i : G) (hi : i ∈ normalizer (K : Set G)) (hsq : i ^ 2 = 1)
    (hout : K.normalizerMonoidHom ⟨i, hi⟩ ∉ (MulAut.conj : K →* MulAut K).range) :
    ∃ n : ℕ, Odd n ∧ 1 < n ∧ Nonempty
      ((K ⊓ centralizer ({i} : Set G) : Subgroup G) ≃* DihedralGroup n) := by
  have hasq : K.normalizerMonoidHom ⟨i, hi⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨i, hi⟩ : normalizer (K : Set G)) ^ 2 = 1 from Subtype.ext hsq,
      map_one]
  obtain ⟨n, hn, hlarge, ⟨e⟩⟩ := prime_outer_fixed_dihedral hp eK
    (K.normalizerMonoidHom ⟨i, hi⟩) hasq hout
  exact ⟨n, hn, hlarge, ⟨(K.normalizerFixedEquivCentralizer ⟨i, hi⟩).symm.trans e⟩⟩

end Theory.PSL2

end
