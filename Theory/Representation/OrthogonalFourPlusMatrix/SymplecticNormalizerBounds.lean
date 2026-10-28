module

public import Theory.Representation.OrthogonalFourPlusMatrix.SymplecticNormalizerDefs
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterElementaryRank
-- Intentional internal proof split in the determinant-normalizer family:
-- reuse the one-factor involution calculation without widening its public API.
import all Theory.Representation.OrthogonalFourPlusMatrix.OuterElementaryRank

/-!
# Symplectic bounds for the determinant normalizer

For any invariant nondegenerate binary form on M₂(𝔽₄), the normalizer of
SL₂(4) × SL₂(4) inside its isometry group has order at most 14400. An invariant
form eliminates the scalar centralizer, giving a faithful conjugation action
on A₅ × A₅. The image is proper: an involution inducing an outer automorphism
on just one factor would centralize the other factor, forcing it into the
original determinant action. The automorphism group has order 28800.

Every elementary two-subgroup outside the determinant image has order at
most eight, by the maximum-rank calculation for the full linear normalizer.
These intrinsic estimates are used by the literal terminal-action consumer
in Aschbacher--Smith 14.3.15, printed p.994, case G.11.2(7). The form remains
an explicit parameter; neither estimate identifies an arbitrary action with
the determinant tensor.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Matrix Subgroup Module
open Representation.BinaryOffender
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
open Theory.GroupTheory.WreathTwoElementaryRank

private def rowVector (i : Fin 2) (v : Fin 2 → F) : V := fun j k => if j=i then v k else 0

private theorem rowVector_add (i : Fin 2) (v w : Fin 2 → F) :
    rowVector i (v+w) = rowVector i v + rowVector i w := by
  funext j k
  by_cases h : j=i <;> simp [rowVector,h]

private theorem rowVector_smul (i : Fin 2) (c : F) (v : Fin 2 → F) :
    rowVector i (c • v) = c • rowVector i v := by
  funext j k
  by_cases h : j=i <;> simp [rowVector,h]

private theorem rowVector_sum (v : V) : v = rowVector 0 (v 0) + rowVector 1 (v 1) := by
  funext j k
  fin_cases j <;> simp [rowVector]

private theorem invariant_row_zero
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g u v, B (action g u) (action g v) = B u v)
    (v w : Fin 2 → F) : B (rowVector 0 v) (rowVector 0 w) = 0 := by
  let a : SpecialLinearGroup (Fin 2) F := SpecialLinearGroup.transvection zero_ne_one 1
  have h0 (v : Fin 2 → F) : action (a,1) (rowVector 0 v) = rowVector 0 v := by
    funext j k
    fin_cases j <;> fin_cases k <;>
      simp [action_apply,a,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two,rowVector]
  have h1 (w : Fin 2 → F) : action (a,1) (rowVector 1 w) = rowVector 1 w + rowVector 0 w := by
    funext j k
    fin_cases j <;> fin_cases k <;>
      simp [action_apply,a,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two,rowVector]
  have hh := hB (a,1) (rowVector 0 v) (rowVector 1 w)
  rw [h0,h1,map_add] at hh
  exact add_eq_left.mp hh

/-- A scalar isometry of an invariant nondegenerate binary form is trivial. -/
theorem invariant_scalar_isometry_eq_one
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (action g u) (action g v) = B u v)
    (c : F) (hc : c ≠ 0) (hiso : ∀ u v, B (c • u) (c • v) = B u v) : c = 1 := by
  by_contra hc1
  have hc2 : c*c-1 ≠ 0 := by
    intro he
    exact hc1 (CharTwo.sq_injective (by simpa only [pow_two,one_mul] using sub_eq_zero.mp he))
  let a := SpecialLinearGroup.diag2 c hc
  have he0 (v : Fin 2 → F) : c • action (a,1) (rowVector 0 v) = rowVector 0 ((c*c) • v) := by
    funext j k
    fin_cases j <;> fin_cases k <;>
      simp [action_apply,a,SpecialLinearGroup.diag2_coe',Matrix.vecMul,Matrix.vecHead,Matrix.vecTail,dotProduct,Matrix.mul_apply,Fin.sum_univ_two,rowVector,mul_assoc]
  have he1 (v : Fin 2 → F) : c • action (a,1) (rowVector 1 v) = rowVector 1 v := by
    funext j k
    fin_cases j <;> fin_cases k <;>
      simp [action_apply,a,SpecialLinearGroup.diag2_coe',Matrix.vecMul,Matrix.vecHead,Matrix.vecTail,dotProduct,Matrix.mul_apply,Fin.sum_univ_two,rowVector,hc,mul_assoc]
  have hz (v w : Fin 2 → F) : B (rowVector 0 v) (rowVector 1 w) = 0 := by
    let z : Fin 2 → F := (c*c-1)⁻¹ • v
    have hh := (hiso (action (a,1) (rowVector 0 z)) (action (a,1) (rowVector 1 w))).trans
      (hB (a,1) (rowVector 0 z) (rowVector 1 w))
    rw [he0,he1] at hh
    have hdiff : rowVector 0 ((c*c) • z) - rowVector 0 z = rowVector 0 v := by
      rw [rowVector_smul]
      calc
        (c*c) • rowVector 0 z - rowVector 0 z = (c*c-1) • rowVector 0 z := by rw [sub_smul,one_smul]
        _ = rowVector 0 v := by rw [show rowVector 0 z = (c*c-1)⁻¹ • rowVector 0 v from rowVector_smul 0 _ v,
        smul_smul,mul_inv_cancel₀ hc2,one_smul]
    have hz' : B (rowVector 0 ((c*c) • z) - rowVector 0 z) (rowVector 1 w) = 0 := by
      rw [map_sub,LinearMap.sub_apply,hh,sub_self]
    rwa [hdiff] at hz'
  have he : rowVector 0 (fun _ => (1 : F)) = 0 := hnd.1 _ (by
    intro y
    rw [rowVector_sum y,map_add,invariant_row_zero B hB,hz,zero_add])
  have hh := congrArg (fun x : V => x 0 0) he
  simpa [rowVector] using hh

/-- The scalar commutant disappears in the actual symplectic normalizer. -/
theorem symplectic_centralizing_eq_one
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (action g u) (action g v) = B u v)
    (t : symplecticNormalizer B) (hc : ∀ g, Commute t.val (linearAction g)) : t = 1 := by
  obtain ⟨c,hc⟩ := centralizer_scalar t.val.toAddMonoidHom (by
    intro g v
    exact LinearEquiv.congr_fun (hc g).eq v)
  change ∀ v, t.val v = c • v at hc
  have hc0 : c ≠ 0 := by
    intro hz
    have he := t.val.injective (show t.val (1 : V) = t.val 0 by rw [hc,hc,hz]; simp)
    exact one_ne_zero he
  have he := invariant_scalar_isometry_eq_one B hnd hB c hc0 (fun u v => by
    rw [←hc,←hc]
    exact t.property.2 u v)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simpa [he] using hc v
end ClassicalOrthogonal.FourPlusMatrix.Binary

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Matrix Subgroup Module
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
open Theory.GroupTheory.WreathTwoElementaryRank

def determinantImageEquiv : G ≃* linearAction.range :=
  MonoidHom.ofInjective (fun _ _ h => action_injective (congrArg LinearEquiv.toLinearMap h))

/-- Conjugation by the actual isometries on the determinant group. -/
def symplecticConjugation (B : LinearMap.BilinForm (ZMod 2) V) :
    symplecticNormalizer B →* MulAut G := by
  exact (MulAut.congr determinantImageEquiv.symm).toMonoidHom.comp
    (linearAction.range.normalizerMonoidHom.comp
      (inclusion (show symplecticNormalizer B ≤ normalizer (linearAction.range : Set _) from
        fun _ ht => ht.1)))

theorem symplecticConjugation_action
    (B : LinearMap.BilinForm (ZMod 2) V) (t : symplecticNormalizer B) (g : G) (v : V) :
    action (symplecticConjugation B t g) (t.val v) = t.val (action g v) := by
  have he : linearAction (symplecticConjugation B t g) =
      t.val * linearAction g * t.val⁻¹ := by
    exact congrArg Subtype.val (determinantImageEquiv.apply_symm_apply
      (linearAction.range.normalizerMonoidHom ⟨t.val,t.property.1⟩ (determinantImageEquiv g)))
  have hh : linearAction (symplecticConjugation B t g) * t.val =
      t.val * linearAction g := by rw [he]; group
  exact LinearEquiv.congr_fun hh v

theorem symplecticConjugation_injective
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (action g u) (action g v) = B u v) :
    Function.Injective (symplecticConjugation B) := by
  apply (injective_iff_map_eq_one _).mpr
  intro t ht
  apply symplectic_centralizing_eq_one B hnd hB t
  intro g
  change t.val * linearAction g = linearAction g * t.val
  apply LinearEquiv.ext
  intro v
  have hh := symplecticConjugation_action B t g v
  rw [ht] at hh
  exact hh.symm

private theorem conjugation_of_action
    (B : LinearMap.BilinForm (ZMod 2) V) (t : symplecticNormalizer B) (r : G)
    (hr : ∀ v, t.val v = action r v) : symplecticConjugation B t = MulAut.conj r := by
  apply MulEquiv.ext
  intro g
  apply action_injective
  apply LinearMap.ext
  intro v
  have hh := symplecticConjugation_action B t g (action r⁻¹ v)
  simp only [hr,←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
    Module.End.one_apply] at hh
  simpa only [MulAut.conj_apply,←Module.End.mul_apply,←map_mul,mul_assoc] using hh

/-- The normalizer action cannot realize an outer automorphism on one factor alone. -/
theorem symplecticConjugation_not_surjective
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (action g u) (action g v) = B u v) :
    ¬ Function.Surjective (symplecticConjugation B) := by
  intro hsurj
  let σ : MulAut Pair := (factorEquiv (Equiv.swap (0 : Fin 5) 1)).prodCongr (MulEquiv.refl Alt)
  let e := MulAut.congr alternatingPairEquiv
  obtain ⟨t,ht⟩ := hsurj (e.symm σ)
  have hte : e (symplecticConjugation B t) = σ := by rw [ht,e.apply_symm_apply]
  have hσ2 : σ*σ=1 := by
    apply MulEquiv.ext
    intro p
    apply Prod.ext
    · change factorEquiv (Equiv.swap (0 : Fin 5) 1)
        (factorEquiv (Equiv.swap (0 : Fin 5) 1) p.1) = p.1
      rw [←MulAut.mul_apply,←map_mul,Equiv.swap_mul_self,map_one]
      rfl
    · rfl
  have ht2 : t*t=1 := by
    apply symplecticConjugation_injective B hnd hB
    apply e.injective
    rw [map_mul,map_one,map_mul,hte,hσ2,map_one]
  have hc (a : SpecialLinearGroup (Fin 2) F) :
      symplecticConjugation B t (1,a) = (1,a) := by
    apply alternatingPairEquiv.injective
    have hh := MulEquiv.congr_fun hte (alternatingPairEquiv (1,a))
    change alternatingPairEquiv (symplecticConjugation B t (alternatingPairEquiv.symm
      (alternatingPairEquiv (1,a)))) = σ (alternatingPairEquiv (1,a)) at hh
    rw [alternatingPairEquiv.symm_apply_apply] at hh
    exact hh.trans (by
      change ((factorEquiv (Equiv.swap (0 : Fin 5) 1))
        (Representation.SL2FourNatural.alternatingFiveEquiv 1),
        Representation.SL2FourNatural.alternatingFiveEquiv a) = _
      change (_,_) = (Representation.SL2FourNatural.alternatingFiveEquiv 1,
        Representation.SL2FourNatural.alternatingFiveEquiv a)
      simp only [map_one])
  obtain ⟨b,hb⟩ := right_centralizing_involution t.val
    (fun v => LinearEquiv.congr_fun (congrArg Subtype.val ht2) v) (by
      intro a v
      have hh := symplecticConjugation_action B t (1,a) v
      rw [hc] at hh
      exact hh.symm)
  have hinner := conjugation_of_action B t (b,1) hb
  have hconj : e (MulAut.conj (b,1)) = MulAut.conj (alternatingPairEquiv (b,1)) := by
    apply MulEquiv.ext
    intro x
    simp only [e,MulAut.congr_apply,MulEquiv.trans_apply,MulAut.conj_apply,
      map_mul,map_inv,MulEquiv.apply_symm_apply]
  have hbmark : alternatingPairEquiv (b,1) =
      (Representation.SL2FourNatural.alternatingFiveEquiv b,1) :=
    Prod.ext rfl Representation.SL2FourNatural.alternatingFiveEquiv.map_one
  rw [hbmark] at hconj
  have hσinner := hte.symm.trans ((congrArg e hinner).trans hconj)
  have hα : factorEquiv (Equiv.swap (0 : Fin 5) 1) =
      factorEquiv (Representation.SL2FourNatural.alternatingFiveEquiv b).val := by
    apply MulEquiv.ext
    intro x
    have hh := congrArg Prod.fst (MulEquiv.congr_fun hσinner (x,1))
    change factorEquiv (Equiv.swap (0 : Fin 5) 1) x =
      Representation.SL2FourNatural.alternatingFiveEquiv b * x *
      (Representation.SL2FourNatural.alternatingFiveEquiv b)⁻¹ at hh
    have hi := wreathHom_inner (Representation.SL2FourNatural.alternatingFiveEquiv b) 1
    have hx := congrArg Prod.fst (MulEquiv.congr_fun hi (x,1))
    simp only [wreathHom,wreathMap_apply,baseHom,turn_ne_one,ite_true,
      MonoidHom.coe_mk,OneHom.coe_mk] at hx
    exact hh.trans hx.symm
  have hs := factorEquiv.injective hα
  have hh := (Representation.SL2FourNatural.alternatingFiveEquiv b).property
  rw [←hs] at hh
  have hno : Equiv.swap (0 : Fin 5) 1 ∉ alternatingGroup (Fin 5) := by
    simp [Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1)]
  exact hno hh

/-- The symplectic determinant normalizer has order at most 14400. -/
theorem symplecticNormalizer_card_le
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (action g u) (action g v) = B u v) :
    Nat.card (symplecticNormalizer B) ≤ 14400 := by
  let f := symplecticConjugation B
  let e := (MulAut.congr alternatingPairEquiv).trans wreathEquiv.symm
  have hcard : Nat.card (MulAut G) = 28800 := by
    rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card]
    norm_num [Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Sym,
      Nat.card_perm,Nat.card_fin,Theory.GroupTheory.WreathTwoElementaryRank.C2,
      Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hi : 1 < f.range.index := Subgroup.one_lt_index_of_ne_top
    (fun he => symplecticConjugation_not_surjective B hnd hB
      (MonoidHom.range_eq_top.mp he))
  have he := f.range.card_mul_index
  have hf : Nat.card f.range = Nat.card (symplecticNormalizer B) :=
    (Nat.card_congr (MonoidHom.ofInjective (symplecticConjugation_injective B hnd hB)).toEquiv).symm
  rw [hf,hcard] at he
  nlinarith
end ClassicalOrthogonal.FourPlusMatrix.Binary

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Subgroup Module Representation.BinaryOffender

/-- Elementary actors outside the determinant group have order at most eight. -/
theorem symplecticNormalizer_outer_elementary_card_le
    (B : LinearMap.BilinForm (ZMod 2) V)
    (A : Subgroup (symplecticNormalizer B)) (hA : IsElementaryAbelian 2 A)
    (hout : ¬ A.map (symplecticNormalizer B).subtype ≤ linearAction.range) :
    Nat.card A ≤ 8 := by
  let := hA
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  have he : linearAction.range.map e.symm.toMonoidHom = actionImage action := by
    apply le_antisymm
    · rintro _ ⟨_,⟨g,rfl⟩,rfl⟩
      exact ⟨g,Units.ext rfl⟩
    · rintro _ ⟨g,rfl⟩
      exact ⟨linearAction g,⟨g,rfl⟩,Units.ext rfl⟩
  have hn (t : symplecticNormalizer B) : e.symm t.val ∈ linearNormalizer action := by
    have hh := linearAction.range.le_normalizer_map e.symm.toMonoidHom
      (mem_map_of_mem e.symm.toMonoidHom t.property.1)
    rwa [he] at hh
  let f : symplecticNormalizer B →* linearNormalizer action :=
    (e.symm.toMonoidHom.comp (symplecticNormalizer B).subtype).codRestrict _ hn
  have hf : Function.Injective f := by
    intro x y heq
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val heq))
  have hc : Nat.card A < 16 := by
    by_contra! hlarge
    let C := A.map f
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.map f
    have hC : 16 ≤ Nat.card C := by
      rwa [card_map_of_injective hf]
    have hle := large_elementary_le_actionImage C hC
    apply hout
    rintro _ ⟨t,ht,rfl⟩
    have hm := hle (mem_map_of_mem (linearNormalizer action).subtype (mem_map_of_mem f ht))
    obtain ⟨g,hg⟩ := hm
    refine ⟨g,?_⟩
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun u : (Module.End (ZMod 2) V)ˣ => u.val v) hg
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hlt : n < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [hn] using hc
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 3)
end ClassicalOrthogonal.FourPlusMatrix.Binary
