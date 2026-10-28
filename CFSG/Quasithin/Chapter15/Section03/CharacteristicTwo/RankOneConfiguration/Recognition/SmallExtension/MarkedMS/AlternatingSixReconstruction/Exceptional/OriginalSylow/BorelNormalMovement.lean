module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.RestrictedMovement
public import Theory.GroupTheory.SubgroupConjugation
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.RestrictedMovement

/-!
# Normal Borel actors fixing a large displacement

A subgroup normalized by the six-letter Borel and fixing the movement of
an actor of order greater than two lies in the three-pair mover. If it had
an element outside that mover, that element and its conjugate by (23) would
force every element of the actor to be either 1 or (01). A small checked
coordinate certificate proves this on the augmentation core; the literal
natural quotient creates no additional fixed lifts. Conjugation transports
the result to the marked Borel.

DistanceFourLargeCores applies this calculation to the midpoint two-core
on the original graph, retaining the full cover and the cubic action kernel.
Source: MS93 (3.3)(ii), (5.2)(ii), and the core comparisons in (5.12)(2),
printed pp.867,913--914,925--926.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open BinaryPermutation.SixCover
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelLargeModel
local notation "ρ" => coreRepresentation (Fin 6)
local notation "σ" => naturalRepresentation (Fin 6)
local notation "w" => BorelKernel.words
private theorem two_conjugates_cert : ∀ i j : Fin 16, 8 ≤ i.val →
    (∀ v : Fin 6 → ZMod 2, (∑ k, v k)=0 →
      representation (Fin 6) (w i) (representation (Fin 6) (w j) v-v) =
        representation (Fin 6) (w j) v-v ∧
      representation (Fin 6) (swap23 * w i * swap23⁻¹)
        (representation (Fin 6) (w j) v-v) = representation (Fin 6) (w j) v-v) →
    w j = 1 ∨ w j = swap01 := by
  decide +kernel

private theorem words_lt_eight (i : Fin 16) (hi : i.val < 8) : w i ∈ D := by
  have hdiv : i.val / 8 = 0 := Nat.div_eq_of_lt hi
  simp only [BorelKernel.words,hdiv,pow_zero,mul_one]
  apply D.mul_mem
  · apply D.mul_mem
    · exact D.pow_mem (subset_closure (by simp)) _
    · exact D.pow_mem (subset_closure (by simp)) _
  · exact D.pow_mem (subset_closure (by simp)) _

theorem normal_large_le_plane (A P : Subgroup S)
    (hA : A ≤ borel) (hP : P ≤ borel)
    (hn : borel ≤ normalizer (P : Set S)) (hc : 2 < Nat.card A)
    (hf : ∀ g ∈ P, ∀ a ∈ A, ∀ v, σ g (σ a v-v)=σ a v-v) : P ≤ D := by
  intro g hg
  by_contra hgn
  have hg' : swap23*g*swap23⁻¹ ∈ P :=
    (hn (show swap23 ∈ borel by decide) g).mp hg
  obtain ⟨i,hi⟩ := BorelKernel.words_complete g (hP hg)
  have hlarge : 8 ≤ i.val := by
    by_contra! hh
    exact hgn (hi ▸ words_lt_eight i hh)
  have ha (a : A) : (a : S)=1 ∨ (a : S)=swap01 := by
    obtain ⟨j,hj⟩ := BorelKernel.words_complete a (hA a.property)
    rw [←hj]
    apply two_conjugates_cert i j hlarge
    intro v hv
    let v' : core (Fin 6) := ⟨v,hv⟩
    have hh (t : S) (ht : t ∈ P) :
        ρ t (ρ a v'-v')=ρ a v'-v' := by
      apply six_core_fixed_of_natural_fixed
      simpa only [map_sub,coreToNatural_equivariant] using hf t ht a a.property
        (coreToNatural (Fin 6) v')
    exact ⟨by simpa only [hi,hj,coreRepresentation_apply,Submodule.coe_sub,v'] using congrArg Subtype.val (hh g hg),
      by simpa only [hi,hj,coreRepresentation_apply,Submodule.coe_sub,v'] using congrArg Subtype.val (hh _ hg')⟩
  let f : A → Bool := fun a => if (a : S)=1 then false else true
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha1 : (a : S)=1 <;> by_cases hb1 : (b : S)=1
    · exact Subtype.ext (ha1.trans hb1.symm)
    · simp only [f,ha1,hb1,ite_true,ite_false] at hab
      cases hab
    · simp only [f,ha1,hb1,ite_true,ite_false] at hab
      cases hab
    · exact Subtype.ext (((ha a).resolve_left ha1).trans ((ha b).resolve_left hb1).symm)
  have hh := Nat.card_le_card_of_injective f hinj
  have hb : Nat.card Bool=2 := by simp
  omega
theorem conjugate_normal_large_le_plane (A P : Subgroup S) (u : S)
    (hA : A ≤ borel.map (MulAut.conj u).toMonoidHom)
    (hP : P ≤ borel.map (MulAut.conj u).toMonoidHom)
    (hn : borel.map (MulAut.conj u).toMonoidHom ≤ normalizer (P : Set S))
    (hc : 2 < Nat.card A)
    (hf : ∀ g ∈ P, ∀ a ∈ A, ∀ v, σ g (σ a v-v)=σ a v-v) :
    P ≤ D.map (MulAut.conj u).toMonoidHom := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have hback (H : Subgroup S) : (H.map (MulAut.conj u).toMonoidHom).map f = H :=
    conjBy_inv H u
  have hn' : borel ≤ normalizer (P.map f : Set S) := by
    rw [←hback borel]
    exact (map_mono hn).trans (le_normalizer_map f)
  have he (g : S) (v : natural (Fin 6)) : σ u (σ (f g) v) = σ g (σ u v) := by
    change σ u (σ (u⁻¹*g*u) v) = _
    simp only [map_mul,Module.End.mul_apply,(naturalRepresentation (Fin 6)).self_inv_apply]
  have hh := normal_large_le_plane (A.map f) (P.map f)
    ((map_mono hA).trans_eq (hback borel)) ((map_mono hP).trans_eq (hback borel))
    hn' (by rwa [card_map_of_injective (MulAut.conj u⁻¹).injective])
    (by
      rintro _ ⟨g,hg,rfl⟩ _ ⟨a,ha,rfl⟩ v
      apply (LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation (Fin 6)).asGroupHom u)).injective
      change σ u (σ (f g) (σ (f a) v-v)) = σ u (σ (f a) v-v)
      rw [he,map_sub,he,hf g hg a ha])
  have hout := map_mono (f := (MulAut.conj u).toMonoidHom) hh
  change (P.conjBy u⁻¹).conjBy u ≤ _ at hout
  rwa [conjBy_inv' P u] at hout
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelLargeModel
