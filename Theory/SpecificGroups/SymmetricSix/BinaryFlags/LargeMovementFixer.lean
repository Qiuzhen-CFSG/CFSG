module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.RestrictedMovement
public import Theory.GroupTheory.SubgroupConjugation
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.RestrictedMovement

/-!
# Two-subgroups fixing a large six-letter displacement

Inside a two-subgroup of S₆, a subgroup fixing every displacement of an
actor of order greater than two acts quadratically on the natural module.
In a canonical Borel, a checked sixteen-by-sixteen table records which
permutations fix each other's displacements on the augmentation core.
A nonquadratic pair can both fix only the displacements of 1 and (01),
contradicting the actor order. Natural fixed vectors lift to fixed core
vectors, so the same table applies to the natural quotient. Conjugation
and Sylow containment remove the choice of Borel.

The table records bit j in row i when i fixes the displacement of j;
each entry is checked against the literal permutation action. The small
pair certificate only consults these checked entries. The natural
replacement's Terminal/MidpointCore applies this to its entire midpoint
two-core, retaining both possible central covers.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the six-letter action in (3.3)(ii) and (5.12)(2), printed
pp.867 and 925--926. This proves quadratic action, without requiring
normalization by a full Borel or choosing one fixed three-pair marking.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open BinaryPermutation.SixCover
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.LargeMovementFixer
local notation "ρ" => coreRepresentation (Fin 6)
local notation "σ" => naturalRepresentation (Fin 6)
local notation "w" => BorelKernel.words
private def fixedTable (i j : Fin 16) : Bool :=
  ((![65535,65535,255,255,255,255,255,255,771,771,3,3,3,3,49155,49155] i) : Nat).testBit j.val

private theorem fixed_certificate : ∀ i j : Fin 16, fixedTable i j = true ↔
    ∀ v : Fin 6 → ZMod 2, (∑ k,v k)=0 →
      representation (Fin 6) (w i) (representation (Fin 6) (w j) v-v) =
        representation (Fin 6) (w j) v-v := by
  decide +kernel

private theorem pair_certificate : ∀ i j k : Fin 16,
    fixedTable j i = false → fixedTable i k = true → fixedTable j k = true →
      k=0 ∨ k=1 := by
  decide +kernel

private theorem card_le_two (A : Subgroup S)
    (hA : ∀ a ∈ A, a=1 ∨ a=swap01) : Nat.card A ≤ 2 := by
  let f : A → Bool := fun a => if (a : S)=1 then false else true
  have hi : Function.Injective f := by
    intro a b hab
    by_cases ha : (a : S)=1 <;> by_cases hb : (b : S)=1
    · exact Subtype.ext (ha.trans hb.symm)
    · simp only [f,ha,hb,ite_true,ite_false] at hab
      cases hab
    · simp only [f,ha,hb,ite_true,ite_false] at hab
      cases hab
    · exact Subtype.ext (((hA a a.property).resolve_left ha).trans
        ((hA b b.property).resolve_left hb).symm)
  simpa using Nat.card_le_card_of_injective f hi

theorem borel_large_fixer_quadratic (A P : Subgroup S)
    (hA : A ≤ borel) (hP : P ≤ borel) (hc : 2 < Nat.card A)
    (hf : ∀ g ∈ P, ∀ a ∈ A, ∀ v, σ g (σ a v-v)=σ a v-v) :
    ∀ g ∈ P, ∀ k ∈ P, ∀ v, σ k (σ g v-v)=σ g v-v := by
  intro g hg k hk v
  obtain ⟨i,rfl⟩ := BorelKernel.words_complete g (hP hg)
  obtain ⟨j,rfl⟩ := BorelKernel.words_complete k (hP hk)
  have htab : fixedTable j i = true := by
    by_contra hh
    have hfalse : fixedTable j i = false := Bool.eq_false_iff.mpr hh
    apply (not_le_of_gt hc) (card_le_two A ?_)
    intro a ha
    obtain ⟨l,rfl⟩ := BorelKernel.words_complete a (hA ha)
    have hentry (m : Fin 16) (hm : w m ∈ P) : fixedTable m l = true := by
      apply (fixed_certificate m l).mpr
      intro z hz
      let z' : core (Fin 6) := ⟨z,hz⟩
      have he : ρ (w m) (ρ (w l) z'-z')=ρ (w l) z'-z' := by
        apply six_core_fixed_of_natural_fixed
        simpa only [map_sub,coreToNatural_equivariant] using
          hf (w m) hm (w l) ha (coreToNatural (Fin 6) z')
      exact congrArg Subtype.val he
    rcases pair_certificate i j l hfalse (hentry i hg) (hentry j hk) with rfl | rfl
    · left
      decide
    · right
      decide
  obtain ⟨z,rfl⟩ := coreToNatural_surjective v
  have hh : ρ (w j) (ρ (w i) z-z)=ρ (w i) z-z :=
    Subtype.ext ((fixed_certificate j i).mp htab z.val z.property)
  have he := congrArg (coreToNatural (Fin 6)) hh
  simpa only [map_sub,coreToNatural_equivariant] using he

theorem conjugate_large_fixer_quadratic (A P : Subgroup S) (u : S)
    (hA : A ≤ borel.map (MulAut.conj u).toMonoidHom)
    (hP : P ≤ borel.map (MulAut.conj u).toMonoidHom) (hc : 2 < Nat.card A)
    (hf : ∀ g ∈ P, ∀ a ∈ A, ∀ v, σ g (σ a v-v)=σ a v-v) :
    ∀ g ∈ P, ∀ k ∈ P, ∀ v, σ k (σ g v-v)=σ g v-v := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have hback (H : Subgroup S) : (H.map (MulAut.conj u).toMonoidHom).map f = H :=
    conjBy_inv H u
  have he (g : S) (v : natural (Fin 6)) : σ u (σ (f g) v) = σ g (σ u v) := by
    change σ u (σ (u⁻¹*g*u) v) = _
    simp only [map_mul,Module.End.mul_apply,(naturalRepresentation (Fin 6)).self_inv_apply]
  have hh := borel_large_fixer_quadratic (A.map f) (P.map f)
    ((map_mono hA).trans_eq (hback borel)) ((map_mono hP).trans_eq (hback borel))
    (by rwa [card_map_of_injective (MulAut.conj u⁻¹).injective])
    (by
      rintro _ ⟨g,hg,rfl⟩ _ ⟨a,ha,rfl⟩ v
      apply (LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation (Fin 6)).asGroupHom u)).injective
      change σ u (σ (f g) (σ (f a) v-v)) = σ u (σ (f a) v-v)
      rw [he,map_sub,he,hf g hg a ha])
  intro g hg k hk v
  have h := congrArg (σ u) (hh (f g) (mem_map_of_mem f hg) (f k) (mem_map_of_mem f hk) (σ u⁻¹ v))
  simpa only [he,map_sub,(naturalRepresentation (Fin 6)).self_inv_apply] using h

theorem two_group_large_fixer_quadratic (T A P : Subgroup S)
    (hT : IsPGroup 2 T) (hA : A ≤ T) (hP : P ≤ T) (hc : 2 < Nat.card A)
    (hf : ∀ g ∈ P, ∀ a ∈ A, ∀ v, σ g (σ a v-v)=σ a v-v) :
    ∀ g ∈ P, ∀ k ∈ P, ∀ v, σ k (σ g v-v)=σ g v-v := by
  obtain ⟨T₀,hTT₀⟩ := hT.exists_le_sylow
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq S borelSylow T₀
  have he : (T₀ : Subgroup S) = borel.map (MulAut.conj u).toMonoidHom :=
    (congrArg (fun P : Sylow 2 S => (P : Subgroup S)) hu).symm
  exact conjugate_large_fixer_quadratic A P u ((hA.trans hTT₀).trans_eq he)
    ((hP.trans hTT₀).trans_eq he) hc hf

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.LargeMovementFixer
