module

public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.SpecificGroups.SymmetricEight.TranspositionAutomorphisms
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The actual eight-point action of a normalizer

Given K ≃ A₈, conjugation on K, transport to Aut(A₈), and the inverse
of S₈ ≃ Aut(A₈) give one homomorphism N_G(K) → S₈. Its restriction to
K is the supplied equivalence followed by the alternating inclusion.
A normalizing element centralizing a proper component of K∩C_G(z)
cannot have trivial image: that would make the proper component subnormal
in the simple group K.

This is the action transport used in Aschbacher–Smith, 16.3.11(3), printed
p.1181. The construction preserves conjugation, rather than merely
comparing the abstract isomorphism types of the groups.
-/

open Subgroup Equiv Equiv.Perm
@[expose] public noncomputable section
namespace Theory.SpecificGroups.SymmetricEight.ComponentMarking
variable {G : Type*} [Group G] (K : Subgroup G)

def symmetricAutEquiv : Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))

def normalizerRepresentation (e : K ≃* alternatingGroup (Fin 8)) :
    normalizer (K : Set G) →* Perm (Fin 8) :=
  symmetricAutEquiv.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp K.normalizerMonoidHom)

theorem normalizerRepresentation_conj (e : K ≃* alternatingGroup (Fin 8))
    (g : normalizer (K : Set G)) (x : K) :
    (e (K.normalizerMonoidHom g x) : Perm (Fin 8)) =
      normalizerRepresentation K e g * (e x : Perm (Fin 8)) * (normalizerRepresentation K e g)⁻¹ := by
  have he : MulAut.conjNormal (normalizerRepresentation K e g) =
      MulAut.congr e (K.normalizerMonoidHom g) :=
    symmetricAutEquiv.apply_symm_apply _
  have hx := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) => (f (e x)).val) he
  simpa only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] using hx.symm

theorem normalizerRepresentation_on_subgroup (e : K ≃* alternatingGroup (Fin 8)) (x : K) :
    normalizerRepresentation K e ⟨x, K.le_normalizer x.property⟩ = e x := by
  apply symmetricAutEquiv.injective
  change symmetricAutEquiv (symmetricAutEquiv.symm _) = MulAut.conjNormal (e x).val
  rw [symmetricAutEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change (e (⟨x.val * (e.symm y).val * x.val⁻¹, _⟩ : K)).val =
    (e x).val * y.val * (e x).val⁻¹
  change (e (x * e.symm y * x⁻¹)).val = _
  simp

end Theory.SpecificGroups.SymmetricEight.ComponentMarking

namespace Theory.SpecificGroups.SymmetricEight.ComponentMarking
open Theory.GroupTheory
variable {G : Type*} [Group G] {K L : Subgroup G} {z : G}

theorem normalizerRepresentation_ne_one (e : K ≃* alternatingGroup (Fin 8))
    (hz : z ∈ normalizer (K : Set G)) (hLK : L < K)
    (hL : IsComponentIn L (K ⊓ centralizer ({z} : Set G))) :
    normalizerRepresentation K e ⟨z, hz⟩ ≠ 1 := by
  intro he
  have hact : K.normalizerMonoidHom ⟨z, hz⟩ = 1 := by
    apply (MulAut.congr e).injective
    apply symmetricAutEquiv.symm.injective
    simpa only [normalizerRepresentation, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_one] using he
  have hzC : z ∈ centralizer (K : Set G) := by
    have hm : (⟨z, hz⟩ : normalizer (K : Set G)) ∈ K.normalizerMonoidHom.ker := hact
    rw [normalizerMonoidHom_ker] at hm
    exact hm
  have hC : K ⊓ centralizer ({z} : Set G) = K := by
    apply inf_eq_left.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hzC) x hx)
  rw [hC] at hL
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup K := e.isSimpleGroup
  rcases hL.2.1.eq_bot_or_top_of_isSimpleGroup (inferInstance : IsSimpleGroup K) with hb | ht
  · apply hL.ne_bot
    simpa only [map_subgroupOf_eq_of_le hLK.le, Subgroup.map_bot] using
      congrArg (Subgroup.map K.subtype) hb
  · exact hLK.not_ge (subgroupOf_eq_top.mp ht)

end Theory.SpecificGroups.SymmetricEight.ComponentMarking
