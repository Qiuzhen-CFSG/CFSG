module
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
public import Theory.GroupTheory.PResidual.PrimeSectionHom
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The marked-five residual in an A₅ Sylow stabilizer

The automorphism stabilizer of an A₅ Sylow four-group fixes a point in
S₅, so has order dividing 24. A two-perfect group whose two-core quotient
has order five acts trivially there. Applied to the literal normalizer
action on K/O₂(K), this places the actor commutators inside O₂(K).

Source: Aschbacher--Smith 15.2.4, printed p.1106, the Sylow branch after
C.2.5 and A.3.14 identify the overcomponent with the original A₅ component.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.Alternating.FiveSylowFiveResidual
theorem five_residual_sylow_action_eq_one {E : Type*} [Group E] [Finite E] (h : IsPPerfect 2 E)
    (hc : Nat.card (E ⧸ pCore 2 E) = 5)
    (S : Sylow 2 (alternatingGroup (Fin 5)))
    (a : E →* MulAut (alternatingGroup (Fin 5)))
    (hS : ∀ x, (S : Subgroup _).map (a x).toMonoidHom = S) : a = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨i,hi⟩ := FiveSylowRadical.sylow_stabilizer_fixes_point S
  let f : E →* Equiv.Perm (Fin 5) := FiveExtensionAction.symmetricAutEquiv.symm.toMonoidHom.comp a
  have hfix (x : E) : f x i = i := hi _ (hS x)
  let g := f.codRestrict (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) hfix
  have hcard : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) = 24 := by
    have hh := (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).card_mul_index
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_perm] at hh
    norm_num [Nat.factorial,Nat.card_fin] at hh
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {g : Equiv.Perm (Fin 5) // g i = i} = 24
    omega
  have hg := hom_eq_one_of_prime_core_quotient h (by decide : Nat.Coprime 2 5) hc
    (by rw [hcard]; decide) g
  apply MonoidHom.ext
  intro x
  apply FiveExtensionAction.symmetricAutEquiv.symm.injective
  exact (congrArg Subtype.val (DFunLike.congr_fun hg x)).trans (map_one _).symm

open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]
theorem commutator_le_core_of_five_residual_sylow_normalizing (Y K : Subgroup G) (hp : IsPPerfect 2 Y)
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hYK : Y ≤ normalizer (K : Set G))
    (S : Sylow 2 K)
    (hYS : Y ≤ normalizer (((S : Subgroup K).map K.subtype) : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ⁅Y,K⁆ ≤ K.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let a : Y →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr e).toMonoidHom.comp ((quotientAut (pCore 2 K)).comp
      (K.normalizerMonoidHom.comp (inclusion hYK)))
  have ha (y : Y) (k : K) : a y (f k) =
      f (K.normalizerMonoidHom (inclusion hYK y) k) := by
    change e (quotientAut (pCore 2 K) _ (e.symm (e (q k)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  let S' := S.mapSurjective hf
  have hS' (y : Y) : (S' : Subgroup _).map (a y).toMonoidHom = S' := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (a y).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change a y (f k) ∈ (S' : Subgroup _)
    rw [ha]
    apply mem_map_of_mem
    have hs := le_normalizer_iff.mp hYS y y.property (k:G)
      (mem_map_of_mem K.subtype hk)
    obtain ⟨k',hk',he⟩ := hs
    have he' : k' = K.normalizerMonoidHom (inclusion hYK y) k := Subtype.ext he
    exact he' ▸ hk'
  have heq := five_residual_sylow_action_eq_one hp hc S' a hS'
  apply commutator_le.mpr
  intro y hy k hk
  let y' : Y := ⟨y,hy⟩
  let k' : K := ⟨k,hk⟩
  have hh := ha y' k'
  rw [heq] at hh
  have hh' : q (K.normalizerMonoidHom (inclusion hYK y') k') = q k' :=
    e.injective hh.symm
  have hn : K.normalizerMonoidHom (inclusion hYK y') k' * k'⁻¹ ∈ pCore 2 K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (_ * k'⁻¹) = 1
    rw [map_mul,map_inv,hh',mul_inv_cancel]
  exact mem_map_of_mem K.subtype hn

end Theory.SpecificGroups.Alternating.FiveSylowFiveResidual
