module
public import Theory.Mathieu.M22.CubicHexad.Invariance

/-!
# An invariant cubic hexad pair over every Sylow subgroup of M₂₂

Sylow conjugacy transports the two marked cubic subgroups together. Their
S₃ quotients, invariance under every Sylow-preserving automorphism, perfect
hexad join, and genuine embedded A₆ section are retained by the same map.
This supplies the concrete input to the central-three-cover lifting used in
Aschbacher–Smith 14.3.6(6), printed p.994.
-/

public section
open Subgroup MulAction
namespace Sporadic.Mathieu.M22CubicHexad
open M22ValueBound.Concrete M22ValueBound.Concrete.PartitionStructure M22SolvableSylow

/-- The two invariant cubic overgroups generate a perfect hexad section
containing an actual A₆ subgroup. -/
theorem exists_invariant_cubic_hexad_pair (P : Sylow 2 M22) :
    ∃ J₁ J₂ : Subgroup M22,
      (P : Subgroup M22) ≤ J₁ ∧ (P : Subgroup M22) ≤ J₂ ∧
      (P : Subgroup M22).relIndex J₁ = 3 ∧ (P : Subgroup M22).relIndex J₂ = 3 ∧
      (∀ a : MulAut M22, (P : Subgroup M22).map a.toMonoidHom = P →
        J₁.map a.toMonoidHom = J₁ ∧ J₂.map a.toMonoidHom = J₂) ∧
      Nonempty ((J₁ ⧸ pCore 2 J₁) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((J₂ ⧸ pCore 2 J₂) ≃* Equiv.Perm (Fin 3)) ∧
      Group.IsPerfect (J₁ ⊔ J₂ : Subgroup M22) ∧
      ∃ j : alternatingGroup (Fin 6) →* (J₁ ⊔ J₂ : Subgroup M22),
        Function.Injective j := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 fixedSylow P
  let a := MulAut.conj g
  have hmap : (fixedSylow : Subgroup M22).map a.toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  let J₁ := M22SolvableSylow.pairHexad.map a.toMonoidHom
  let J₂ := second.map a.toMonoidHom
  have hi₁ : (P : Subgroup M22).relIndex J₁ = 3 := by
    rw [← hmap, relIndex_map_map_of_injective (f := a.toMonoidHom) _ _ a.injective]
    exact fixedSylow_index_pair
  have hi₂ : (P : Subgroup M22).relIndex J₂ = 3 := by
    rw [← hmap, relIndex_map_map_of_injective (f := a.toMonoidHom) _ _ a.injective]
    exact fixedSylow_index_second
  have hinv (b : MulAut M22) (hb : (P : Subgroup M22).map b.toMonoidHom = P) :
      J₁.map b.toMonoidHom = J₁ ∧ J₂.map b.toMonoidHom = J₂ := by
    let d : MulAut M22 := a.trans (b.trans a.symm)
    have hd : a.toMonoidHom.comp d.toMonoidHom = b.toMonoidHom.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact a.apply_symm_apply _
    have hdP : (fixedSylow : Subgroup M22).map d.toMonoidHom = fixedSylow := by
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [map_map, hd, ← map_map, hmap, hb]
    obtain ⟨h₁, h₂⟩ := fixed_pair_invariant d hdP
    constructor
    · change (M22SolvableSylow.pairHexad.map a.toMonoidHom).map b.toMonoidHom = _
      rw [map_map, ← hd, ← map_map, h₁]
    · change (second.map a.toMonoidHom).map b.toMonoidHom = _
      rw [map_map, ← hd, ← map_map, h₂]
  let e₁ : M22SolvableSylow.pairHexad ≃* J₁ :=
    M22SolvableSylow.pairHexad.equivMapOfInjective a.toMonoidHom a.injective
  let e₂ : second ≃* J₂ := second.equivMapOfInjective a.toMonoidHom a.injective
  have hjoin : J₁ ⊔ J₂ = m22HexadStabilizer.map a.toMonoidHom := by
    dsimp [J₁, J₂]
    rw [← Subgroup.map_sup, pair_sup_second]
  let eH : m22HexadStabilizer ≃* (J₁ ⊔ J₂ : Subgroup M22) :=
    (m22HexadStabilizer.equivMapOfInjective a.toMonoidHom a.injective).trans
      (MulEquiv.subgroupCongr hjoin.symm)
  let : Group.IsPerfect m22HexadStabilizer := m22HexadStabilizer_isPerfect m22Hexad123_mem
  refine ⟨J₁, J₂, hmap ▸ map_mono fixedSylow_le_pair,
    hmap ▸ map_mono (show (fixedSylow : Subgroup M22) ≤ second from
      fixedSylow_coe ▸ inf_le_right), hi₁, hi₂, hinv, ?_, ?_, ?_, ?_⟩
  · exact ⟨(QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)).symm.trans pairQuotientEquiv⟩
  · exact ⟨(QuotientGroup.congr _ _ e₂ (pCore_map_iso 2 e₂)).symm.trans secondQuotientEquiv⟩
  · exact Group.IsPerfect.ofSurjective (f := eH.toMonoidHom) eH.surjective
  · exact ⟨eH.toMonoidHom.comp (m22HexadSection m22Hexad123_mem),
      eH.injective.comp (m22HexadSection_injective m22Hexad123_mem)⟩

end Sporadic.Mathieu.M22CubicHexad
