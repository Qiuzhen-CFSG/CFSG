module
public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget

/-!
# Three conjugate involutions generate PSL2(11)

The checked root-element words for the standard involution generate the
projective group. Involution fusion transports those same three conjugators
to every involution, and a finite-field isomorphism preserves the actual
PSL2 carrier. Source application: Aschbacher--Smith, proof of 12.6.26,
printed p.833; the concrete words are in ElevenConjugateBudget.Generation.
-/

public section
open Subgroup
namespace Theory.PSL2.ElevenConjugateBudget
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem model_three_involutions :
    closure (Set.range fun i : Fin 3 => triple i * t * (triple i)⁻¹) = ⊤ := by
  let J := closure (Set.range fun i : Fin 3 => triple i * t * (triple i)⁻¹)
  have hm (i : Fin 3) : MulAut.conj (triple i * t * (triple i)⁻¹) ∈
      J.map (MulAut.conj : S →* MulAut S) :=
    mem_map_of_mem _ (subset_closure ⟨i,rfl⟩)
  have hh := inner_triple_generates (J.map (MulAut.conj : S →* MulAut S))
    (by simpa [triple] using hm 0) (by simpa [triple] using hm 1)
    (by simpa [triple] using hm 2)
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hh (show MulAut.conj x ∈ (MulAut.conj : S →* MulAut S).range from ⟨x,rfl⟩)
  have hi := Theory.GroupTheory.conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F)
  exact hi he ▸ hy

/-- Three conjugates of any involution generate the actual PSL2(11). -/
theorem three_involution_conjugates {B : Type*} [_root_.Group B]
    (e : B ≃* S) (v : B) (hv : orderOf v = 2) :
    ∃ c : Fin 3 → B, closure (Set.range fun i => c i * v * (c i)⁻¹) = ⊤ := by
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (Theory.PSL2.involutions_isConj t (e v) (orderOf_eq_prime t_sq t_ne_one)
      ((e.orderOf_eq v).trans hv))
  let a : S ≃* B := (MulAut.conj g).trans e.symm
  have ht : a t = v := by
    change e.symm (g*t*g⁻¹)=v
    rw [hg,e.symm_apply_apply]
  refine ⟨fun i => a (triple i),?_⟩
  have hh := congrArg (Subgroup.map a.toMonoidHom) model_three_involutions
  simpa only [MonoidHom.map_closure, ←Set.range_comp, Function.comp_def,
    MulEquiv.coe_toMonoidHom,map_mul,map_inv,ht,
    Subgroup.map_top_of_surjective a.toMonoidHom a.surjective] using hh

/-- The same generation statement over every finite field of order eleven. -/
theorem three_involution_conjugates_of_card
    {B K : Type*} [_root_.Group B] [Field K] [Finite K]
    (hK : Nat.card K = 11)
    (e : B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (v : B) (hv : orderOf v = 2) :
    ∃ c : Fin 3 → B, closure (Set.range fun i => c i * v * (c i)⁻¹) = ⊤ := by
  let : Fintype K := Fintype.ofFinite K
  let eF : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card,←Nat.card_eq_fintype_card,hK])
  exact three_involution_conjugates (e.trans (GorensteinWalter.psl2RingEquiv eF)) v hv
end Theory.PSL2.ElevenConjugateBudget

