module
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Centralization by maximal elementary subgroups in a local group

Let S be the ambient image of a Sylow two-subgroup of B, and let B
normalize W. If J(S) centralizes W, then every elementary subgroup of B
having the same order as a maximal elementary subgroup of S centralizes W.
Sylow conjugacy puts that subgroup into S; maximality and normalization
then transport centralization back. All embeddings remain literal.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemmas 12.6.6 and 12.6.9, printed pp.824--825.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Centralization transfers to every elementary subgroup of the same maximal order. -/
theorem maxElementary_centralizes_of_local_card
    (B S W A E : Subgroup G) (P : Sylow 2 B)
    (hP : (P : Subgroup B).map B.subtype = S)
    (hn : B ≤ normalizer (W : Set G))
    (hJ : elementaryAbelianMaxJ S ≤ centralizer (W : Set G))
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hEB : E ≤ B) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card A = Nat.card E) : E ≤ centralizer (W : Set G) := by
  obtain ⟨R,hR⟩ := (hE.isPGroup.comap_subtype (K := B)).exists_le_sylow
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq B R P
  let e := MulAut.conj (b : G)
  have hEP : E.map e.toMonoidHom ≤ S := by
    rw [←hP]
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨b * ⟨x,hEB hx⟩ * b⁻¹,?_,rfl⟩
    have hp : (R : Subgroup B).map (MulAut.conj b).toMonoidHom = (P : Subgroup B) := by
      change ((b • R : Sylow 2 B) : Subgroup B) = (P : Subgroup B)
      rw [hb]
    rw [←hp]
    exact mem_map_of_mem _ (hR hx)
  have hmax : E.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups S := by
    refine ⟨hEP,hE.map _,?_⟩
    intro F hFS hF
    rw [card_map_of_injective e.injective,←hc]
    exact hA.2.2 F hFS hF
  intro x hx w hw
  have hwf : (b : G)*w*(b : G)⁻¹ ∈ W := (hn b.property w).mp hw
  have hhf := hJ (le_sSup hmax (mem_map_of_mem e.toMonoidHom hx)) _ hwf
  change ((b : G)*w*(b : G)⁻¹)*((b : G)*x*(b : G)⁻¹) =
    ((b : G)*x*(b : G)⁻¹)*((b : G)*w*(b : G)⁻¹) at hhf
  have heq := congrArg (fun z : G => (b : G)⁻¹*z*b) hhf
  simpa only [e,MulAut.conj_apply,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,
    inv_mul_cancel,mul_inv_cancel,mul_one,one_mul] using heq
end Theory.GroupTheory
