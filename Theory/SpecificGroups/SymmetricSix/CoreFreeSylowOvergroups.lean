module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Proper Sylow overgroups of S6 are core-free

Any nontrivial normal subgroup contains A6. A proper overgroup of a full
Sylow subgroup cannot contain A6, since its order is divisible by sixteen.
Thus its normal core is trivial. This supplies the literal relative core
in the binary symplectic pair of E.2.7, printed pp.219–220.
-/

public section
namespace Theory.SpecificGroups.SymmetricSix
open Subgroup Theory.SpecificGroups.SymmetricSix
variable {X : Type*} [Group X] [Finite X]

/-- Every proper Sylow overgroup of the literal S6 model has trivial normal core. -/
theorem normalCore_eq_bot_of_sylow_le (e : X ≃* Equiv.Perm (Fin 6))
    (S : Sylow 2 X) (A : Subgroup X) (hSA : (S : Subgroup X) ≤ A) (hA : A ≠ ⊤) :
    A.normalCore = ⊥ := by
  by_contra hne
  let N := A.normalCore.map e.toMonoidHom
  let : N.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  have hN : N ≠ ⊥ := fun hh => hne ((A.normalCore.map_eq_bot_iff_of_injective e.injective).mp hh)
  have hn : Nontrivial N := (nontrivial_iff_ne_bot _).mpr hN
  have hAlt : alternatingGroup (Fin 6) ≤ A.map e.toMonoidHom :=
    (Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) hn).trans
      (map_mono A.normalCore_le)
  have hd : (A.map e.toMonoidHom).index ∣ 2 :=
    (alternatingGroup.index_eq_two (α := Fin 6)) ▸ index_dvd_of_le hAlt
  have hp : A.map e.toMonoidHom ≠ ⊤ := by
    intro hh
    exact hA (e.mapSubgroup.injective (hh.trans e.mapSubgroup.map_top.symm))
  have hidx : (A.map e.toMonoidHom).index = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun hh => hp (index_eq_one.mp hh))
  have heq := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have hs : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,Nat.card_congr e.toEquiv,s6_order]
    decide +kernel
  have hdiv := card_dvd_of_le (map_mono (f := e.toMonoidHom) hSA)
  rw [card_map_of_injective e.injective,hs,heq,a6_order] at hdiv
  norm_num at hdiv
end Theory.SpecificGroups.SymmetricSix
