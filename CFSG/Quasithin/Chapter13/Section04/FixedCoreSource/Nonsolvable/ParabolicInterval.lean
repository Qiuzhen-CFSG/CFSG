module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Parabolics

/-!
# Selecting the outside member of a two-parabolic Sylow interval

Suppose N has exactly two proper overgroups of the common Sylow subgroup.
A proper inside overgroup A in M must be one of them. The other is the
unique minimal overgroup outside M, generates N with A, and intersects A
in precisely the original Sylow subgroup. All subgroups are transported
from N to the ambient group using N.subtype.

This common selection proof is used for the L₃(2), A₆ and S₆ quotient rows
in Aschbacher–Smith 13.4.10(7–8), printed p.909. The quotient recognition
and the inside overgroup remain with qt-d-1341-nonsolvable-source.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem unique_outside_of_interval
    (T : Sylow 2 G) (M N A B : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hN : N ∈ Chapter1.HOver G (T : Set G)) (hNM : ¬ N ≤ M)
    (hB : (T : Subgroup G) < B)
    (hBN : B < N) (hAM : A ≤ M)
    (hgen : A ⊔ B = N)
    (interval : ∀ U : Subgroup G, (T : Subgroup G) ≤ U → U ≤ N →
      U = (T : Subgroup G) ∨ U = A ∨ U = B ∨ U = N) :
    B ∈ Chapter3.HStar (T : Subgroup G) M ∧
      ∀ U ∈ Chapter3.HStar (T : Subgroup G) M, U ≤ N → U = B := by
  have hBM : ¬ B ≤ M := fun hb => hNM (hgen ▸ sup_le hAM hb)
  have hstar : B ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨Chapter3.mem_HOver_of_sylow_interval T hB.le hBN.le hN, hBM⟩, ?_⟩
    intro U hU hUB
    rcases interval U hU.1.2 (hUB.trans hBN.le) with he | he | he | he
    · exact (hU.2 (he ▸ hTM)).elim
    · exact (hU.2 (he ▸ hAM)).elim
    · exact he ▸ le_rfl
    · exact (hBN.not_ge (he ▸ hUB)).elim
  refine ⟨hstar, ?_⟩
  intro U hU hUN
  rcases interval U hU.1.1.2 hUN with he | he | he | he
  · exact (hU.1.2 (he ▸ hTM)).elim
  · exact (hU.1.2 (he ▸ hAM)).elim
  · exact he
  · have hNB : N ≤ B := he ▸ hU.2 hstar.1 (he.symm ▸ hBN.le)
    exact (hBN.not_ge hNB).elim

omit [Finite G] in
/-- The unique outside parabolic, its generation and its Sylow intersection,
from the intrinsic two-parabolic interval of the actual overgroup. -/
theorem unique_outside_of_sylow_pair
    (T : Sylow 2 G) (M N A : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hN : N ∈ Chapter1.HOver G (T : Set G)) (hNM : ¬ N ≤ M)
    (hTA : (T : Subgroup G) < A) (hAN : A < N) (hAM : A ≤ M)
    (pair : ∃ P Q : Subgroup N,
      IsCoatom P ∧ IsCoatom Q ∧ P ≠ Q ∧
      P ⊓ Q = ((T.subtype hN.2 : Sylow 2 N) : Subgroup N) ∧
      ((T.subtype hN.2 : Sylow 2 N) : Subgroup N) < P ∧
      ((T.subtype hN.2 : Sylow 2 N) : Subgroup N) < Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧
      ∀ U : Subgroup N, ((T.subtype hN.2 : Sylow 2 N) : Subgroup N) ≤ U →
        U = ((T.subtype hN.2 : Sylow 2 N) : Subgroup N) ∨
          U = P ∨ U = Q ∨ U = ⊤) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) M ∧ P < N ∧
      Group.IsSolvable P ∧ A ⊔ P = N ∧ A ⊓ P = (T : Subgroup G) ∧
      (∀ U ∈ Chapter3.HStar (T : Subgroup G) M, U ≤ N → U = P) := by
  let S := T.subtype hN.2
  obtain ⟨P,Q,hP,hQ,hPQ,hI,hSP,hSQ,hsP,hsQ,cover⟩ := pair
  have hSN : (S : Subgroup N).map N.subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le hN.2
  have htop : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have lift_lt {B C : Subgroup N} (h : B < C) :
      B.map N.subtype < C.map N.subtype :=
    (map_lt_map_iff_of_injective N.subtype_injective).mpr h
  have cover' : ∀ U : Subgroup G, (T : Subgroup G) ≤ U → U ≤ N →
      U = (T : Subgroup G) ∨ U = P.map N.subtype ∨ U = Q.map N.subtype ∨ U = N := by
    intro U hTU hUN
    have hSU : (S : Subgroup N) ≤ U.subgroupOf N := fun _ hx => hTU hx
    have heq := map_subgroupOf_eq_of_le hUN
    rcases cover (U.subgroupOf N) hSU with he | he | he | he
    · exact Or.inl (heq.symm.trans ((congrArg (fun U : Subgroup N => U.map N.subtype) he).trans hSN))
    · exact Or.inr (Or.inl (heq.symm.trans (congrArg (fun U : Subgroup N => U.map N.subtype) he)))
    · exact Or.inr (Or.inr (Or.inl (heq.symm.trans (congrArg (fun U : Subgroup N => U.map N.subtype) he))))
    · exact Or.inr (Or.inr (Or.inr (heq.symm.trans
        ((congrArg (fun U : Subgroup N => U.map N.subtype) he).trans htop))))
  have finish (P Q : Subgroup N) (hP : IsCoatom P) (hQ : IsCoatom Q) (hne : P ≠ Q)
      (hSQ : (S : Subgroup N) < Q)
      (hsQ : Group.IsSolvable Q) (hI : P ⊓ Q = (S : Subgroup N))
      (hc : ∀ U : Subgroup G, (T : Subgroup G) ≤ U → U ≤ N →
        U = (T : Subgroup G) ∨ U = P.map N.subtype ∨ U = Q.map N.subtype ∨ U = N)
      (hAP : A = P.map N.subtype) :
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) M ∧ P < N ∧
        Group.IsSolvable P ∧ A ⊔ P = N ∧ A ⊓ P = (T : Subgroup G) ∧
        (∀ U ∈ Chapter3.HStar (T : Subgroup G) M, U ≤ N → U = P) := by
    have hgen : A ⊔ Q.map N.subtype = N := by
      rw [hAP, ← Subgroup.map_sup, hP.sup_eq_top_of_ne hQ hne, htop]
    have hi : A ⊓ Q.map N.subtype = (T : Subgroup G) := by
      rw [hAP, ← map_inf _ _ _ N.subtype_injective, hI, hSN]
    have hQN : Q.map N.subtype < N := by
      have hh := lift_lt hQ.lt_top
      rwa [htop] at hh
    have hTQ : (T : Subgroup G) < Q.map N.subtype := hSN ▸ lift_lt hSQ
    have hu := unique_outside_of_interval T M N A (Q.map N.subtype) hTM hN hNM
      hTQ hQN hAM hgen (hAP.symm ▸ hc)
    let : Group.IsSolvable Q := hsQ
    have hsolv : Group.IsSolvable (Q.map N.subtype) :=
      Group.isSolvable_of_surjective (f :=
        (Q.equivMapOfInjective N.subtype N.subtype_injective).toMonoidHom)
        (Q.equivMapOfInjective N.subtype N.subtype_injective).surjective
    exact ⟨Q.map N.subtype, hu.1, hQN, hsolv, hgen, hi, hu.2⟩
  rcases cover' A hTA.le hAN.le with he | he | he | he
  · exact (hTA.ne he.symm).elim
  · exact finish P Q hP hQ hPQ hSQ hsQ hI cover' he
  · apply finish Q P hQ hP hPQ.symm hSP hsP ((inf_comm Q P).trans hI) ?_ he
    intro U hTU hUN
    rcases cover' U hTU hUN with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · exact (hAN.ne he).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
