module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.CharacterData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationData
public import Theory.GroupAction.SimpleCosets
public import Theory.Character.MinimalDegree
public import Theory.Character.PermutationActionCharacter

/-!
# The degree-22 coset action and its character

For any subgroup of index 22, the minimum irreducible degree and uniqueness
in `Degree21Character` force its permutation character to be `1 + chi`.
The normal core gives faithfulness in a simple group. The sign map is trivial
because a simple group of order greater than two cannot embed in the sign
group. Relabeling the cosets preserves each fixed-point set by an explicit
bijection, giving all nine required order/fixed-point pairs on `Fin 22`.

This proves the conditional action step at the start of Janko (1968),
Section 9, p.17, DOI 10.1016/0021-8693(68)90002-1. The character and the
index-22 subgroup must still be constructed from the local hypotheses.
-/

noncomputable section
open Representation
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
universe u
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] Fintype.ofFinite

/-- The transitive coset character is the principal character plus the unique
irreducible character of degree 21. -/
public theorem coset_character (C : Degree21Character G) (H : Subgroup G)
    (hH : H.index = 22) (g : G) :
    (permutationAction G (G ⧸ H)).character g = 1 + C.chi g := by
  classical
  have hdegree : (permutationAction G (G ⧸ H)).character 1 = (21 + 1 : ℕ) := by
    rw [char_one]
    simp only [Module.finrank_pi]
    exact_mod_cast (Nat.card_eq_fintype_card (α := G ⧸ H)).symm.trans
      (H.index_eq_card.symm.trans hH)
  obtain ⟨theta, hirr, hdeg, htheta⟩ := Theory.Character.eq_one_add_irreducible_of_min_degree
    (permutationAction G (G ⧸ H)) 21 (by decide) hdegree
    (permutationAction_scalarProduct_one_of_pretransitive G (G ⧸ H)) C.minimum
  rw [C.unique theta hirr hdeg] at htheta
  exact htheta g

private def cosetLabeling (H : Subgroup G) (hH : H.index = 22) : (G ⧸ H) ≃ Fin 22 :=
  Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card (α := G ⧸ H)).symm.trans
    (H.index_eq_card.symm.trans hH))

/-- The natural left coset action, transported to the twenty-two labels. -/
public def cosetAction (H : Subgroup G) (hH : H.index = 22) : G →* Equiv.Perm (Fin 22) :=
  (cosetLabeling H hH).permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))

/-- Simplicity makes the index-22 coset action faithful. -/
public theorem cosetAction_faithful [IsSimpleGroup G] (H : Subgroup G) (hH : H.index = 22) :
    Function.Injective (cosetAction H hH) := by
  have hproper : H ≠ ⊤ := by
    intro he
    have hh := Subgroup.index_eq_one.mpr he
    omega
  let := H.faithfulSMul_quotient_of_simple hproper
  exact (cosetLabeling H hH).permCongrHom.injective.comp MulAction.toPerm_injective

omit [Finite G] in
/-- The sign character of a simple group of order greater than two is trivial. -/
public theorem even_of_simple [IsSimpleGroup G] (hG : 2 < Nat.card G)
    (rho : G →* Equiv.Perm (Fin 22)) (g : G) : rho g ∈ alternatingGroup (Fin 22) := by
  let f : G →* ℤˣ := Equiv.Perm.sign.comp rho
  rw [Equiv.Perm.mem_alternatingGroup]
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · have hi := (MonoidHom.ker_eq_bot_iff f).mp h
    have hc := Nat.card_le_card_of_injective f hi
    have htwo : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
    rw [htwo] at hc
    omega
  · exact congrArg (fun f : G →* ℤˣ => f g) (MonoidHom.ker_eq_top_iff.mp h)

/-- Relabeling gives a bijection on the fixed points of each element. -/
public theorem cosetAction_fixed_card (H : Subgroup G) (hH : H.index = 22) (g : G) :
    (Finset.univ.filter (fun x => cosetAction H hH g x = x)).card =
      Nat.card (MulAction.fixedBy (G ⧸ H) g) := by
  classical
  let e := cosetLabeling H hH
  have hfix (x : G ⧸ H) : cosetAction H hH g (e x) = e (g • x) := by
    simp [cosetAction, e, Equiv.permCongrHom, Equiv.permCongr_apply]
  let f : MulAction.fixedBy (G ⧸ H) g ≃
      {y : Fin 22 // cosetAction H hH g y = y} :=
    { toFun := fun x => ⟨e x, by rw [hfix, x.property]⟩
      invFun := fun y => ⟨e.symm y, by
        apply e.injective
        rw [← hfix, e.apply_symm_apply, y.property]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  have hh := Nat.card_congr f
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hh.symm


/-- The degree-21 character table determines the nine exact order/fixed-point pairs. -/
public theorem cosetAction_order_fixed (C : Degree21Character G) (H : Subgroup G)
    (hH : H.index = 22) (g : G) :
    (orderOf g, (Finset.univ.filter (fun x => cosetAction H hH g x = x)).card) ∈
      allowedOrderFixedPairs := by
  classical
  rw [cosetAction_fixed_card]
  have hc : (Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℂ) = 1 + C.chi g := by
    rw [← permutationAction_character]
    exact coset_character C H hH g
  rcases C.values g with ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ |
    ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩
  all_goals
    rw [hv] at hc
    norm_num at hc
    norm_cast at hc
    simp [allowedOrderFixedPairs, ho, hc]

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
