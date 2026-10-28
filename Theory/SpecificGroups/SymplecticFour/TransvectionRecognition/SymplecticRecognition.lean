module
public import Theory.SpecificGroups.SymplecticFour.NativeFieldEmbedding
public import Theory.SpecificGroups.SymplecticFour.NativeTrace
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TraceModelConjugacy
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.AbsoluteSocle

/-!
# Recognizing a symplectic carrier from its original action

Let N be an irreducible subgroup of Sp₄(F), isomorphic to Sp₄(K) and normalized
by a transvection t. The carrier order supplies an embedding of K into F.
Every trace of N⟨t⟩ lies in the resulting coefficient subfield L: odd-order
classes are fixed by the |K|-th power, and every element of N⟨t⟩ has square
in N. Rank-one trace descent constructs a faithful action of N⟨t⟩ in Sp₄(L)
with an actual intertwiner. Its restriction to N is onto because the group
orders agree. Form uniqueness converts that intertwiner into an ambient
symplectic conjugator. The coefficient copy's normalizer then identifies
every original overgroup normalizing N.

This is the symplectic carrier step in Aschbacher--Smith G.4.1, printed
p.342, using the trace descent of G.4.8, printed p.340. The original E.2.7
consumer is `SourceSymplecticRecognized`.
-/

public noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes DiagramAutomorphisms.FieldFixedResidual
variable {F K : Type*} [Field F] [Finite F] [CharP F 2]
  [Field K] [Finite K] [CharP K 2]

omit [Finite F] [CharP F 2] in
private theorem overgroup_irreducible (N D : Subgroup (Sp F)) (hND : N ≤ D)
    (hi : IsIrreducible ((symplecticNatural 2).comp N.subtype)) :
    IsIrreducible ((symplecticNatural 2).comp D.subtype) := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let Q : Subrepresentation ((symplecticNatural 2).comp N.subtype) :=
    ⟨P.toSubmodule, fun n v hv => P.apply_mem_toSubmodule ⟨n.val, hND n.property⟩ hv⟩
  rcases hi.eq_bot_or_eq_top Q with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ((symplecticNatural 2).comp N.subtype) =>
      S.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ((symplecticNatural 2).comp N.subtype) =>
      S.toSubmodule) h

/-- An irreducible symplectic carrier normalized by a transvection is an
actual conjugate of the coefficient group over a subfield of the carrier
field's order. No identification of its given action is assumed. -/
theorem coefficient_copy_of_symplectic_carrier {n f : ℕ}
    (hF : Nat.card F = 2^n) (hf : 0<f) (hK : Nat.card K = 2^f)
    (N : Subgroup (Sp F))
    (hi : IsIrreducible ((symplecticNatural 2).comp N.subtype))
    (e : N ≃* Sp K) (t : Sp F) (ht : t ∈ normalizer (N : Set (Sp F)))
    (hb : IsB1 t) :
    ∃ L : Subfield F, Nat.card L = Nat.card K ∧ ∃ c : Sp F,
      N = (coefficientInclusion L).range.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨L,⟨eL⟩⟩ := NativeFieldEmbedding.subgroup_exists_subfield_equiv hf hK hF N e
  have hL : Nat.card L = Nat.card K := (Nat.card_congr eL.toEquiv).symm
  let D : Subgroup (Sp F) := N ⊔ zpowers t
  let ρ : Representation F D (Vector F) := (symplecticNatural 2).comp D.subtype
  let : ρ.IsIrreducible := overgroup_irreducible N D le_sup_left hi
  have htD : t ∈ D := (show zpowers t ≤ D from le_sup_right) (mem_zpowers t)
  have hr : Module.finrank F (LinearMap.range (ρ ⟨t,htD⟩ - 1)) = 1 := hb.2
  have ht2 : t^2=1 := by simpa only [hb.1] using pow_orderOf_eq_one t
  have htrace : ∀ x : D, LinearMap.trace F (Vector F) (ρ x) ∈ L := by
    intro x
    exact NativeTrace.join_character_mem hK N e L hL t ht2 ht x
  obtain ⟨M⟩ := TraceFieldDescent.exists_model_over_trace_subfield ρ ⟨t,htD⟩ hr
    (form F) TwoLocalCover.form_alternating TwoLocalCover.form_nondegenerate
    (fun x => preserves_form (x : Sp F)) L htrace
  obtain ⟨j,hj,A,hA⟩ := exists_symplectic_action_of_trace_model D L M
  let i : N →* D := Subgroup.inclusion le_sup_left
  let jN : N →* Sp L := j.comp i
  have hjN : Function.Injective jN := hj.comp (Subgroup.inclusion_injective le_sup_left)
  have hcard : Nat.card N = Nat.card (Sp L) := by
    rw [Nat.card_congr e.toEquiv, card_sp, card_sp, hL]
  let eN : N ≃* Sp L := MulEquiv.ofBijective jN
    ((Nat.bijective_iff_injective_and_card jN).mpr ⟨hjN,hcard⟩)
  have ha := subgroup_absolutelyIrreducible_of_isB1_normalizer N hi t ht hb
  obtain ⟨c,hc⟩ := exists_coefficient_conjugator_of_absolute_intertwiner N ha L eN A
    (fun x v => hA (i x) v)
  exact ⟨L,hL,c,hc⟩

/-- A normalizing overgroup containing the original transvection is the same
literal conjugate of the coefficient group. -/
theorem coefficient_copy_of_normalized_symplectic_carrier {n f : ℕ}
    (hF : Nat.card F = 2^n) (hf : 0<f) (hK : Nat.card K = 2^f)
    (H N : Subgroup (Sp F)) (hNH : N ≤ H)
    (hH : H ≤ normalizer (N : Set (Sp F)))
    (hi : IsIrreducible ((symplecticNatural 2).comp N.subtype))
    (e : N ≃* Sp K) (hex : ∃ t ∈ H, IsB1 t) :
    ∃ L : Subfield F, Nat.card L = Nat.card K ∧ ∃ c : Sp F,
      H = (coefficientInclusion L).range.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨t,ht,hb⟩ := hex
  obtain ⟨L,hL,c,hc⟩ := coefficient_copy_of_symplectic_carrier hF hf hK N hi e t (hH ht) hb
  refine ⟨L,hL,c,le_antisymm ?_ ?_⟩
  · rw [hc,conjugate_coefficient_range_normalizer] at hH
    exact hH
  · rw [←hc]
    exact hNH

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
