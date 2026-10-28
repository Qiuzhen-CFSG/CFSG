module
public import Theory.Representation.BinaryTensorThree.NormalizerNonFF
public import Theory.Representation.BinaryTensorThree.Irreducible
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.Representation.RepEquiv
public import Theory.Representation.Quotient
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# Stability of binary tensor constituents under the whole ambient group

An elementary actor faithful on a normal GL₃(2) square has rank at most four.
Under the source bound on fixed codimension, each of its elements moves at
most eight dimensions. A nine-dimensional simple tensor constituent therefore
cannot meet a distinct translate under the actor: such a translate would force
at least nine moved dimensions. This makes every tensor constituent a module
for the join of the original actor and the normal square.

Two disjoint tensor constituents would now exceed twice that same actor's
rank, by the full tensor normalizer's non-FF theorem. Every ambient translate
is another marked tensor constituent, so all ambient elements preserve it.
No stability, faithful ambient action or semisimplicity premise is assumed.

Source: Aschbacher--Smith D.3.7, D.3.9 and F.9.18(2--5),
printed pp.197--200,325--326. The literal terminal quotient application is in
Chapter14/Section06/SourceSuitableChoice/ComponentSupports/Modules/Recognition.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace BinaryTensorThree

/-- The two independent natural factors act irreducibly on the tensor. -/
theorem baseRepresentation_irreducible : baseRepresentation.IsIrreducible := by
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
  intro S
  have hs := additive_invariant_eq_bot_or_top S.toSubmodule.toAddSubgroup
    (fun g X hX => S.apply_mem_toSubmodule g hX)
  rcases hs with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.toAddSubgroup_injective h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.toAddSubgroup_injective h

private def factorEquiv : Matrix.PSL3Two.SL ≃* Factor :=
  Matrix.PSL3Two.equivGL.trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Natural))

/-- The automorphism group of the actual tensor base has two-rank at most four. -/
theorem automorphism_square_rank_le_four :
    primeRank 2 (MulAut (Factor × Factor)) ≤ 4 := by
  have hr : primeRank 2 (MulAut Matrix.PSL3Two.SL) = 2 := by
    rw [primeRank_equiv 2 (MulAut.congr Matrix.PSL3Two.equiv)]
    exact Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)
  rw [←primeRank_equiv 2 (MulAut.congr (factorEquiv.prodCongr factorEquiv))]
  have h := AutomorphismSquare.rank_bound Matrix.PSL3Two.center_eq_bot
    (show 0 < primeRank 2 (MulAut Matrix.PSL3Two.SL) by omega)
  omega

variable {D V : Type*} [_root_.Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Faithful conjugation on the original normal tensor base bounds actor rank. -/
theorem rank_le_four_of_faithful_on_tensor_base
    (N A : Subgroup D) [N.Normal] (hA : IsElementaryTwo A)
    (hAC : A ⊓ centralizer (N : Set D) = ⊥)
    (e : N ≃* Factor × Factor) : rank A ≤ 4 := by
  let f : A →* MulAut N := (MulAut.conjNormal : D →* MulAut N).comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hAC]
    refine ⟨a.property,?_⟩
    change (a : D) ∈ (MulAut.conjNormal : D →* MulAut N).ker at ha
    rwa [MulAut.conjNormal_ker_eq_centralizer] at ha
  let : IsElementaryAbelian 2 A := hA.2
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr : primeRank 2 (MulAut N) ≤ 4 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact automorphism_square_rank_le_four
  have hc := (primeRank_le_iff_elementary_card_le _).mp hr f.range he
  rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hc
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

variable [FiniteDimensional (ZMod 2) V]

/-- The original codimension budget forces actor stability of each marked tensor. -/
theorem marked_tensor_constituent_stable
    (ρ : Representation (ZMod 2) D V) (N A : Subgroup D) [N.Normal]
    (hA : IsElementaryTwo A) (hAC : A ⊓ centralizer (N : Set D) = ⊥)
    (hbudget : fixedCodim ρ A ≤ 2 * rank A)
    (U : Subrepresentation (ρ.comp N.subtype))
    (e : N ≃* Factor × Factor)
    (b : Representation.Equiv U.toRepresentation (baseRepresentation.comp e.toMonoidHom)) :
    ∀ a ∈ A, U.toSubmodule.map (ρ a) = U.toSubmodule := by
  have hi : U.toRepresentation.IsIrreducible :=
    (RepEquiv.irreducible_euqiv ⟨b.toLinearEquiv,b.isIntertwining'⟩).mpr
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective baseRepresentation).mpr
        baseRepresentation_irreducible)
  have hr := rank_le_four_of_faithful_on_tensor_base N A hA hAC e
  have hd : Module.finrank (ZMod 2) U.toSubmodule = 9 := by
    rw [b.toLinearEquiv.finrank_eq,Module.finrank_matrix]
    norm_num
  intro a ha
  apply map_constituent_eq_self_of_displacement_lt ρ N a U hi
  rw [←fixedCodim_zpowers_eq_displacement_rank]
  have hf := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ha))
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank ρ (zpowers a)
  omega

/-- Two tensor constituents already violate the original actor budget;
no invariance under that actor is an additional premise. -/
theorem no_disjoint_marked_tensor_constituents
    (ρ : Representation (ZMod 2) D V) (N A : Subgroup D) [N.Normal]
    (hA : IsElementaryTwo A) (hAC : A ⊓ centralizer (N : Set D) = ⊥)
    (hbudget : fixedCodim ρ A ≤ 2 * rank A)
    (U W : Subrepresentation (ρ.comp N.subtype))
    (hd : Disjoint U.toSubmodule W.toSubmodule)
    (eU eW : N ≃* Factor × Factor)
    (bU : Representation.Equiv U.toRepresentation (baseRepresentation.comp eU.toMonoidHom))
    (bW : Representation.Equiv W.toRepresentation (baseRepresentation.comp eW.toMonoidHom)) : False := by
  let J := A ⊔ N
  have hNJ : N ≤ J := le_sup_right
  have hAJ : A ≤ J := le_sup_left
  let lift (X : Subrepresentation (ρ.comp N.subtype))
      (hs : ∀ a ∈ A, X.toSubmodule.map (ρ a) = X.toSubmodule) :
      Subrepresentation (ρ.comp J.subtype) := {
    toSubmodule := X.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨a,ha,n,hn,hg⟩ := mem_sup_of_normal_right.mp g.property
      change ρ g.val v ∈ X.toSubmodule
      rw [←hg,map_mul,Module.End.mul_apply]
      rw [←hs a ha]
      exact ⟨ρ n v,X.apply_mem_toSubmodule ⟨n,hn⟩ hv,rfl⟩ }
  let U' := lift U (marked_tensor_constituent_stable ρ N A hA hAC hbudget U eU bU)
  let W' := lift W (marked_tensor_constituent_stable ρ N A hA hAC hbudget W eW bW)
  let c := subgroupOfEquivOfLe hNJ
  let bU' : Representation.Equiv (U'.toRepresentation.comp (N.subgroupOf J).subtype)
      (baseRepresentation.comp (c.trans eU).toMonoidHom) :=
    .mk bU.toLinearEquiv (fun g => bU.isIntertwining' (c g))
  let bW' : Representation.Equiv (W'.toRepresentation.comp (N.subgroupOf J).subtype)
      (baseRepresentation.comp (c.trans eW).toMonoidHom) :=
    .mk bW.toLinearEquiv (fun g => bW.isIntertwining' (c g))
  exact (not_lt_of_ge hbudget)
    (twice_rank_lt_fixedCodim_of_restricted_marked_tensors ρ N A hA hAC J hAJ hNJ
      U' W' hd (c.trans eU) (c.trans eW) bU' bW')

/-- The budget forces every tensor constituent to be invariant under the
entire ambient group: any distinct translate would be a second tensor. -/
theorem marked_tensor_constituent_invariant
    (ρ : Representation (ZMod 2) D V) (N A : Subgroup D) [N.Normal]
    (hA : IsElementaryTwo A) (hAC : A ⊓ centralizer (N : Set D) = ⊥)
    (hbudget : fixedCodim ρ A ≤ 2 * rank A)
    (U : Subrepresentation (ρ.comp N.subtype))
    (e : N ≃* Factor × Factor)
    (b : Representation.Equiv U.toRepresentation (baseRepresentation.comp e.toMonoidHom)) :
    ∀ g : D, U.toSubmodule.map (ρ g) = U.toSubmodule := by
  have hi : U.toRepresentation.IsIrreducible :=
    (RepEquiv.irreducible_euqiv ⟨b.toLinearEquiv,b.isIntertwining'⟩).mpr
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective baseRepresentation).mpr
        baseRepresentation_irreducible)
  intro g
  let c := conjugateSubrepresentationOrderIso ρ N g
  let W := c U
  have ha : IsAtom U := (Subrepresentation.irreducible_iff_isAtom U).mp hi
  by_contra hne
  have hWU : W ≠ U := by
    intro he
    apply hne
    simpa only [W,c,conjugateSubrepresentationOrderIso_toSubmodule] using
      congrArg Subrepresentation.toSubmodule he
  have hd : Disjoint U.toSubmodule W.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      (((c.isAtom_iff U).mpr ha).disjoint_of_ne ha hWU).symm.eq_bot
  let eg : N ≃* Factor × Factor := (MulAut.conjNormal g⁻¹).trans e
  let bg := (conjugateSubrepresentationEquiv ρ N U g⁻¹).trans
    (conjugateRepEquiv (RepEquiv.mk b.toLinearEquiv b.isIntertwining') g⁻¹)
  let bW : Representation.Equiv W.toRepresentation (baseRepresentation.comp eg.toMonoidHom) :=
    .mk bg.toLinearEquiv bg.isIntertwining'
  exact no_disjoint_marked_tensor_constituents ρ N A hA hAC hbudget U W hd e eg b bW
end BinaryTensorThree
