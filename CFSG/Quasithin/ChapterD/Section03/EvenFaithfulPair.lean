module
public import CFSG.Quasithin.ChapterD.Section03.EvenActorConstituent
public import CFSG.Quasithin.ChapterD.Section03.HermitianMultiplicity
public import Theory.Representation.SL2.NaturalDegreeBound
public import Theory.Representation.SL2.SmallSquare
public import Theory.Representation.BinaryOffender.SquarePreserving
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Models
public import CFSG.Quasithin.ChapterD.Section03.EvenNaturalTensor

/-!
# Faithful factor actors and the remaining even-linear square kernels

For a faithful irreducible pair with an SL₂(2ⁿ) factor, a starred actor faithful
on that factor's conjugation action has rank at most n. The exact constituent
classification gives a natural or Hermitian constituent. Natural multiplicity
bounds the whole binary dimension by 4n; the Hermitian multiplicity theorem
would make the factor irreducible, contradicting the commuting perfect factor.

The small-square theorem therefore gives whole-space natural-tensor coordinates.
Every exchanging actor gives the same coordinates by the Schur-field calculation.
The remaining preserving actor has nonzero kernels on both original factors;
these kernels are disjoint by irreducibility of the pair and binary Schur's lemma.
No quotient-faithfulness hypothesis is discarded in this alternative.

The original Chapter 10 Hall application is in CentralHall/Nonlinear/Modules/
SeedAnalysis/EvenDoubleKernel. Ambient natural-tensor exclusion and the case of
both nontrivial kernels still require proof.
Source: Aschbacher--Smith D.3.7, D.3.9 and D.3.21, printed pp.197--207;
refs/quasithin.pdf. The Chapter 10 use is 10.1.1 and10.2.3, pp.741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

omit [FiniteDimensional (ZMod 2) V] in
private theorem unmark
    {J K W : Type*} [Group J] [Group K]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) J V) (τ : Representation (ZMod 2) K W)
    (e : J ≃* K) (a : Representation.Equiv (σ.comp e.symm.toMonoidHom) τ) (j : J) (v : W) :
    a.toLinearEquiv.symm (τ (e j) v) = σ j (a.toLinearEquiv.symm v) := by
  have hh := LinearMap.congr_fun (a.symm.isIntertwining' (e j)) v
  change a.toLinearEquiv.symm (τ (e j) v) =
    σ (e.symm (e j)) (a.toLinearEquiv.symm v) at hh
  simpa only [e.symm_apply_apply] using hh

/-- Faithfulness on a factor bounds a small starred actor's entire pair module. -/
theorem even_pair_degree_le_of_faithful_starred_actor
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L K : Subgroup G) [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    [Group.IsPerfect K] [Nontrivial K]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (e : L ≃* SL(2,F)) (n : ℕ) (hn : 3 ≤ n) (hF : Nat.card F = 2^n)
    (hi : IsIrreducible (ρ.comp (L ⊔ K).subtype))
    (hc : K ≤ centralizer (L : Set G))
    (A : Subgroup G) (hA : A ∈ QhatStar ρ) (hsmall : cubicRatio ρ ≤ 2)
    (hfaith : Function.Injective ((MulAut.conjNormal : G →* MulAut L).comp A.subtype)) :
    Module.finrank (ZMod 2) V ≤ 4*n := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : ρ.IsIrreducible := irreducible_of_subgroup_restriction ρ (L ⊔ K) hi
  let α : G →* MulAut SL(2,F) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hα (g : G) (l : L) : e (MulAut.conjNormal g l) = α g (e l) := by
    change _ = e (MulAut.conjNormal g (e.symm (e l)))
    rw [e.symm_apply_apply]
  have hfα : Function.Injective (α.comp A.subtype) := (MulAut.congr e).injective.comp hfaith
  have hmove : ¬ A ≤ centralizer (L : Set G) := by
    intro hh
    apply hA.1.2.1.1
    apply bot_unique
    intro a ha
    have he : (MulAut.conjNormal a : MulAut L) = 1 := by
      apply DFunLike.ext
      intro l
      apply Subtype.ext
      change a * (l : G) * a⁻¹ = (l : G)
      rw [← hh ha l l.property,mul_assoc,mul_inv_cancel,mul_one]
    exact congrArg (fun b : A => (b : G)) (hfaith (show
      (MulAut.conjNormal : G →* MulAut L).comp A.subtype ⟨a,ha⟩ =
      (MulAut.conjNormal : G →* MulAut L).comp A.subtype 1 from he.trans (map_one _).symm))
  have hrank : rank A ≤ n := by
    let : IsElementaryAbelian 2 A := hA.1.2.1.2
    have hr : rank A ≤ primeRank 2 A := by
      have hh := (primeRank_le_iff_elementary_card_le (p := 2) A).mp le_rfl ⊤
        (IsElementaryAbelian.of_injective (p := 2) (⊤ : Subgroup A).subtype Subtype.val_injective)
      rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv,
        hA.1.2.1.card_eq_two_pow_rank] at hh
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
    exact hr.trans ((Theory.GroupTheory.primeRank_le_of_injective 2 _ hfα).trans
      (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le (by omega) hF))
  obtain ⟨U,hU,_⟩ := exists_faithful_normal_simple_constituent ρ hf inferInstance L
  obtain ⟨_,hm⟩ := even_constituent_of_bounded_starred_actor ρ hf inferInstance L hL e n
    (by omega) hF A hA hsmall hrank hmove U hU
  have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hsmall)
  rcases hm with hm | ⟨s,hs,hpos,hm⟩
  · obtain ⟨a⟩ := hm
    let E : (Fin 2 → F) ≃ₗ[ZMod 2] U.toSubmodule := a.toLinearEquiv.symm
    have hE (l : L) v : E ((e l).val.mulVec v) = U.toRepresentation l (E v) :=
      unmark U.toRepresentation SL2.BinarySmall.natural e a l v
    have hd := SL2AutomorphismNatural.degree_le_two_of_faithful_actor ρ L e.toMonoidHom
      e.surjective α hα U hU E hE (by rw [hF]; exact (show 2^1 < 2^n from (Nat.pow_lt_pow_iff_right (by decide)).mpr (by omega)))
      A hA.1.2.1 hfα hb
    have he : Module.finrank (ZMod 2) (Fin 2 → F) = 2*n :=
      NaturalTensor.finrank_natural F hF
    simpa only [he,show 2*(2*n)=4*n by omega] using hd
  · let : NeZero s := ⟨hpos.ne'⟩
    obtain ⟨b,⟨a⟩⟩ := hm
    let e' := e.trans (Atlas.fieldEquivSL 2 b)
    let α' : G →* MulAut SL(2,OrthogonalFourMinus.FiniteModel.Field s) :=
      (MulAut.congr e').toMonoidHom.comp MulAut.conjNormal
    have hα' (g : G) (l : L) : e' (MulAut.conjNormal g l) = α' g (e' l) := by
      change _ = e' (MulAut.conjNormal g (e'.symm (e' l)))
      rw [e'.symm_apply_apply]
    have hfα' : Function.Injective (α'.comp A.subtype) :=
      (MulAut.congr e').injective.comp hfaith
    let E : OrthogonalFourMinus.FiniteModel.Space s ≃ₗ[ZMod 2] U.toSubmodule :=
      a.toLinearEquiv.symm
    have hE (l : L) v : E (SL2.BinarySmall.hermitian s (e' l) v) =
        U.toRepresentation l (E v) :=
      unmark U.toRepresentation ((SL2.BinarySmall.hermitian s).comp
        (Matrix.SpecialLinearGroup.map b.toRingHom)) e a l v
    let : IsQuasisimple SL(2,OrthogonalFourMinus.FiniteModel.Field s) :=
      IsQuasisimple.of_mulEquiv e'
    have hirr := hermitian_irreducible_of_faithful_actor s (hL.knownSimple_of_equiv e')
      (by omega) ρ L e'.toMonoidHom e'.surjective α' hα' U hU E hE A hA.1.2.1 hfα' hb
    exact (not_irreducible_of_faithful_commuting_perfect ρ hf L K hc hirr).elim

open Representation.QuadraticFourGroup.TensorClassification

/-- The two actual component kernels inside the same preserving starred actor. -/
@[expose] def EvenSquareDoubleKernel
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V) : Prop :=
  ∃ A : Subgroup (SquarePreserving.group σ), A ∈ QhatStar (SquarePreserving.action σ) ∧
    A ⊓ centralizer (SquarePreserving.left σ : Set _) ≠ ⊥ ∧
    A ⊓ centralizer (SquarePreserving.right σ : Set _) ≠ ⊥ ∧
    Disjoint (A ⊓ centralizer (SquarePreserving.left σ : Set _))
      (A ⊓ centralizer (SquarePreserving.right σ : Set _))

private theorem kernel_nonzero {X : Type*} [Group X] (J A : Subgroup X) [J.Normal]
    (h : ¬ Function.Injective ((MulAut.conjNormal : X →* MulAut J).comp A.subtype)) :
    A ⊓ centralizer (J : Set X) ≠ ⊥ := by
  intro hz
  apply h
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  apply mem_bot.mp
  rw [←hz]
  refine ⟨a.property,?_⟩
  intro j hj
  have he := congrArg (fun f : MulAut J => (f ⟨j,hj⟩ : X)) ha
  change (a : X) * j * (a : X)⁻¹ = j at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A small square has its whole natural-tensor coordinates, or the preserving
starred actor has nonzero, disjoint kernels on both original factors. -/
theorem even_square_natural_or_double_kernel
    [IsSimpleGroup SL(2,F)] [IsQuasisimple SL(2,F)]
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,F))
    (n : ℕ) (hn : 3 ≤ n) (hF : Nat.card F=2^n)
    (hsmall : cubicRatio (normalizerRepresentation σ) ≤ 2) :
    (∃ α : MulAut SL(2,F), Nonempty (σ.Equiv (restrictScalars (k := ZMod 2)
      (externalTensor ((SL2.BinarySmall.embeddedNatural (RingHom.id F)).comp α.symm.toMonoidHom)
        (SL2.BinarySmall.embeddedNatural (RingHom.id F)))))) ∨ EvenSquareDoubleKernel σ := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let := hi
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation σ) 2).mp hsmall
  by_cases hpres : ∀ a ∈ A, a.val ∈ SquarePreserving.group σ
  · have hb := SquarePreserving.cubic_le_of_preserving_actor σ A hA hc hd
      (fun a ha => (hpres a ha).1) (fun a ha => (hpres a ha).2)
    let ρ := SquarePreserving.action σ
    let L := SquarePreserving.left σ
    let K := SquarePreserving.right σ
    let eL := SquarePreserving.leftEquiv σ hf
    let eK := SquarePreserving.rightEquiv σ hf
    let : IsSimpleGroup L := eL.symm.isSimpleGroup
    let : IsSimpleGroup K := eK.symm.isSimpleGroup
    let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL
    let : IsQuasisimple K := IsQuasisimple.of_mulEquiv eK
    let : Nontrivial L := eL.symm.surjective.nontrivial
    let : Nontrivial K := eK.symm.surjective.nontrivial
    have hirr := SquarePreserving.pair_irreducible σ hi hf
    have hcomm := SquarePreserving.right_centralizes_left σ
    have hρ := SquarePreserving.action_faithful σ
    obtain ⟨B,hB⟩ := (QhatStar_nonempty_iff ρ).mpr hb
    by_cases hfL : Function.Injective ((MulAut.conjNormal : SquarePreserving.group σ →* MulAut L).comp B.subtype)
    · have hdim := even_pair_degree_le_of_faithful_starred_actor ρ hρ L K
        (hS.knownSimple_of_equiv eL) eL.symm n hn hF hirr hcomm B hB hb hfL
      exact Or.inl (SL2.SmallSquare.small_square_natural_tensor σ hf n hn hF (by omega))
    by_cases hfK : Function.Injective ((MulAut.conjNormal : SquarePreserving.group σ →* MulAut K).comp B.subtype)
    · have hdim := even_pair_degree_le_of_faithful_starred_actor ρ hρ K L
        (hS.knownSimple_of_equiv eK) eK.symm n hn hF (by rwa [sup_comm])
        (le_centralizer_iff.mp hcomm) B hB hb hfK
      exact Or.inl (SL2.SmallSquare.small_square_natural_tensor σ hf n hn hF (by omega))
    refine Or.inr ⟨B,hB,kernel_nonzero L B hfL,kernel_nonzero K B hfK,?_⟩
    apply disjoint_def.mpr
    intro b hbL hbK
    let : IsElementaryAbelian 2 B := hB.1.2.1.2
    let : IsIrreducible (ρ.comp (L ⊔ K).subtype) := hirr
    exact BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ (L ⊔ K) hρ
      (elemPow_eq_one_of_isElementaryAbelian b hbL.1)
      (by
        have hl : L ≤ centralizer ({b} : Set (SquarePreserving.group σ)) :=
          fun l hl => by intro z hz; simpa only [Set.mem_singleton_iff.mp hz] using (hbL.2 l hl).symm
        have hk : K ≤ centralizer ({b} : Set (SquarePreserving.group σ)) :=
          fun k hk => by intro z hz; simpa only [Set.mem_singleton_iff.mp hz] using (hbK.2 k hk).symm
        intro g hg
        exact (sup_le hl hk hg b rfl).symm)
  · push Not at hpres
    obtain ⟨a,ha,hnorm⟩ := hpres
    let : IsElementaryAbelian 2 A := hA.2
    have h2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
    obtain ⟨α,hα⟩ := (SquarePreserving.involution_preserves_or_exchanges σ
      center_eq_bot_of_simple_perfect hf a h2).resolve_left hnorm
    have hr := SquarePreserving.twisted_exchange_rank_le σ
      center_eq_bot_of_simple_perfect hi hf A a ha α hα
    have hrank : rank A ≤ n+1 := hr.trans (Nat.add_le_add_right
      (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le (by omega) hF) 1)
    have hdisp := NaturalTensor.operatorFixedCodim_le_fixedCodim
      (normalizerRepresentation σ) A ha
    change Module.finrank (ZMod 2) (a.val.val-1).range ≤ _ at hdisp
    by_cases hlin : SchurNormalizer.IsSchurLinear σ a
    · exact Or.inl ⟨α,SL2.EvenSquare.twisted_schur_linear_exchange_natural
        σ hf n hn hF a h2 hlin α hα (hdisp.trans (hd.trans (by omega)))⟩
    · have hb := SchurNormalizer.finrank_le_twice_fixedCodim σ a hlin
      rw [fixedCodim_zpowers_eq_displacement_rank] at hb
      change Module.finrank (ZMod 2) V ≤ 2*Module.finrank (ZMod 2) (a.val.val-1).range at hb
      exact Or.inl (SL2.SmallSquare.small_square_natural_tensor σ hf n hn hF (by omega))
end CFSG.Quasithin.ChapterD
