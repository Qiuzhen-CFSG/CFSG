module
public import CFSG.Quasithin.ChapterD.Section03.EvenHermitianMultiplicity
public import Theory.Representation.BinaryOffender.Homogeneous.MarkedMultiplicityCost

/-!
# Excluding the genuine two-kernel Hermitian square

The Hermitian multiplicity construction forces binary dimension at least 8n.
Each factor type has dimension 2n, so invariant-section selection gives four
copies for the same full actor. Each copy costs at least the rank of that
factor's conjugation image; a Hermitian copy costs strictly more. The two
images jointly detect the full actor, even though both kernels are nonzero.
Their combined bounds contradict the full actor's two-rank budget.

If both selected types are natural instead, their genuine cubic fixed-point
freeness identifies the whole seed with dimension 4n, also a contradiction.
Thus no Hermitian multiplicity alternative survives. The original Chapter 10
application retains its exact orbit quotient and both component restrictions.
Source: Aschbacher--Smith D.3.7, printed pp.198--199, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.ChapterD
variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

omit [Finite V] in
private theorem unmark_cost
    {J K W : Type*} [Group J] [Group K]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) J V) (τ : Representation (ZMod 2) K W)
    (e : J ≃* K) (a : Representation.Equiv (σ.comp e.symm.toMonoidHom) τ) (j : J) (v : W) :
    a.toLinearEquiv.symm (τ (e j) v) = σ j (a.toLinearEquiv.symm v) := by
  have hh := LinearMap.congr_fun (a.symm.isIntertwining' (e j)) v
  change a.toLinearEquiv.symm (τ (e j) v) =
    σ (e.symm (e j)) (a.toLinearEquiv.symm v) at hh
  simpa only [e.symm_apply_apply] using hh

set_option backward.isDefEq.respectTransparency false in
/-- Four copies cost four times the factor-image rank, strictly more for a Hermitian type. -/
theorem even_factor_four_copy_cost
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L) (e : L ≃* SL(2,F))
    (n : ℕ) (hn : 3 ≤ n) (hF : Nat.card F=2^n)
    (I : Subrepresentation (ρ.comp L.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (hdI : Module.finrank (ZMod 2) I.toSubmodule=2*n)
    (hmodel : SL2.BinarySmall.IsNatural (I.toRepresentation.comp e.symm.toMonoidHom) ∨
      ∃ s : ℕ, n=2*s ∧ ∃ hs : 0<s, letI : NeZero s := ⟨hs.ne'⟩;
        SL2.BinarySmall.IsHermitian (I.toRepresentation.comp e.symm.toMonoidHom) s)
    (hd : 8*n ≤ Module.finrank (ZMod 2) V)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hpos : 0 < rank (A.map (MulAut.conjNormal : G →* MulAut L))) :
    4 * rank (A.map (MulAut.conjNormal : G →* MulAut L)) ≤ fixedCodim ρ A ∧
      (SL2.BinarySmall.IsNatural (I.toRepresentation.comp e.symm.toMonoidHom) ∨
        4 * (rank (A.map (MulAut.conjNormal : G →* MulAut L))+1) ≤ fixedCodim ρ A) := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let : IsSemisimpleModule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple ρ inferInstance L
  have hd' : 4 * Module.finrank (ZMod 2) I.toSubmodule ≤ Module.finrank (ZMod 2) V := by omega
  rcases hmodel with hm | ⟨s,hs,hposS,hm⟩
  · obtain ⟨a⟩ := hm
    let α : G →* MulAut SL(2,F) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
    have hα (g : G) (l : L) : e (MulAut.conjNormal g l) = α g (e l) := by
      change _ = e (MulAut.conjNormal g (e.symm (e l)))
      rw [e.symm_apply_apply]
    let E := a.toLinearEquiv.symm
    have hE (l : L) v : E ((e l).val.mulVec v) = I.toRepresentation l (E v) :=
      unmark_cost I.toRepresentation SL2.BinarySmall.natural e a l v
    have ht : (normalTypeAction ρ L).inertia I = ⊤ := by
      apply top_unique
      intro g _
      exact SL2AutomorphismNatural.natural_sameModule_conjugate ρ L e.toMonoidHom α hα I E hE g
    have htype := restriction_isotypic_of_typeInertia_top ρ L I hI ht
    let bI : Representation.Equiv I.toRepresentation (SL2NaturalOffenders.NoStrong.natural.comp e.toMonoidHom) := {
      __ := E.symm
      isIntertwining' l := by
        apply LinearMap.ext
        intro v
        change E.symm (I.toRepresentation l v) = (e l).val.mulVec (E.symm v)
        apply E.injective
        rw [E.apply_symm_apply,hE,E.apply_symm_apply] }
    have hFn : 2 < Nat.card F := by
      rw [hF]
      exact (show 2^1 < 2^n from (Nat.pow_lt_pow_iff_right (by decide)).mpr (by omega))
    have hstrong : ¬ IsStrongFFModule (normalizerRepresentation
        (SL2NaturalOffenders.NoStrong.natural (F := F))) :=
      SL2NaturalOffenders.normalizer_not_strong (F := F) hFn
    have hh := (marked_isotypic_multiplicity_cost ρ L (SL2NaturalOffenders.NoStrong.natural (F := F))
      (SL2NaturalOffenders.natural_injective (F := F)) e.toMonoidHom e.surjective α hα I hI bI htype A hA
      4 hd' hstrong).1
    have hr : rank (A.map α) = rank (A.map (MulAut.conjNormal : G →* MulAut L)) := by
      rw [show α = (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal from rfl,
        ←Subgroup.map_map,rank_map_injective _ (MulAut.congr e).injective]
    rw [hr] at hh
    exact ⟨hh,Or.inl ⟨a⟩⟩
  · let : NeZero s := ⟨hposS.ne'⟩
    obtain ⟨b,⟨a⟩⟩ := hm
    let e' := e.trans (Atlas.fieldEquivSL 2 b)
    let α : G →* MulAut SL(2,OrthogonalFourMinus.FiniteModel.Field s) :=
      (MulAut.congr e').toMonoidHom.comp MulAut.conjNormal
    have hα (g : G) (l : L) : e' (MulAut.conjNormal g l) = α g (e' l) := by
      change _ = e' (MulAut.conjNormal g (e'.symm (e' l)))
      rw [e'.symm_apply_apply]
    let E := a.toLinearEquiv.symm
    have hE (l : L) v : E (SL2.BinarySmall.hermitian s (e' l) v) = I.toRepresentation l (E v) :=
      unmark_cost I.toRepresentation ((SL2.BinarySmall.hermitian s).comp
        (Matrix.SpecialLinearGroup.map b.toRingHom)) e a l v
    have ht : (normalTypeAction ρ L).inertia I = ⊤ := by
      apply top_unique
      intro g _
      exact SL2Hermitian.sameModule_conjugate s ρ L e'.toMonoidHom α hα I E hE g
    have htype := restriction_isotypic_of_typeInertia_top ρ L I hI ht
    let bI : Representation.Equiv I.toRepresentation ((SL2.BinarySmall.hermitian s).comp e'.toMonoidHom) := {
      __ := E.symm
      isIntertwining' l := by
        apply LinearMap.ext
        intro v
        change E.symm (I.toRepresentation l v) = SL2.BinarySmall.hermitian s (e' l) (E.symm v)
        apply E.injective
        rw [E.apply_symm_apply,hE,E.apply_symm_apply] }
    let : IsQuasisimple SL(2,OrthogonalFourMinus.FiniteModel.Field s) := IsQuasisimple.of_mulEquiv e'
    have hff := hermitian_normalizer_not_ff s (hL.knownSimple_of_equiv e') (by omega)
    have hstrong : ¬ IsStrongFFModule (normalizerRepresentation (SL2.BinarySmall.hermitian s)) := by
      rintro ⟨P,hP,hlt⟩
      exact hff ⟨P,hP,hlt.le⟩
    have hh := marked_isotypic_multiplicity_cost ρ L (SL2.BinarySmall.hermitian s)
      (OrthogonalFourMinus.RankOne.hermitian_injective s) e'.toMonoidHom e'.surjective
      α hα I hI bI htype A hA 4 hd' hstrong
    have hr : rank (A.map α) = rank (A.map (MulAut.conjNormal : G →* MulAut L)) := by
      rw [show α = (MulAut.congr e').toMonoidHom.comp MulAut.conjNormal from rfl,
        ←Subgroup.map_map,rank_map_injective _ (MulAut.congr e').injective]
    rw [hr] at hh
    exact ⟨hh.1,Or.inr (hh.2 hpos hff)⟩
end CFSG.Quasithin.ChapterD

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {n : ℕ}

/-- Both actual factor-image costs exclude every genuine Hermitian two-kernel square. -/
theorem not_even_square_hermitian_multiplicity
    [IsSimpleGroup SL(2,GaloisField 2 n)] [IsQuasisimple SL(2,GaloisField 2 n)]
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,GaloisField 2 n)) :
    ¬ EvenSquareHermitianMultiplicity σ := by
  intro hm
  obtain ⟨s,hs,hposS,_⟩ := hm.2.2.1
  have hn : 3 ≤ n := by omega
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
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
  let : IsIrreducible (ρ.comp (L ⊔ K).subtype) := SquarePreserving.pair_irreducible σ hi hf
  let : ρ.IsIrreducible := irreducible_of_subgroup_restriction ρ (L ⊔ K) inferInstance
  have hcomm := SquarePreserving.right_centralizes_left σ
  have hρ := SquarePreserving.action_faithful σ
  obtain ⟨A,hA,hL,hK,hdis⟩ := hm.1.1
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hmL : ¬ A ≤ centralizer (L : Set (SquarePreserving.group σ)) := by
    intro hh
    apply hK
    apply bot_unique
    intro a ha
    exact disjoint_def.mp hdis ⟨ha.1,hh ha.1⟩ ha
  have hmK : ¬ A ≤ centralizer (K : Set (SquarePreserving.group σ)) := by
    intro hh
    apply hL
    apply bot_unique
    intro a ha
    exact disjoint_def.mp hdis ha ⟨ha.1,hh ha.1⟩
  have hpos (J : Subgroup (SquarePreserving.group σ)) [J.Normal]
      (hj : ¬ A ≤ centralizer (J : Set (SquarePreserving.group σ))) :
      0 < rank (A.map (MulAut.conjNormal : SquarePreserving.group σ →* MulAut J)) := by
    let α : SquarePreserving.group σ →* MulAut J := MulAut.conjNormal
    let : IsElementaryAbelian 2 (A.map α) := IsElementaryAbelian.map _
    apply IsElementaryTwo.rank_pos (show IsElementaryTwo (A.map α) from ⟨?_,inferInstance⟩)
    intro hz
    have hh : A ≤ α.ker := by
      intro a ha
      exact mem_bot.mp (hz ▸ mem_map_of_mem α ha)
    rw [MulAut.conjNormal_ker_eq_centralizer] at hh
    exact hj hh
  have hposL := hpos L hmL
  have hposK := hpos K hmK
  have hr := rank_le_sum_image_ranks A
    (MulAut.conjNormal : SquarePreserving.group σ →* MulAut L)
    (MulAut.conjNormal : SquarePreserving.group σ →* MulAut K)
    (BinaryIrreducibleCentralizer.pair_elementary_conjugation_injective ρ L K hρ A)
  obtain ⟨I,hI,_,_,_,_,_,hdI,hmodI⟩ := even_pair_moved_constituent
    ρ hρ L K (hS.knownSimple_of_equiv eL) eL.symm n (by omega)
    (GaloisField.card 2 n (by omega)) inferInstance hcomm A hA hmL
  obtain ⟨J,hJ,_,_,_,_,_,hdJ,hmodJ⟩ := even_pair_moved_constituent
    ρ hρ K L (hS.knownSimple_of_equiv eK) eK.symm n (by omega)
    (GaloisField.card 2 n (by omega)) (by rwa [sup_comm])
    (le_centralizer_iff.mp hcomm) A hA hmK
  obtain ⟨hcostL,haltL⟩ := even_factor_four_copy_cost ρ L (hS.knownSimple_of_equiv eL)
    eL.symm n hn (GaloisField.card 2 n (by omega)) I hI hdI hmodI hm.2.1 A hA.1.2.1 hposL
  obtain ⟨hcostK,haltK⟩ := even_factor_four_copy_cost ρ K (hS.knownSimple_of_equiv eK)
    eK.symm n hn (GaloisField.card 2 n (by omega)) J hJ hdJ hmodJ hm.2.1 A hA.1.2.1 hposK
  have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  rcases haltL with hnatI | hstrict
  · rcases haltK with hnatJ | hstrict
    · let I' := I.compActors eL.toMonoidHom
      let J' := J.compActors eK.toMonoidHom
      have hiI : I'.toRepresentation.IsIrreducible :=
        (irreducible_comp_surjective_iff eL.toMonoidHom eL.surjective I.toRepresentation).mpr hI
      have hiJ : J'.toRepresentation.IsIrreducible :=
        (irreducible_comp_surjective_iff eK.toMonoidHom eK.surjective J.toRepresentation).mpr hJ
      let := hi
      have hd := SL2.PairNatural.degree_of_natural_constituents σ (by omega)
        ⟨I',hiI,hnatI⟩ ⟨J',hiJ,hnatJ⟩
      have hd' := hm.2.1
      omega
    · omega
  · omega
end CFSG.Quasithin.ChapterD
