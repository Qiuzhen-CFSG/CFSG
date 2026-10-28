module
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.Representation.GeneralLinearNatural

/-!
# Quadratic actors on paired binary SL3 central covers

On a commutator-generated four-dimensional SL3(2) module every involution
has displacement equal to its fixed plane. If an elementary group acts
quadratically, its moved space maps into the involution displacement line
of any natural quotient. For paired natural and dual quotients, the two
line bounds and the displacement-map count force actor rank at most one.

Two embedded four-dimensional covers with intersection of dimension at
most one have involution displacement of dimension at least three. They
therefore cannot occur in a module of quadratic ratio at most two. The
intersection need not vanish: the two covering lines may coincide.

The original-action application is ComponentSupports/Modules/Recognition/
LinearThreeFullAction in Chapter14. It retains the component action on
the full orbit and the literal central quotient of U.
Source: Aschbacher--Smith B.4.8(2), F.9.18(2),14.6.22,
printed pp.91,325,1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  [FiniteDimensional (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
  (σ : Representation (ZMod 2) BinaryLinearThree.Group X)
  (τ : Representation (ZMod 2) BinaryLinearThree.Group Y)

/-- The quotient of a quadratic four-space has moved space inside each involution range. -/
theorem quadratic_cover_moved_le_involution_range
    (p : σ.IntertwiningMap τ) (hp : Function.Surjective p)
    (hd : Module.finrank (ZMod 2) X = 4) (hm : Coinvariants.ker σ = ⊤)
    {A : Subgroup BinaryLinearThree.Group} (hq : IsQuadratic σ A)
    (a : BinaryLinearThree.Group) (ha : a ∈ A) (ho : orderOf a = 2) :
    subspaceCommutator τ ⊤ A ≤ LinearMap.range (τ a - LinearMap.id) := by
  have hr := (NaturalExtension.involution_range_eq_fixed σ hd a ho
    (NaturalExtension.involution_codim_of_commutator_top σ hd hm a ho)).1
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,y,_,rfl⟩
  obtain ⟨x,rfl⟩ := hp y
  have hf : σ b x - x ∈ fixedSpace σ (zpowers a) :=
    (mem_fixedSpace_zpowers_iff σ a _).mpr (hq a ha b hb x)
  rw [←hr] at hf
  obtain ⟨z,hz⟩ := hf
  refine ⟨p z,?_⟩
  have he := congrArg p hz
  change p (σ a z-z) = p (σ b x-x) at he
  simpa only [map_sub,p.isIntertwining,LinearMap.sub_apply,LinearMap.id_apply] using he

/-- Quadraticity on a natural four-dimensional cover bounds dual fixed codimension by one. -/
theorem quadratic_natural_cover_dual_codim_le_one
    (p : σ.IntertwiningMap W) (hp : Function.Surjective p)
    (hd : Module.finrank (ZMod 2) X = 4) (hm : Coinvariants.ker σ = ⊤)
    {A : Subgroup BinaryLinearThree.Group} (hA : IsElementaryTwo A)
    (hq : IsQuadratic σ A) : fixedCodim W.dual A ≤ 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a,ha,hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hl := Submodule.finrank_mono
    (quadratic_cover_moved_le_involution_range σ W p hp hd hm hq a ha ho)
  rw [←fixedCodim_zpowers_eq_displacement_rank] at hl
  have hu := (involution_actor_rank_and_fixedCodim W a ho).2.2.2
  have hw : Module.finrank (ZMod 2) Vector = 3 := Module.finrank_fin_fun _
  rw [hw] at hu
  rw [fixedCodim_dual_eq_moved_finrank]
  omega

/-- Quadraticity on a dual-natural four-dimensional cover bounds natural fixed codimension by one. -/
theorem quadratic_dual_cover_codim_le_one
    (p : σ.IntertwiningMap W.dual) (hp : Function.Surjective p)
    (hd : Module.finrank (ZMod 2) X = 4) (hm : Coinvariants.ker σ = ⊤)
    {A : Subgroup BinaryLinearThree.Group} (hA : IsElementaryTwo A)
    (hq : IsQuadratic σ A) : fixedCodim W A ≤ 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a,ha,hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hl := Submodule.finrank_mono
    (quadratic_cover_moved_le_involution_range σ W.dual p hp hd hm hq a ha ho)
  rw [←fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_dual] at hl
  have hu := (involution_actor_rank_and_fixedCodim W a ho).2.2.2
  have hw : Module.finrank (ZMod 2) Vector = 3 := Module.finrank_fin_fun _
  rw [hw] at hu
  have he : fixedCodim W A = Module.finrank (ZMod 2) (subspaceCommutator W.dual ⊤ A) := by
    rw [subspaceCommutator_top_eq_coinvariants]
    change fixedCodim W A = Module.finrank (ZMod 2) (Coinvariants.ker (Representation.dual (W.comp A.subtype)))
    rw [←dualAnnihilator_invariants (W.comp A.subtype)]
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (Representation.invariants (W.comp A.subtype))
    have h' := fixedCodim_add_finrank W A
    change Module.finrank (ZMod 2) (fixedSpace W A) +
      Module.finrank (ZMod 2) (Representation.invariants (W.comp A.subtype)).dualAnnihilator =
      Module.finrank (ZMod 2) Vector at h
    omega
  rw [he]
  omega

variable [FiniteDimensional (ZMod 2) Y]
/-- An elementary group quadratic on both four-dimensional covers has rank at most one. -/
theorem quadratic_paired_covers_rank_le_one
    (p : σ.IntertwiningMap W) (hp : IsCover p)
    (q : τ.IntertwiningMap W.dual) (hq : IsCover q)
    (hdX : Module.finrank (ZMod 2) X = 4)
    (hdY : Module.finrank (ZMod 2) Y = 4)
    {A : Subgroup BinaryLinearThree.Group} (hA : IsElementaryTwo A)
    (hσ : IsQuadratic σ A) (hτ : IsQuadratic τ A) : rank A ≤ 1 := by
  have h1 := quadratic_natural_cover_dual_codim_le_one σ p hp.1 hdX hp.2.2 hA hσ
  have h2 := quadratic_dual_cover_codim_le_one τ q hq.1 hdY hq.2.2 hA hτ
  exact (rank_le_fixedCodim_mul_dual W (specialLinearNatural_injective 3) A).trans
    ((Nat.mul_le_mul h2 h1).trans_eq (by decide))

section Embedded
variable (U V : Subrepresentation σ)

/-- Two four-space displacements yield dimension at least three even with a shared central line. -/
theorem paired_involution_codim_ge_three
    (hU : Module.finrank (ZMod 2) U.toSubmodule = 4)
    (hV : Module.finrank (ZMod 2) V.toSubmodule = 4)
    (hmU : Coinvariants.ker U.toRepresentation = ⊤)
    (hmV : Coinvariants.ker V.toRepresentation = ⊤)
    (hi : Module.finrank (ZMod 2) ↥(U.toSubmodule ⊓ V.toSubmodule) ≤ 1)
    (a : BinaryLinearThree.Group) (ha : orderOf a = 2) :
    3 ≤ fixedCodim σ (zpowers a) := by
  let R := LinearMap.range (σ a - LinearMap.id)
  let RU := (LinearMap.range (U.toRepresentation a - LinearMap.id)).map U.toSubmodule.subtype
  let RV := (LinearMap.range (V.toRepresentation a - LinearMap.id)).map V.toSubmodule.subtype
  have hu : Module.finrank (ZMod 2) RU = 2 := by
    rw [←(Submodule.equivMapOfInjective U.toSubmodule.subtype Subtype.val_injective
      (LinearMap.range (U.toRepresentation a - LinearMap.id))).finrank_eq]
    rw [←fixedCodim_zpowers_eq_displacement_rank]
    exact NaturalExtension.involution_codim_of_commutator_top U.toRepresentation hU hmU a ha
  have hv : Module.finrank (ZMod 2) RV = 2 := by
    rw [←(Submodule.equivMapOfInjective V.toSubmodule.subtype Subtype.val_injective
      (LinearMap.range (V.toRepresentation a - LinearMap.id))).finrank_eq]
    rw [←fixedCodim_zpowers_eq_displacement_rank]
    exact NaturalExtension.involution_codim_of_commutator_top V.toRepresentation hV hmV a ha
  have hRU : RU ≤ U.toSubmodule := by rintro _ ⟨v,_,rfl⟩; exact v.property
  have hRV : RV ≤ V.toSubmodule := by rintro _ ⟨v,_,rfl⟩; exact v.property
  have hUR : RU ≤ R := by
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨v.val,rfl⟩
  have hVR : RV ≤ R := by
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨v.val,rfl⟩
  have hsum := RU.finrank_sup_add_finrank_inf_eq RV
  have hinf := (Submodule.finrank_mono (inf_le_inf hRU hRV)).trans hi
  have hr := Submodule.finrank_mono (sup_le hUR hVR)
  rw [fixedCodim_zpowers_eq_displacement_rank]
  change 3 ≤ Module.finrank (ZMod 2) R
  omega

/-- A small quadratic ratio excludes an embedded pair of natural and dual four-dimensional covers. -/
theorem not_small_quadraticRatio_of_paired_covers
    (p : U.toRepresentation.IntertwiningMap W) (hp : IsCover p)
    (q : V.toRepresentation.IntertwiningMap W.dual) (hq : IsCover q)
    (hU : Module.finrank (ZMod 2) U.toSubmodule = 4)
    (hV : Module.finrank (ZMod 2) V.toSubmodule = 4)
    (hi : Module.finrank (ZMod 2) ↥(U.toSubmodule ⊓ V.toSubmodule) ≤ 1) :
    ¬ quadraticRatio σ ≤ 2 := by
  intro hsmall
  obtain ⟨A,hA,hquad,hbound⟩ := (quadraticRatio_le_two_iff σ).mp hsmall
  have hqu : IsQuadratic U.toRepresentation A := by
    intro a ha b hb v
    apply Subtype.ext
    exact hquad a ha b hb v
  have hqv : IsQuadratic V.toRepresentation A := by
    intro a ha b hb v
    apply Subtype.ext
    exact hquad a ha b hb v
  have hr := quadratic_paired_covers_rank_le_one U.toRepresentation V.toRepresentation
    p hp q hq hU hV hA hqu hqv
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a,ha,hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hlo := paired_involution_codim_ge_three σ U V hU hV hp.2.2 hq.2.2 hi a ho
  have hle := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr ha))
  have h1 := fixedCodim_add_finrank σ A
  have h2 := fixedCodim_add_finrank σ (zpowers a)
  omega
end Embedded
end Representation.OneCohomology.SLThreeCentralExtension
