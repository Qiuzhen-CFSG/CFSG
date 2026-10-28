module
public import Theory.Representation.Suzuki.NaturalSupportMultiplicity
public import Theory.Representation.SL3OddNaturalNormalizer.ActorCost
public import Theory.Representation.BinaryParabolicNatural.RepeatedOffender
public import CFSG.Quasithin.ChapterD.Section03.SuzukiStrongSupport

/-!
# At most four natural-field multiplicities in Suzuki support

Take the literal orbit of the natural support constituent under the commuting
Suzuki component. Its faithful scalar action uses the original natural field.
The coordinates preserve the entire support joined with the starred actor,
so fixed codimension multiplies by the number of copies. The pointwise actor
kernel is unchanged on the orbit. Its inherited ratio-two budget, together
with the natural constituent's rank-to-cost bound, permits at most four copies.

The original Chapter 10 application constructs the constituent, discharges
movement, and contradicts the coprime-field Suzuki degree bound.
Source: Aschbacher--Smith D.2.7,D.3.9 and10.1.1--2,10.2.3,
printed pp.180,200--201,741--742,745; refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The same full starred actor forces a faithful Suzuki action on at most four multiplicities. -/
theorem suzuki_natural_support_small_faithful_action
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (eK : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [J.Normal]
    (hA : A ∈ QhatStar ρ) (hKJ : K ≤ centralizer (J : Set G))
    (hKA : K ≤ centralizer (A : Set G))
    (F : BinaryField) (ho : Odd F.degree)
    (R : Submodule (ZMod 2) V) (hJR : J ≤ subspaceStabilizer ρ R)
    (hAR : A ≤ subspaceStabilizer ρ R) (hmove : ¬ R ≤ fixedSpace ρ A)
    (a : ActionEquiv (invariantSubspace ρ J R hJR).toRepresentation (linearNatural F 3)) :
    ∃ r : ℕ, r ≤ 4 ∧ ∃ f : K →* Matrix.GeneralLinearGroup (Fin r) F.Carrier,
      Function.Injective f := by
  let X := J ⊔ A
  have hXR : X ≤ subspaceStabilizer ρ R := sup_le hJR hAR
  have hc : K ≤ centralizer (X : Set G) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hKJ) (le_centralizer_iff.mp hKA))
  have hiJ := ExtensionConsequences.irreducible_of_equiv a
    (ExtensionConsequences.linearNatural_irreducible F (by decide : 2 ≤ 3))
  let τ := (invariantSubspace ρ X R hXR).toRepresentation
  have hi : IsIrreducible τ := by
    let := hiJ
    let : Nontrivial R := Subrepresentation.irreducible_module_nontrivial
      (invariantSubspace ρ J R hJR).toRepresentation
    rw [Representation.IsIrreducible,isSimpleOrder_iff]
    refine ⟨⟨⊥,⊤,?_⟩,fun S => ?_⟩
    · intro h
      have hh : (⊥ : Submodule (ZMod 2) R) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top hh
    · let S' : Subrepresentation (invariantSubspace ρ J R hJR).toRepresentation :=
        ⟨S.toSubmodule,fun g _ hv => S.apply_mem_toSubmodule (inclusion le_sup_left g) hv⟩
      rcases eq_bot_or_eq_top S' with h | h
      · left
        apply Subrepresentation.toSubmodule_injective
        exact congrArg (fun U : Subrepresentation (invariantSubspace ρ J R hJR).toRepresentation => U.toSubmodule) h
      · right
        apply Subrepresentation.toSubmodule_injective
        exact congrArg (fun U : Subrepresentation (invariantSubspace ρ J R hJR).toRepresentation => U.toSubmodule) h
  obtain ⟨r,e,he,f,hf⟩ := Suzuki.natural_support_faithful_multiplicity
    ρ K hfix m hm eK X J le_sup_left hc R hXR hi a.groupEquiv a.linearEquiv a.intertwines
  refine ⟨r,?_,f,hf⟩
  let O := orbitSpan ρ K R
  have hXO := CommutingMultiplicity.orbit_invariant_of_commuting ρ X K hc R hXR
  have hAO : A ≤ subspaceStabilizer ρ O := le_sup_right.trans hXO
  have hmoveO : ¬ O ≤ fixedSpace ρ A := fun hh => hmove ((le_orbitSpan ρ K R).trans hh)
  let σ := (invariantSubspace ρ X O hXO).toRepresentation
  let A' := A.subgroupOf X
  have hcost (S : Submodule (ZMod 2) V) (hXS : X ≤ subspaceStabilizer ρ S) :
      fixedCodim (invariantSubspace ρ X S hXS).toRepresentation A' =
        fixedCodim (subspaceImageRepresentation ρ S) (restrictedSubgroup ρ S A) := by
    apply congrArg (fun Q : Submodule (ZMod 2) S => Module.finrank (ZMod 2) (S ⧸ Q))
    rw [fixedSpace_restrictedSubgroup ρ S A (le_sup_right.trans hXS)]
    ext v
    constructor
    · intro hv b
      exact congrArg Subtype.val (hv ⟨⟨b,(show A ≤ X from le_sup_right) b.property⟩,b.property⟩)
    · intro hv b
      exact Subtype.ext (hv ⟨b,b.property⟩)
  have he' : ∀ x v, e (σ x v) = fun i => τ x (e v i) := he
  have hrep := fixedCodim_map_equivariant σ (BinaryParabolicNatural.copies (Fin r) τ)
    (MonoidHom.id X) e he' A'
  simp only [Subgroup.map_id,BinaryParabolicNatural.fixedCodim_copies,Fintype.card_fin] at hrep
  change fixedCodim (invariantSubspace ρ X O hXO).toRepresentation A' =
    r * fixedCodim (invariantSubspace ρ X R hXR).toRepresentation A' at hrep
  rw [hcost O hXO,hcost R hXR] at hrep
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hp := IsElementaryAbelian.isPGroup 2 A
  have hk := CommutingMultiplicity.kernel_commuting_orbit ρ A K hKA R
  have h₁ := rank_subspaceKernel_add_image ρ O A hAO hp
  have h₂ := rank_subspaceKernel_add_image ρ R A hAR hp
  have hr : rank (restrictedSubgroup ρ O A) = rank (restrictedSubgroup ρ R A) := by
    rw [hk] at h₁
    omega
  have hb := RPlusBound.restricted ρ
    (show A ∈ RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,QhatStar.mem_RPlus ρ hA⟩) O hAO hmoveO
  have hu := (actionRatio_le_nat_iff _ hb.1 2).mp hb.2
  rw [hr,hrep] at hu
  have hl := SL3OddNaturalNormalizer.natural_invariant_actor_rank_cost F.degree_pos ho F.card_eq
    ρ J R hJR a.groupEquiv a.linearEquiv a.intertwines A hA.1.2.1 hAR hmove
  have hpos := fixedCodim_pos_of_faithful (subspaceImageRepresentation ρ R)
    (subspaceImageRepresentation_injective ρ R) (hA.1.2.1.restrictedSubgroup ρ R hAR hmove).1
  nlinarith
end CFSG.Quasithin.ChapterD
