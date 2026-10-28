module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.FiveCosets
public import Theory.Representation.CentralCubicNaturalFour

/-!
# Natural markings of the full ambient plane normalizers

For each actual elementary plane A of a returning pair, the five-coset
kernel has central image of order three in its automizer. Fusion
transitivity makes this cubic fixed-point-free. The recovered F₄ scalars
and the automizer order 180 identify its actual action with the natural
GL₂(4) action. In particular this is an action marking, not just an
abstract isomorphism inferred from order.

The literal quotient by A is marked compatibly with ambient conjugation.
Gaschütz splitting then identifies the WHOLE ambient N_G(A) with
F₄² ⋊ GL₂(4), carrying every original plane element to its corresponding
translation. An actual complement and its natural action are also supplied.
Every local premise is proved from the H-type seed and one-class hypothesis.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(5a), pp.257–258.
These local normalizers do not by themselves establish ambient J₃ recognition.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
open Representation.CentralCubicNaturalFour
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D)

/-- The actual automizer on either original plane is natural GL₂(4). -/
theorem plane_automizer_natural (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ (f : A.normalizerMonoidHom.range ≃* LinearGroup) (e : A ≃* Plane),
      ∀ g a, e (g • a) = naturalAction (f g) (e a) := by
  obtain ⟨hC,hc⟩ := P.plane_automizer_central_cubic hclass A hA hAR
  exact automorphism_marking _ (P.plane_normalizer_action_card hclass A hA hAR) hA
    (P.plane_automizer_transitive hclass A hA) _ hC hc

/-- The quotient marking respects the literal ambient conjugation on the same plane. -/
theorem plane_quotient_natural (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ (q : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃* LinearGroup)
      (e : A ≃* Plane),
      ∀ (n : normalizer (A : Set G)) (a : A),
        e (A.normalizerMonoidHom n a) =
          naturalAction (q (QuotientGroup.mk n)) (e a) := by
  obtain ⟨f,e,he⟩ := P.plane_automizer_natural hclass A hA hAR
  let q := ((QuotientGroup.quotientMulEquivOfEq
    (P.plane_normalizer_action_kernel A hA hAR).symm).trans
      (QuotientGroup.quotientKerEquivRange A.normalizerMonoidHom)).trans f
  exact ⟨q,e,fun n a => he (A.normalizerMonoidHom.rangeRestrict n) a⟩

/-- The WHOLE ambient plane normalizer is the naturally marked affine group over F₄. -/
theorem plane_normalizer_natural (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ (q : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃* LinearGroup)
      (e : A ≃* Plane) (f : normalizer (A : Set G) ≃* Plane ⋊[naturalAction] LinearGroup),
      (∀ (n : normalizer (A : Set G)) (a : A),
        e (A.normalizerMonoidHom n a) = naturalAction (q (QuotientGroup.mk n)) (e a)) ∧
      (∀ a : A, f (inclusion le_normalizer a) = SemidirectProduct.inl (e a)) ∧
      (A.subgroupOf (normalizer (A : Set G))).map f.toMonoidHom =
        (SemidirectProduct.inl : Plane →* Plane ⋊[naturalAction] LinearGroup).range := by
  obtain ⟨q,e,he⟩ := P.plane_quotient_natural hclass A hA hAR
  obtain ⟨C,hC⟩ := P.plane_normalizer_splits hclass A hA hAR
  let eV := (subgroupOfEquivOfLe (le_normalizer : A ≤ normalizer (A : Set G))).trans e
  obtain ⟨f,hf,hm⟩ := exists_marked_semidirect_equiv_of_split_coordinates
    (A.subgroupOf (normalizer (A : Set G))) C hC q eV naturalAction (by
      intro n a
      exact he n ((subgroupOfEquivOfLe le_normalizer) a))
  exact ⟨q,e,f,he,fun a => hf ((subgroupOfEquivOfLe le_normalizer).symm a),hm⟩

/-- An actual complement is GL₂(4), acting naturally on the original plane. -/
theorem plane_complement_natural (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ (C : Subgroup (normalizer (A : Set G))) (f : C ≃* LinearGroup) (e : A ≃* Plane),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
      ∀ (c : C) (a : A), e (A.normalizerMonoidHom c a) = naturalAction (f c) (e a) := by
  obtain ⟨f,e,he⟩ := P.plane_automizer_natural hclass A hA hAR
  obtain ⟨C,j,hC,_,hj⟩ := P.plane_normalizer_marked_complement hclass A hA hAR
  refine ⟨C,j.trans f,e,hC,?_⟩
  intro c a
  have hh := he (j c) a
  change e ((j c : MulAut A) a) = _ at hh
  rw [hj] at hh
  exact hh

end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
