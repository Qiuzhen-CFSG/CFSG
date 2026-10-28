module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Alternatives
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints

/-!
# Interfaces between the two arguments in original 14.6.15

`CriticalPair` retains the literal rank-eight alternative of 14.6.13,
including its F.9 vertex and its one conjugator. `NormalizerGeometry`
records the intermediate conclusions needed from the module argument on
printed p.1034. It does not assert their existence. In particular its
prime-order centralizer identities must be proved in both the residual
and exchanged PSL₂(16) cases before the second-normalizer argument applies.

The second argument must construct C.2.3 and an escaping component in
N_G(K₂), and then exclude it. None of those conclusions is a field below.
The source-theorem assembly retains both obligations.

Source: Aschbacher--Smith 14.6.13--15, printed pp.1031--1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The primitive residual hypothesis preceding 14.6.12, on H/O₂(H). -/
structure PrimitiveResidual (H : Subgroup G) (p : ℕ) : Prop where
  elementary : IsElementaryAbelian p (pResidual 2 (H ⧸ pCore 2 H))
  nontrivial : pResidual 2 (H ⧸ pCore 2 H) ≠ ⊥
  minimal : ∀ B : Subgroup (H ⧸ pCore 2 H), B.Normal →
    B ≤ pResidual 2 (H ⧸ pCore 2 H) →
      B = ⊥ ∨ B = pResidual 2 (H ⧸ pCore 2 H)

/-- The permitted earlier 14.6.13 input. The endpoint uses left conjugation
by `representative`; the book's right conjugator is its inverse. The subgroup
Dγ is expressed as the intersection with the actual action kernel on U_H/Z,
not as a new independent label. -/
structure CriticalPair {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (a : LocalQuotientAction D.H D.UH D.V₁)
    (Mc H1 : Subgroup G) where
  endpoint : h.CriticalEndpoint
  outside : endpoint.representative ∉ Mc
  proper_kernel : endpoint.conjugate D.UH ⊓ h.kernel D.UH < endpoint.conjugate D.UH
  actor_le : actorImage D.H (endpoint.conjugate D.UH) ≤ actorImage D.H H1
  point_le : endpoint.conjugate D.V₁ ≤ firstSupport a H1
  reverse_point_le : D.V₁ ≤ endpoint.conjugate (firstSupport a H1)
  moved_rank : Module.finrank (ZMod 2)
    (subspaceCommutator a.representation ⊤ ⊤) = 8

/-- The literal intermediate geometry on p.1034, before applying C.2.3.
The same pair of factors and the same conjugator occur in every field.
This is a target for the module argument, not an additional source hypothesis. -/
structure NormalizerGeometry (T Mc H H1 H2 U Z W1 W2 : Subgroup G) (g : G) where
  K1 : Subgroup G
  K2 : Subgroup G
  U1 : Subgroup G
  U2 : Subgroup G
  first_le : K1 ≤ Mc
  second_le : K2 ≤ Mc
  join_eq : K1 ⊔ K2 = residualClosure H Mc
  residual_first_le : residual H1 ≤ K1
  residual_second_le : residual H2 ≤ K2
  models :
    (K1 = residual H1 ∧ K2 = residual H2 ∧
      Nonempty ((K1 ⧸ pCore 2 K1) ≃* Multiplicative (ZMod 5)) ∧
      Nonempty ((K2 ⧸ pCore 2 K2) ≃* Multiplicative (ZMod 5))) ∨
    ((K1.subgroupOf Mc).IsCComponent ∧ (K2.subgroupOf Mc).IsCComponent ∧
      Nonempty ((K1 ⧸ pCore 2 K1) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) ∧
      Nonempty ((K2 ⧸ pCore 2 K2) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)))
  first_support_le : W1 ≤ U1
  second_support_le : W2 ≤ U2
  first_module_le : U1 ≤ U
  second_module_le : U2 ≤ U
  first_centralizes : U1 ≤ centralizer (K2 : Set G)
  second_centralizes : U2 ≤ centralizer (K1 : Set G)
  first_generated : closure {x : G | x ∈ K1 ∧ orderOf x = 5} = K1
  second_generated : closure {x : G | x ∈ K2 ∧ orderOf x = 5} = K2
  point_closure : closure {x : G |
    x ∈ centralizer (Z : Set G) ∧ orderOf x = 5} = residualClosure H Mc
  conjugate_point_closure : closure {x : G |
    x ∈ (residualClosure H Mc).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (Z : Set G) ∧ orderOf x = 5} =
        K2.map (MulAut.conj g).toMonoidHom
  point_core : Z ≤ K2.pCoreIn 2
  exchanged : ∃ s ∈ T, s ∉ normalizer (K1 : Set G) ∧
    K1.map (MulAut.conj s⁻¹).toMonoidHom = K2
  intersection_index : (Mc ⊓ normalizer (K2 : Set G)).relIndex Mc = 2
  intersection_core : (Mc ⊓ normalizer (K2 : Set G)).pCoreIn 2 = Mc.pCoreIn 2
  closure_normalizer : normalizer (residualClosure H Mc : Set G) = Mc

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
