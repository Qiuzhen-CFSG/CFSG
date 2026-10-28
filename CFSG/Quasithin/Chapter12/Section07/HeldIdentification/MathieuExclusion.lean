module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Excluding M₂₄ from the Held component branch

The actual M₂₄ involution coverage reduces every involution centralizer to
two marked representatives. A normal self-centralizing two-subgroup in
each representative excludes every component. An ambient isomorphism then
transports the component Kₜ of C_G(t) supplied by 12.7.5 to a contradiction.

Only the two representative kernel calculations remain explicit. Their
existing producers are `m24-centralizer-2a-shape` and
`m24-centralizer-2b-shape`; neither global recognition nor an order table is
an input. The source ambient component is the subgroup inside C_G(t), not
a subgroup normal in G. Its actual conjugate-closure definition is retained.

Source: Aschbacher–Smith, Theorem 12.7.7, printed pp.840–842. This supplies
its final M₂₄ exclusion from the earlier component alternative, once the
two intrinsic model calculations have been proved.
-/

open Subgroup Theory.GroupTheory
open Theory.GroupTheory.CentralizerSmallKernelTransport
open Sporadic.Mathieu Sporadic.Mathieu.M24InvolutionCentralizers

namespace CFSG.Quasithin.Chapter12.Section07.HeldIdentification

private theorem no_component_of_two_kernel {C : Type*} [Group C] [Finite C]
    (h : ∃ Q : Subgroup C, Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set C) ≤ Q)
    (K : Subgroup C) : ¬ IsComponent C K := by
  obtain ⟨Q, hn, hp, hc⟩ := h
  let := hn
  let : Group.IsNilpotent Q := hp.isNilpotent
  exact not_isComponent_of_solvable_normal_selfCentralizing Q hc K

private theorem no_component_of_conjugate {x y : M24} (hxy : IsConj x y)
    (h : ∃ Q : Subgroup (centralizer ({x} : Set M24)),
      Q.Normal ∧ IsPGroup 2 Q ∧
        centralizer (Q : Set (centralizer ({x} : Set M24))) ≤ Q)
    (K : Subgroup (centralizer ({y} : Set M24))) :
    ¬ IsComponent (centralizer ({y} : Set M24)) K := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have he : (MulAut.conj g) x = y := hg
  let e := (centralizerEquiv (MulAut.conj g) x).trans
    (MulEquiv.subgroupCongr (congrArg (fun z => centralizer ({z} : Set M24)) he))
  intro hK
  exact no_component_of_two_kernel h _ (hK.map_equiv e.symm)

/-- The genuine 12.7.5 component alternative excludes an actual M₂₄
isomorphism, conditional only on the two marked self-centralizing kernels.
Both original centralizers and every conjugation equivalence are retained. -/
public theorem not_isomorphic_m24_of_component
    {G : Type*} [Group G] [Finite G]
    (hA : ∃ Q : Subgroup centralizer2A,
      Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set centralizer2A) ≤ Q)
    (hB : ∃ Q : Subgroup centralizer2B,
      Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set centralizer2B) ≤ Q)
    (t : G) (ht : orderOf t = 2) (Lt : Subgroup G)
    (hK : IsComponent (centralizer ({t} : Set G))
      ((conjugateSpanBy Lt (centralizer ({t} : Set G))).subgroupOf
        (centralizer ({t} : Set G)))) :
    ¬ Nonempty (G ≃* M24) := by
  rintro ⟨e⟩
  have het : orderOf (e t) = 2 :=
    (orderOf_injective e.toMonoidHom e.injective t).trans ht
  have hcomponent := hK.map_equiv (centralizerEquiv e t)
  rcases involution_classes (e t) het with h | h
  · exact no_component_of_conjugate h hA _ hcomponent
  · exact no_component_of_conjugate h hB _ hcomponent

end CFSG.Quasithin.Chapter12.Section07.HeldIdentification
