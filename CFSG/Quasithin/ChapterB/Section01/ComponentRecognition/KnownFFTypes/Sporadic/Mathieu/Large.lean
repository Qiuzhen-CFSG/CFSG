module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.Degree
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms
public import Theory.Representation.BinaryPrimeDegreeCenter
public import Theory.Representation.Quotient
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M24.Properties.OuterRestriction

/-!
# The ambient action and assembly for large Mathieu recognition

For both actual central quotients M₂₃ and M₂₄, innerness of all quotient
automorphisms proves G = F*(G), even before eliminating its center. Once
the binary degree is eleven, prime-dimensional absolute irreducibility
eliminates the center. Native small-module recognition then transports to
the original representation, including its actual equivariant map.

The degree and native completeness inputs remain explicit. Consequently
the two final implications are conditional assemblies, not proofs of the
GM02 classification. Neither the full linear normalizer nor any local
offender calculation enters these implications.

Source: Aschbacher–Smith, Chapter K, printed pp.451, 457–458; the recognition
input cited there is GM02 Theorem 6.6 and Table 6.7. The native M₂₄ small
recognition input is also the James input to G.7.3(2), printed p.348.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
open Subgroup Theory.GroupTheory Representation Sporadic.Mathieu
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- There is no larger ambient actor in the M₂₃ branch, even for central covers. -/
theorem m23_generalizedFitting_eq_top
    (hL : IsQuasisimple (generalizedFitting G))
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M23) :
    generalizedFitting G = ⊤ := by
  let : IsQuasisimple (generalizedFitting G) := hL
  exact generalizedFitting_eq_top_of_inner_centralQuotient e m23_conj_surjective

/-- There is no larger ambient actor in the M₂₄ branch, even for central covers. -/
theorem m24_generalizedFitting_eq_top
    (hL : IsQuasisimple (generalizedFitting G))
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M24) :
    generalizedFitting G = ⊤ := by
  let : IsQuasisimple (generalizedFitting G) := hL
  exact generalizedFitting_eq_top_of_inner_centralQuotient e M24OuterRestriction.conj_surjective

omit [Finite G] in
/-- The degree bound removes the central cover, giving an actual ambient
isomorphism rather than merely an isomorphism of central quotients. -/
theorem ambient_equiv_of_prime_degree {S : Type*} [Group S]
    {ρ : Representation (ZMod 2) G V} (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* S)
    (ht : generalizedFitting G = ⊤) (hp : (Module.finrank (ZMod 2) V).Prime) :
    Nonempty (G ≃* S) := by
  let L := generalizedFitting G
  let : IsQuasisimple L := h.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hc : center L = ⊥ := center_eq_bot_of_binary_prime_finrank
    (ρ.comp L.subtype) (h.faithful.comp Subtype.val_injective) hp
    (Group.IsPerfect.not_isMulCommutative L)
  let d : L ≃* G := (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
  exact ⟨d.symm.trans ((QuotientGroup.quotientBot (G := L)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc.symm).trans e))⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem irreducible_of_fitting_eq_top
    {ρ : Representation (ZMod 2) G V} (h : SourceHypotheses ρ)
    (ht : generalizedFitting G = ⊤) : ρ.IsIrreducible := by
  have hs : Function.Surjective (generalizedFitting G).subtype := by
    intro g
    exact ⟨⟨g, ht ▸ mem_top g⟩, rfl⟩
  exact (irreducible_comp_surjective_iff _ hs ρ).mp h.irreducible

/-- Conditional K.4 recognition for the original M₂₃ actor. The two inputs
are independent degree and native completeness obligations, not ratio calculations. -/
theorem source_m23_of_degree_and_small_recognition
    (degree : M23DegreeEleven.{u,v}) (small : M23SmallRecognition.{v})
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M23) :
    generalizedFitting G = ⊤ ∧ Module.finrank (ZMod 2) V = 11 ∧
      (MathieuCode.IsM23Code ρ ∨ MathieuCode.IsM23Cocode ρ) := by
  have ht := m23_generalizedFitting_eq_top h.quasisimple e
  have hd := degree ρ h ⟨e⟩
  obtain ⟨a⟩ := ambient_equiv_of_prime_degree h e ht (hd ▸ by decide)
  have hi := irreducible_of_fitting_eq_top h ht
  have hs := (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective ρ).mpr hi
  refine ⟨ht, hd, ?_⟩
  rcases small (ρ.comp a.symm.toMonoidHom)
      (h.faithful.comp a.symm.injective) hs hd with hc | hc
  · obtain ⟨b, E, hE⟩ := hc
    left
    refine ⟨a.trans b, E, fun g v => ?_⟩
    simpa using hE (a g) v
  · obtain ⟨b, E, hE⟩ := hc
    right
    refine ⟨a.trans b, E, fun g v => ?_⟩
    simpa using hE (a g) v

/-- Conditional K.4 recognition for the original M₂₄ actor, using the exact
native degree-at-most-fourteen completeness input already owned for G.7.3. -/
theorem source_m24_of_degree_and_small_recognition
    (degree : M24DegreeEleven.{u,v})
    (small : ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) M24 W),
      Function.Injective σ → σ.IsIrreducible → Module.finrank (ZMod 2) W ≤ 14 →
      MathieuSmall.IsM24ToddOrDual σ)
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M24) :
    generalizedFitting G = ⊤ ∧ Module.finrank (ZMod 2) V = 11 ∧
      MathieuSmall.IsM24ToddOrDual ρ := by
  have ht := m24_generalizedFitting_eq_top h.quasisimple e
  have hd := degree ρ h ⟨e⟩
  obtain ⟨a⟩ := ambient_equiv_of_prime_degree h e ht (hd ▸ by decide)
  have hi := irreducible_of_fitting_eq_top h ht
  have hs := (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective ρ).mpr hi
  obtain ⟨b, hc⟩ := small (ρ.comp a.symm.toMonoidHom)
    (h.faithful.comp a.symm.injective) hs (by omega)
  refine ⟨ht, hd, a.trans b, ?_⟩
  rcases hc with hc | hc
  · obtain ⟨E⟩ := hc
    left
    refine ⟨Representation.Equiv.mk E.toLinearEquiv (fun g => ?_)⟩
    simpa using E.isIntertwining' (a g)
  · obtain ⟨E⟩ := hc
    right
    refine ⟨Representation.Equiv.mk E.toLinearEquiv (fun g => ?_)⟩
    simpa using E.isIntertwining' (a g)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
