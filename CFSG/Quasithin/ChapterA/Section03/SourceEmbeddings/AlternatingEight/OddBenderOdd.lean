module
public import Theory.SpecificGroups.Alternating.EightSylowDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.GroupTheory.SylowCyclicDerivedSections
public import CFSG.Quasithin.ChapterA.Section03.RankThreeSylow
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import ABG.ChapterII.Section1.DerivedFrattini
public import ABG.ChapterII.Section1.WreathedDerived
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
/-!
# Excluding odd containing models for the original A₈ section

The odd Theorem C Sylow groups have dihedral, semidihedral or wreathed
presentations, hence cyclic derived subgroups. This property passes through
subgroups and surjections. The literal quotient B/O₂(B) therefore cannot
be PSL₄(2): the concrete A₈ Sylow has two distinct derived involutions.
No quasisimplicity of B or vanishing of its two-core is used.

The arbitrary stored PSU₃ form is transported to the standard special
unitary carrier before taking its actual projective image. Every section
transfer uses the subgroup inclusion and the specified quotient map.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 15.3.32(3), p.1133.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G]
private theorem cyclic_derived_of_shape {P : Type*} [Group P]
    (h : Stellmacher.IsSemidihedralGroup P ∨ ABG.IsWreathedGroup P) :
    IsCyclic (commutator P) := by
  rcases h with h | ⟨n,h⟩
  · obtain ⟨n,hn,hcard,a,b,ha,hb,hab,hgen⟩ := h
    exact (ABG.QuasiDihedral.derived_eq_frattini hn hcard a b ha hb hab hgen).2.2.1
  · obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation h
    exact P.derived_structure.2.1

/-- Every odd Theorem C model has cyclic derived Sylow two-subgroups. -/
theorem odd_model_sylow_derived_cyclic
    (hG : ChapterA.Section02.IsTheoremCOddModel G) (S : Sylow 2 G) :
    IsCyclic (commutator S) := by
  cases hG with
  | linear_two p n hp ho _ hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      have := Finite.one_lt_card (α := F)
      simp only [hn0,pow_zero] at hF
      omega
    apply sylow_derived_cyclic_of_injective e.toMonoidHom e.injective ?_ S
    intro P
    obtain ⟨m,_,⟨d⟩⟩ :=
      GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ⟨p,n,hp,ho,hn,hF⟩ P
    exact derived_cyclic_of_injective d.toMonoidHom d.injective
      (dihedral_derived_cyclic (2^m))
  | linear_three p hp ho hm =>
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let k : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let e' := e.trans (Atlas.fieldEquivPSL 3 k)
    apply sylow_derived_cyclic_of_injective e'.toMonoidHom e'.injective ?_ S
    intro P
    exact sylow_derived_cyclic_of_surjective (QuotientGroup.mk' (center SL(3,ZMod p)))
      (QuotientGroup.mk'_surjective _) (fun T => cyclic_derived_of_shape (sl3_sylow_shape p ho T)) P
  | unitary_three p hp ho hm =>
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F p := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hs : ∀ x, (ABG.unitaryForm 3 p 1 (by decide)).conj x = x ^ p := by
      intro x
      simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
    obtain ⟨k⟩ : Nonempty (J.specialSubgroup ≃* RankThreeSU p) :=
      J.nonempty_specialEquiv_of_card (ABG.unitaryForm 3 p 1 (by decide)) p
        hF (J.card_fixed_of_prime_frobenius (p := p) hconj)
        (GaloisField.card p (2*1) (by decide))
        ((ABG.unitaryForm 3 p 1 (by decide)).card_fixed_of_prime_frobenius hs)
    apply sylow_derived_cyclic_of_injective e.toMonoidHom e.injective ?_ S
    intro P
    apply sylow_derived_cyclic_of_surjective J.specialToProjective
      J.specialToProjective_surjective ?_ P
    intro T
    exact sylow_derived_cyclic_of_injective k.toMonoidHom k.injective
      (fun U => cyclic_derived_of_shape (su3_sylow_shape p ho U)) T

/-- An A₈ two-core quotient cannot occur in a subgroup of a group whose
Sylow two-subgroups have cyclic derived subgroup. -/
theorem not_linearFourTwo_section_of_cyclic_derived_sylows [Finite G]
    (hG : ∀ S : Sylow 2 G, IsCyclic (commutator S)) (B : Subgroup G)
    (hB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e' := (e.trans (Atlas.fieldEquivPSL 4 k)).trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  have hquot : ∀ S : Sylow 2 (B ⧸ pCore 2 B), IsCyclic (commutator S) :=
    sylow_derived_cyclic_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _)
      (sylow_derived_cyclic_of_injective B.subtype B.subtype_injective hG)
  let S : Sylow 2 (alternatingGroup (Fin 8)) := Sylow.nonempty.some
  exact _root_.AlternatingEight.sylow_derived_not_cyclic S
    (sylow_derived_cyclic_of_surjective e'.toMonoidHom e'.surjective hquot S)

/-- The actual local A₈ section excludes every odd Theorem C containing row.
This applies to B itself, retaining its potentially nontrivial O₂(B). -/
theorem not_linearFourTwo_section_of_odd_model [Finite G]
    (hG : ChapterA.Section02.IsTheoremCOddModel G) (B : Subgroup G)
    (hB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) : False :=
  not_linearFourTwo_section_of_cyclic_derived_sylows (odd_model_sylow_derived_cyclic hG) B hB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
