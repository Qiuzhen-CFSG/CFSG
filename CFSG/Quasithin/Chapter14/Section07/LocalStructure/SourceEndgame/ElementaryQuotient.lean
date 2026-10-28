module

public import Theory.Representation.BinaryConjugationSection.TransitiveSquares
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.GroupAction.SubgroupConjugation

/-!
# Elementary abelianness in the original 14.7.73 quotient

For the original k, retain E=S∩Sᵏ, K=⟨S,Sᵏ⟩ and
P=⟨S∩P,Sᵏ∩P⟩, where Sᵏ uses right conjugation. The 14.7.72 Frattini
bound transports to Sᵏ and makes E/U central in K/U. It also makes both
root spaces square-one modulo U. Nontriviality of the recognized P/E
natural module supplies a nonzero square-one lift from one of these roots.
Transitivity on the fifteen nonzero vectors then proves P/U elementary.

This proves the square step without assuming that P/U is already a vector
space. The preceding construction of P, the two generation equalities and
the natural P/E identification remain inputs from the earlier stages of
14.7.73, owned by this source endgame. G.1.3 is the recognition input retained
by qt-14-07; this file does not replace that application by a dimension label.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.73(3), printed pp.1076–1077 (PDF pp.1093–1094).
-/

public section

open Subgroup Representation Representation.SL2FourNatural
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

variable {G : Type*} [Group G] [Finite G]

/-- The actual conjugate roots give central E/U and elementary P/U. -/
theorem elementary_source_quotient
    (K P S U : Subgroup G) (k : K)
    (qK : K →* SL) (hqK : Function.Surjective qK)
    (d : BinaryConjugationSection K P (S ⊓ S.conjBy ((k : G)⁻¹))
      (naturalRepresentation.comp qK))
    [(U.subgroupOf P).Normal]
    (hS : IsPGroup 2 S) (hPhi : (frattini S).map S.subtype ≤ U)
    (hNU : K ≤ normalizer U)
    (hKgen : K = S ⊔ S.conjBy ((k : G)⁻¹))
    (hPgen : P = (S ⊓ P) ⊔ (S.conjBy ((k : G)⁻¹) ⊓ P)) :
    ⁅S ⊓ S.conjBy ((k : G)⁻¹), K⁆ ≤ U ∧
      IsElementaryAbelian 2 (P ⧸ U.subgroupOf P) := by
  classical
  let f := (MulAut.conj ((k : G)⁻¹)).toMonoidHom
  have hUf : U.map f = U :=
    mem_normalizer_iff_map_conj_eq.mp (hNU (K.inv_mem k.property))
  have hPhik : (frattini (S.conjBy ((k : G)⁻¹))).map
      (S.conjBy ((k : G)⁻¹)).subtype ≤ U := by
    change (frattini (S.map f)).map (S.map f).subtype ≤ U
    rw [frattini_image_map S f (MulAut.conj ((k : G)⁻¹)).injective]
    exact (map_mono hPhi).trans_eq hUf
  have hSk : IsPGroup 2 (S.conjBy ((k : G)⁻¹)) := hS.map f
  have hcentral : ⁅S ⊓ S.conjBy ((k : G)⁻¹), K⁆ ≤ U := by
    exact (commutator_mono le_rfl hKgen.le).trans (intersection_commutator_sup_le
      (derived_le_of_frattini_image_le hS hPhi)
      (derived_le_of_frattini_image_le hSk hPhik) (hKgen.ge.trans hNU))
  have hsquares (A : Subgroup G) (hA : IsPGroup 2 A)
      (hF : (frattini A).map A.subtype ≤ U) : ∀ a ∈ A, a ^ 2 ∈ U := by
    let : Fact (IsPGroup 2 A) := ⟨hA⟩
    intro a ha
    exact hF ⟨(⟨a, ha⟩ : A) ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩
  have hs := hsquares S hS hPhi
  have hsk := hsquares (S.conjBy ((k : G)⁻¹)) hSk hPhik
  have hseed : ∃ p : P, (p : G) ^ 2 ∈ U ∧ d.coordinates p ≠ 1 := by
    by_contra hn
    push Not at hn
    have hleft : S ⊓ P ≤ S ⊓ S.conjBy ((k : G)⁻¹) := by
      intro a ha
      exact (d.coordinates_eq_one_iff ⟨a, ha.2⟩).mp (hn ⟨a, ha.2⟩ (hs a ha.1))
    have hright : S.conjBy ((k : G)⁻¹) ⊓ P ≤ S ⊓ S.conjBy ((k : G)⁻¹) := by
      intro a ha
      exact (d.coordinates_eq_one_iff ⟨a, ha.2⟩).mp (hn ⟨a, ha.2⟩ (hsk a ha.1))
    have hPE : P ≤ S ⊓ S.conjBy ((k : G)⁻¹) := hPgen.le.trans (sup_le hleft hright)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨p, hp⟩ := d.onto (Multiplicative.ofAdd v)
    exact hv (congrArg Multiplicative.toAdd
      (hp.symm.trans ((d.coordinates_eq_one_iff p).mpr (hPE p.property))))
  refine ⟨hcentral, d.elementary_quotient_of_transitive U hNU ?_
    (fun e he => hs e he.1) hseed ?_⟩
  · rw [commutator_comm]
    exact (commutator_mono le_rfl d.section_le).trans hcentral
  · intro u v hu hv
    obtain ⟨g, hg⟩ := transitive_nonzero u v hu hv
    obtain ⟨a, ha⟩ := hqK g
    exact ⟨a, by change action (qK a) u = v; rw [ha, hg]⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
