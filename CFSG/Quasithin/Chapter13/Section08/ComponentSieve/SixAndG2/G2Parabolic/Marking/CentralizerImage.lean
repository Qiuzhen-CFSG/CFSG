module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Marking.CoreKernel
public import Theory.GroupTheory.CentralLineCorrection

/-!
# The literal line centralizer in the star quotient

An actor fixing the quotient image of A₁ may have a central error in V₁.
The nonzero commutator row of its generator against Q_H corrects that error
without changing the star image. Thus the actual centralizer image equals
the vector stabilizer, including when A₁ is not centralized by Q_H.
Source: Aschbacher–Smith 13.8.27, printed p.963.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry Atlas.G2

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) W}

theorem source_mem_line_centralizer_star_iff
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hcard : Nat.card V₁ = 2)
    (hcomm : ⁅Source.QH H,Source.UH H V₃⁆ ≤ V₁)
    (t : Source.UH H V₃) (ht : (t:G) ∈ c.Aone V₁) (ht1 : (t:G) ≠ 1)
    (hne : ¬ (t:G) ∈ centralizer (Source.QH H : Set G))
    (x : Source.Hstar H) :
    x ∈ Source.starImage H (centralizer (c.Aone V₁ : Set G)) ↔
      ρ x (s.quotient t).toAdd = (s.quotient t).toAdd := by
  have hcardA : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone,card_map_of_injective (MulAut.conj (c.gb:G)).injective,hcard]
  have htgen := zpowers_eq_top_of_prime_card hcardA
    (g := (⟨t,ht⟩ : c.Aone V₁)) (fun h => ht1 (congrArg Subtype.val h))
  have hAt : c.Aone V₁ = zpowers (t:G) := by
    have hh := congrArg (Subgroup.map (c.Aone V₁).subtype) htgen
    rw [MonoidHom.map_zpowers,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  have hC : centralizer (c.Aone V₁ : Set G) = centralizer ({(t:G)} : Set G) := by
    rw [hAt,zpowers_eq_closure,centralizer_closure]
  constructor
  · rintro ⟨a,ha,rfl⟩
    apply sub_eq_zero.mp
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    have hc : ⁅(a:G),(t:G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((mem_centralizer_iff.mp ha) t ht).symm
    change ⁅(a:G),(t:G)⁆ ∈ V₁
    rw [hc]
    exact V₁.one_mem
  · intro hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    have ha : ⁅(a:G),(t:G)⁆ ∈ V₁ := by
      apply (s.quotient_eq_zero_iff ⟨⁅(a:G),(t:G)⁆,s.commutator_mem a t⟩).mp
      rw [← s.displacement, hx, sub_self]
    have hn : ∃ q ∈ Source.QH H, ⁅(t:G),q⁆ ≠ 1 := by
      by_contra hn
      push Not at hn
      apply hne
      exact mem_centralizer_iff.mpr (fun q hq =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hn q hq)).symm)
    obtain ⟨q,hq,hqa⟩ := exists_centralizer_correction_of_binary_commutator
      (Source.QH H) V₁ hcard
      ((le_centralizer_iff.mp s.centralizes).trans (centralizer_le (pCoreIn_le 2 H)))
      t (fun q hq => (commutator_comm (Source.QH H) (Source.UH H V₃) ▸ hcomm)
        (commutator_mem_commutator t.property hq)) hn a ha
    have hqH := pCoreIn_le 2 H hq
    let q' : H := ⟨q,hqH⟩
    have hq1 : QuotientGroup.mk' (pCore 2 H) q' = 1 := by
      obtain ⟨b,hb,he⟩ := hq
      have he' : b = q' := Subtype.ext he
      subst b
      exact (QuotientGroup.eq_one_iff q').mpr hb
    refine ⟨q'*a, ?_, ?_⟩
    · change q*(a:G) ∈ centralizer (c.Aone V₁ : Set G)
      rwa [hC]
    · rw [map_mul,hq1,one_mul]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
