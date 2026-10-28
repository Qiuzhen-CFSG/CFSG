module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CubicSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.NoncubicLinear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.G2
public import Theory.SpecificGroups.Suzuki.OddSubgroups

/-!
# The refined remaining field and cubic-cover cases of the split theorem

The new fixed-subfield proofs eliminate all symplectic and G₂ actors at
noncubic primes, and the proved binary PSL₃ absorption excludes that row.
Binary PSL₂ and Suzuki have cyclic odd Sylow subgroups; the small derived
and Tits rows have two-group outer automorphism groups. Applying these facts
to the full earlier catalogue leaves only PSU₃, triality and Ree at noncubic
primes. The cubic result already leaves odd-degree PSU₃ and classical covers.

All arguments use the original outside element and the literal two-core
component central quotient. `ReducedActorRemainder` is an explicit remaining
proof obligation, not a classification conclusion or an assumed source input.
The ordinary-root leaf consumes this reduction on its actual Cartan extension.
Source: Aschbacher–Smith A.3.18, pp.51–53, and 4.3.6, p.615.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels

/-- The noncubic source rows still requiring a field-actor proof. -/
inductive NoncubicFieldModel (S : Type*) [Group S] : Prop
  | unitary (n : ℕ) (hn : 2 ≤ n) (model : ClassicalGroup.IsPSU S 3 (2 ^ n))
  | triality (n : ℕ) (hn : 1 ≤ n) (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) S)
  | ree (m : ℕ) (hm : 1 ≤ m) (model : IsReeF4At S m)

variable {H : Type*} [Group H] [Finite H]

/-- Noncubic fixed-subfield and cyclic-Sylow exclusions on the original split domain. -/
theorem noncubic_even_model_remainder
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3)
    (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    (hm : EvenLieModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    NoncubicFieldModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) := by
  let : Fact p.Prime := ⟨hp⟩
  let B := K ⧸ pCore 2 K
  let S := B ⧸ center B
  let : IsSimpleGroup S := IsQuasisimple.simple
  have hrS : 1 < primeRank p S := by
    have he := primeRank_eq_of_surjective_of_coprime p (QuotientGroup.mk' (center B))
      (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])
    have ht := primeRank_quotient_eq_of_isTwoGroup p ho
      (pCore 2 K) pCore_isPGroup
    change primeRank p B = primeRank p S at he
    change primeRank p B = primeRank p K at ht
    rw [← he, ht]
    exact hr
  have hout : ¬ IsPGroup 2 (MulAut.Outer S) := by
    intro hh
    apply outer_not_twoGroup hH hK hp ho hr hz a ha haK
    exact hh.of_injective (MulAut.centralQuotientOuter (MulEquiv.refl _))
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl _))
  rcases hm with hm | hm
  · cases hm with
    | linear n hn hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hb := Matrix.SL2.binary_odd_primeRank_le_one (F := F) ho
      have he := primeRank_congr p (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
      rw [← he] at hb
      exact (not_lt_of_ge hb hrS).elim
    | unitary n hn hm => exact .unitary n hn hm
    | suzuki m hm he =>
      obtain ⟨e⟩ := he
      let P : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := default
      have hb := P.primeRank_le_one_of_isCyclic
        (BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two (by omega)
          (by rintro rfl; exact (by decide : ¬ Odd 2) ho) P)
      rw [← primeRank_congr p e] at hb
      exact (not_lt_of_ge hb hrS).elim
  · cases hm with
    | linear n hn hm => exact (not_noncubic_linear_twoCore_model
        hH hK hp ho hp3 hr hz (by omega) hm a ha haK).elim
    | symplectic n hn hm => exact (not_symplectic_twoCore_model
        hH hK hp ho hr hz hn hm a ha haK).elim
    | g2 n hn hm => exact (not_g2_twoCore_model
        hH hK hp ho hp3 hr hz hn hm a ha haK).elim
    | triality n hn hm => exact .triality n hn hm
    | ree m hm he => exact .ree m hm he
    | symplectic_derived he =>
      obtain ⟨e⟩ := he
      let d := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
      exact (hout ((IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card).of_equiv
        (MulAut.outerCongr d).symm)).elim
    | g2_derived he =>
      obtain ⟨e⟩ := he
      exact (hout (Theory.SpecificGroups.BinaryComponentResidual.g2_outer_two.of_equiv
        (MulAut.outerCongr e).symm)).elim
    | tits he =>
      obtain ⟨e⟩ := he
      exact (hout (Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_equiv
        (MulAut.outerCongr e).symm)).elim

/-- Remaining obligations after the linear, symplectic, G₂, rank-one and
small outer-two exclusions. This is not a source classification alternative. -/
def ReducedActorRemainder (p : ℕ) (K : Subgroup H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    NoncubicFieldModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))) ∧
    CubicUnitaryModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ Nat.card (center (twoCoreComponent K)) = 3 ∧
    ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
      IsSLSign (twoCoreComponent K) unitary 3 q)

/-- The universal split-domain reduction with every new row exclusion applied. -/
theorem alternatives_or_reduced_actor_remainder
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ ReducedActorRemainder p K := by
  rcases alternatives_or_actor_remainder hH hK hp ho hr a ha haK hgen with halt | hrem
  · exact Or.inl halt
  rcases hrem with ⟨hp3, hz, hm⟩ | hrem
  · exact Or.inr (Or.inl ⟨hp3, hz,
      noncubic_even_model_remainder hH hK hp ho hp3 hr hz hm a ha haK⟩)
  · exact Or.inr (Or.inr hrem)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
