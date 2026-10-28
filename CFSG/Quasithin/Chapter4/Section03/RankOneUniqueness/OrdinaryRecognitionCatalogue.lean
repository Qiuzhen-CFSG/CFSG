module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionLinear
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionField
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Exhausting the proved ordinary carrier exclusions

Apply the proved Theorem C catalogue to the actual central quotient of K.
The original full Sylow and proper local component exclude all Bender
carriers. The original C.2.8 module excludes the odd rows and J₁. The binary
degree and full-Sylow calculations exclude all alternating and higher linear
rows. Actual local placement and the R₀ action exclude the nonsymplectic
large-field rows and M₂₂/M₂₃. Every surviving symplectic row gives the full
OrdinarySymplecticMarking, with its field recovered from the original L.

The resulting disjunction states the precise unfinished source cases, with
actual quotient equivalences: binary triality, large Ree, derived G₂(2),
Tits, and eight sporadic carriers. It does not assert that those remaining
cases are impossible. Their source-specific elimination and final marking
remain with qt-d-1222-rankone-ordinary-symplectic-marking.
Source: Aschbacher--Smith A.2.4, C.3.1, and 4.3.6, printed pp.33,149--151,614.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
open ChapterA.Section02 ChapterA.Section03.SourceEmbeddings ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Full-Sylow properness excludes the complete actual Bender catalogue. -/
theorem ordinary_no_bender (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    (hm : IsBenderModel (c.K ⧸ center c.K)) : False := by
  let := ho.2
  let : IsSimpleGroup (c.K ⧸ center c.K) := IsQuasisimple.simple
  let : IsQuasisimple (c.K ⧸ center c.K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center c.K)) (QuotientGroup.mk'_surjective _)
  let e := MulEquiv.refl (c.K ⧸ center c.K)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  obtain ⟨P,_,hl,hproper⟩ := c.ordinary_model_local_data D ho e
  exact FiveLocalFF.CarrierSieve.not_bender_model
    (P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    (c.ordinaryLocal.map f) hl hproper hm

/-- Actual source application of the catalogue, all completed exclusions and
field recovery. Only the displayed genuine remaining quotient rows are retained. -/
theorem ordinary_marking_or_remaining_rows (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Nonempty (OrdinarySymplecticMarking c n) ∨
      Triality.Standard.IsTrialityGroupAt 2 (c.K ⧸ center c.K) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((c.K ⧸ center c.K) ≃* ReeF4.Model m)) ∨
      Nonempty ((c.K ⧸ center c.K) ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty ((c.K ⧸ center c.K) ≃* Tits.ParrottGroup) ∨
      (∃ name : SporadicName,
        (name = .m11 ∨ name = .m12 ∨ name = .m24 ∨ name = .j2 ∨ name = .j4 ∨
          name = .hs ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((c.K ⧸ center c.K) ≃* name.Carrier)) := by
  let := ho.2
  have hm := quasisimple_center_quotient_theoremC_model (c.c28.sqtk.subgroup c.K)
  cases hm with
  | alternating d hd e => exact (c.ordinary_no_alternating D ho hn hpsl hd e.some).elim
  | odd hm => exact (c.c28.no_ordinary_component_of_theoremC_odd_model c.K ho hm).elim
  | bender hm => exact (c.ordinary_no_bender D ho hm).elim
  | linear_binary d hd hm => exact (c.ordinary_no_higher_binary_linear D ho hn hpsl hd hm).elim
  | rank_two f hr =>
    cases hr with
    | linear hf hm =>
      by_cases h1 : f = 1
      · exact (c.ordinary_no_pslThree_binary ho hn hpsl (by simpa [h1] using hm)).elim
      · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
        exact (c.ordinary_no_pslThree D ho (by omega) hF e).elim
    | symplectic hf hm =>
      exact Or.inl (c.ordinarySymplecticMarking_of_symplectic_row D ho hn hpsl (by omega) hm)
    | g2 hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hq : 2 < Nat.card F := by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hf)
      exact (c.ordinary_no_g2 D ho hq e).elim
    | triality hf hm =>
      by_cases h1 : f = 1
      · exact Or.inr (Or.inl (by simpa [h1] using hm))
      · obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp hm
        have hq : 2 < 2 ^ f := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
          (Nat.pow_le_pow_right (by decide) (by omega))
        exact (c.ordinary_no_triality_large D ho f hf hq e).elim
    | ree_f4 m hm _ e => exact Or.inr (Or.inr (Or.inl ⟨m,hm,e⟩))
    | symplectic_derived _ e =>
      exact (c.ordinary_no_alternating D ho hn hpsl (by decide : 6 ≤ 8)
        (e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
    | g2_derived _ e => exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    | tits _ e => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  | sporadic hm =>
    rcases hm with ⟨name,hname,⟨e⟩⟩ | ⟨e⟩
    · cases name with
      | m22 => exact (c.ordinary_no_m22 D ho hn hpsl e).elim
      | m23 => exact (c.ordinary_no_m23 D ho hn hpsl e).elim
      | j3 => exact (hname rfl).elim
      | m11 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.m11,by simp,⟨e⟩⟩))))
      | m12 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.m12,by simp,⟨e⟩⟩))))
      | m24 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.m24,by simp,⟨e⟩⟩))))
      | j2 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.j2,by simp,⟨e⟩⟩))))
      | j4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.j4,by simp,⟨e⟩⟩))))
      | hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.hs,by simp,⟨e⟩⟩))))
      | he => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.he,by simp,⟨e⟩⟩))))
      | ru => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.ru,by simp,⟨e⟩⟩))))
    · exact (c.c28.no_ordinary_component_janko_central_quotient c.K ho e.some).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
