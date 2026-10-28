module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Local
public import Theory.GroupTheory.Recognition.QuasithinM23.ExceptionalSplitting

/-!
# Splitting the exceptional local in the original nonmaximal linear row

The constructed exceptional overcomponent has its original self-centralizing
E₁₆ core and actual A₇ quotient. The fixed-point-free cubic and Gaschütz
argument constructs a complement, and a section for every chosen quotient
marking. Thus later marking arguments may use this splitting without adding
it as a source hypothesis. This proves the splitting step of Aschbacher–Smith
5.2.17, printed p.655 (`refs/quasithin.pdf`); the compatible native marking is
a further step, and ambient M₂₃ recognition is not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The original exceptional local splits over its actual two-core, with a
section preserving any supplied seven-point quotient marking. -/
theorem Preparation.linear_exceptional_splitting
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) :
    (∃ C : Subgroup J, (pCore 2 J).IsComplement' C) ∧
      ∀ e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7),
        ∃ s : alternatingGroup (Fin 7) →* J,
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))).comp s = MonoidHom.id _ := by
  have hTH := hH.1.1.2
  have hn := (d.block_overcomponent_parameter h hTH hp F hm hF (.inl he) hJ.1 hKJ).1
  have hb := d.linear_four_overcomponent_exceptional (hn ▸ h) hTH hp F hm hF he hJ.1 hKJ
  obtain ⟨ha,hcard,_⟩ := d.linear_overcomponent_action h hTH hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hcard
  have hcard : Nat.card (pCore 2 J) = 16 := hcard
  let := ha
  have hC : centralizer (pCore 2 J : Set J) = pCore 2 J :=
    le_antisymm (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hJ.1) (fun x hx y hy => setLike_mul_comm hy hx)
  have apply_split (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7)) :
      (∃ C : Subgroup J, (pCore 2 J).IsComplement' C) ∧
      ∃ s : alternatingGroup (Fin 7) →* J,
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))).comp s = MonoidHom.id _ := by
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = pCore 2 J :=
      (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
    exact ⟨QuasithinM23.exceptional_exists_complement (pCore 2 J) hcard q hq hk hC,
      QuasithinM23.exceptional_exists_section (pCore 2 J) hcard q hq hk hC⟩
  exact ⟨(apply_split hb.2.1.some).1,fun e => (apply_split e).2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
