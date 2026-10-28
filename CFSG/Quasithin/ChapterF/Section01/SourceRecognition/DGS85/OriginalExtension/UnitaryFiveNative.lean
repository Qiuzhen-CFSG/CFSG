module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.FlagRestoration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.FiveInner
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Exclusion

/-!
# Original U₅ restoration after the actual quasithin field sieve

The reduced marked line parabolic embeds in the original finite group. The
proved odd-rank obstruction therefore forces q = 4 when that group is
quasithin, for either orientation and every even prime-power input. For this
surviving row, the native lift and inner-flag theorem restore both original
endpoints in a type-preserving automorphism extension. Both reduced maps
and the full original Borel are retained, without assuming that S is inner.

Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228, and the actual
quasithin sieve in Aschbacher–Smith F.1.12, p.264. This does not assert a
general-parameter DGS restoration without quasithinness; reduced recognition
and the other source rows remain independent obligations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.UnitaryFiveNative
open GreenBook.UnitaryFive

def endpoint {q : ℕ} (M : Model q) (line : Bool) : Subgroup M.Carrier :=
  if line then M.leftParabolic else M.rightParabolic

theorem overlap_le_endpoint {q : ℕ} (M : Model q) (line : Bool) :
    M.overlap ≤ endpoint M line := by
  cases line
  · exact inf_le_right
  · exact inf_le_left

def amalgam {q : ℕ} (M : Model q) (line : Bool) :
    RankTwoAmalgam (endpoint M line) M.overlap (endpoint M (!line)) :=
  ofSubgroups _ _ _ (overlap_le_endpoint M line) (overlap_le_endpoint M (!line))

/-- Apply the source's actual quasithin sieve before restricting the parameter.
The embedding uses the literal reduced-to-original subgroup inclusion. -/
theorem field_eq_four_of_reduced_iso
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : Model q) (line : Bool)
    (e : Iso (reducedAmalgam L S) (amalgam M line)) : q = 4 := by
  cases line
  · exact M.field_size_eq_four_of_parabolic_embedding hq heven hG
      ((parabolic L (SuzukiContainment.reducedSylow L S) 1).subtype.comp e.right.symm.toMonoidHom)
      (Subtype.val_injective.comp e.right.symm.injective)
  · exact M.field_size_eq_four_of_parabolic_embedding hq heven hG
      ((parabolic L (SuzukiContainment.reducedSylow L S) 0).subtype.comp e.left.symm.toMonoidHom)
      (Subtype.val_injective.comp e.left.symm.injective)

theorem endpoints_generate (M : Model 4) (line : Bool) :
    endpoint M line ⊔ endpoint M (!line) = ⊤ := by
  cases line
  · exact (sup_comm _ _).trans (Chapter5.UnitaryNativeLift.Five.parabolics_generate M)
  · exact Chapter5.UnitaryNativeLift.Five.parabolics_generate M

theorem native_lifts (M : Model 4) (line : Bool)
    (a : Iso (amalgam M line) (amalgam M line)) :
    ∃ f : M.Carrier →* M.Carrier,
      (∀ x : endpoint M line, f (x : M.Carrier) = (a.left x : M.Carrier)) ∧
      (∀ x : endpoint M (!line), f (x : M.Carrier) = (a.right x : M.Carrier)) := by
  cases line
  · obtain ⟨f,hl,hr⟩ := Chapter5.UnitaryNativeLift.Five.native_automorphism M a.reverse
    exact ⟨f.toMonoidHom,hr,hl⟩
  · obtain ⟨f,hl,hr⟩ := Chapter5.UnitaryNativeLift.Five.native_automorphism M a
    exact ⟨f.toMonoidHom,hl,hr⟩

theorem inner_flag (M : Model 4) (line : Bool) (x : M.Carrier)
    (hl : (endpoint M line).map (MulAut.conj x).toMonoidHom = endpoint M line)
    (hr : (endpoint M (!line)).map (MulAut.conj x).toMonoidHom = endpoint M (!line)) :
    x ∈ M.overlap := by
  cases line
  · exact Chapter6.Source.RankOneGeneric.Global.UnitaryFullNormalizer.five_inner_flag M x ⟨hr,hl⟩
  · exact Chapter6.Source.RankOneGeneric.Global.UnitaryFullNormalizer.five_inner_flag M x ⟨hl,hr⟩

/-- The whole original U₅ pair, including its odd Borel and prescribed
reduced restrictions, is realized in one genuine automorphism extension. -/
theorem exists_original_extension_iso
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (M : Model 4) (line : Bool)
    (e : Iso (reducedAmalgam L S) (amalgam M line)) :
    ∃ E : SourceCompletion.UnitaryNonbinary.SourceExtension (endpoint M line) (endpoint M (!line)),
      ∃ F : Iso (originalAmalgam L S) E.amalgam,
        (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 0,
          (F.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) : MulAut M.Carrier) =
            MulAut.conj (e.left x : M.Carrier)) ∧
        (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 1,
          (F.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) : MulAut M.Carrier) =
            MulAut.conj (e.right x : M.Carrier)) ∧
        (∀ b : commonBorel L (SuzukiContainment.reducedSylow L S),
          (F.middle (inclusion (SuzukiContainment.reduced_commonBorel_le h) b) : MulAut M.Carrier) =
            MulAut.conj (e.middle b : M.Carrier)) := by
  apply exists_original_extension_of_native_flag h (endpoint M line) (endpoint M (!line))
    M.overlap (overlap_le_endpoint M line) (overlap_le_endpoint M (!line))
    (by cases line; exact inf_comm _ _; rfl) (endpoints_generate M line)
    (SourceCompletion.UnitaryNonbinary.five_conj_injective M) (inner_flag M line)
    (native_lifts M line) e

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.UnitaryFiveNative
