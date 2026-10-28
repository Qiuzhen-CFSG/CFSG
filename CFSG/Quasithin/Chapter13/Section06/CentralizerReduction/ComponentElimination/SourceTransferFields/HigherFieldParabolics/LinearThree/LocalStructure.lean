module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.KernelControl
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# Local structure of the actual marked SL₃ flag preimages

The image of Tᵥ∩K under the literal K→K⁺ map is a two-subgroup. Extend it
to a Sylow subgroup of SL₃ and conjugate that Sylow to the standard upper
unitriangular subgroup. The published flag construction can then be applied
with this same model equivalence.

KernelControl proves centrality of the literal intrinsic-to-plus comparison
kernel using the full earlier reduced-family condition and A.3.6. Thus each
normalized flag residual belongs to L(Gᵥ,Tᵥ), has quasisimple intrinsic
two-core quotient, and gives a minimal parabolic over every Sylow subgroup
mapping to Tᵥ. The moving-flag consumer retains maximality, the marked
intersection and the actual plus-core PSL₂ quotient. The final consumer
applies precisely short_of_C126, with the kernel premise discharged.

Parabolic normalization is supplied by qt-13-06-sl3-marked-module-obstruction.
The earlier reduced-family, Sylow, characteristic-two, 13.6.16(2), A.3.6 and
C.1.26 inputs retain their source meanings and are discharged by
qt-13-06-centralizer-reduction (A.3.6 is owned by qt-a03-sqtk-structure).
This conditional local-structure result does not complete the SL₃ exclusion;
that assembly belongs to qt-13-06-higher-field-sl3-parabolics.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.19, printed p.931, using the earlier source Sylow condition.
-/

@[expose] public section

open Subgroup
open Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
open ComponentSelection
universe u
variable {G : Type u} [Group G]
variable (F : Type*) [Field F] [Finite F]

/-- Conjugate the given model so the actual source intersection has its required marking. -/
theorem exists_aligned_model {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2 ^ m)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    ∃ e' : plusImage K L T z v hL hz K ≃* SL(3, F),
      ((Tv T v).subgroupOf K).map
        (e'.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
          Matrix.PSL3.LinearThree.unipotentSL F := by
  let f := e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)
  have hp := (Chapter1.isSylowIn_iff.mp hSylow).1
  obtain ⟨S, hS⟩ := (hp.comap_subtype.map f).exists_le_sylow
  obtain ⟨g, hg, _⟩ :=
    Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate F hm hF S
  let a := MulAut.conj g
  refine ⟨e.trans a.symm, ?_⟩
  change (((Tv T v).subgroupOf K).map (a.symm.toMonoidHom.comp f)) ≤ _
  rw [← map_map]
  calc
    _ ≤ (S : Subgroup SL(3, F)).map a.symm.toMonoidHom := map_mono hS
    _ = _ := by
      rw [← hg, map_map]
      have hi : a.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        exact a.symm_apply_apply x
      rw [hi, map_id]

/-- The aligned model feeds the published flag selection without a separate marking premise. -/
theorem moving_aligned_flag_residual [Finite G] [CharP F 2] {m : ℕ}
    (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (e₀ : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    ∃ e : plusImage K L T z v hL hz K ≃* SL(3, F),
      ((Tv T v).subgroupOf K).map
        (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
          Matrix.PSL3.LinearThree.unipotentSL F ∧
      ∃ P ∈ ({pointPreimage F K L T z v hL hz e,
        linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
        P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
          ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
          Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
            pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) := by
  obtain ⟨e, he⟩ := exists_aligned_model F (lt_trans Nat.zero_lt_one hm) hF
    K L T z v hL hz hSylow e₀
  exact ⟨e, he, moving_marked_flag_residual F hm hF K L T z v hL hz hK hn e he⟩

open Chapter1.Section02

/-- For either of the two normalized marked flags, the source kernel theorem
supplies the intrinsic local structure. Selection also preserves every literal
flag and quotient clause used by the higher-field branch. -/
theorem source_moving_marked_flag_local_structure [Finite G] [CharP F 2]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
        Matrix.PSL3.LinearThree.unipotentSL F)
    (hpoint : Tv T v ≤ normalizer (pointPreimage F K L T z v hL hz e : Set G))
    (hline : Tv T v ≤ normalizer (linePreimage F K L T z v hL hz e : Set G)) :
    ∃ P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) ∧
        Tv T v ≤ normalizer (residualIn P : Set G) ∧
        residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
        IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) ∧
        ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
          (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
            (residualIn P ⊔ Tv T v).subtype = Tv T v →
              ChapterB.IsMinimalParabolicOver S ⊤ := by
  obtain ⟨P, hflag, hPK, hmax, hinter, hmove, he⟩ :=
    moving_marked_flag_residual F hm hF K L T z v hL hz hK hn e hmark
  have hnP : Tv T v ≤ normalizer (P : Set G) := by
    rcases hflag with h | h
    · exact h ▸ hpoint
    · exact (Set.mem_singleton_iff.mp h) ▸ hline
  exact ⟨P, hflag, hPK, hmax, hinter, hmove, he,
    residualIn_normalized (Tv T v) P hnP,
    source_flag_local_structure hG hA36 F hF hm K L T P z v hv hL hz e hflag
      hK hnP hSylow hf hW⟩

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

/-- The actual C.1.26 application for a moving flag residual. Local membership,
intrinsic quasisimplicity, minimal parabolicity and comparison-kernel centrality
are conclusions of the source local argument, not additional premises. -/
theorem source_short_flag_residual [Finite G] [CharP F 2]
    (choices : DistinguishedPairs.{u})
    (source : C126Source CFSG.KnownSimple.IsKnownSimple choices)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (K L T P : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hflag : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (P : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (hmove : ¬ residualIn P ≤ centralizer ({z} : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D) :
    ChapterC.IsShort (residualIn P) := by
  obtain ⟨hlocal, hquasi, hpar⟩ := source_flag_local_structure hG hA36 F hF hm
    K L T P z v hv hL hz e hflag hK hn hSylow hf hW
  have hPK : P ≤ K := by
    rcases hflag with h | h
    · subst P
      exact preimageIn_le _ _ _
    · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp h
      subst P
      exact preimageIn_le _ _ _
  let := hquasi
  have hnR := residualIn_normalized (Tv T v) P hn
  exact short_of_C126 choices source (Tv T v) (residualIn P) hlocal.2 hnR
    (h16 _ hlocal hnR hmove)
    (residual_join_sqtk hG T P v hv (hPK.trans hK.1.1))
    (residual_join_characteristic_two T P v (hPK.trans hK.1.1) hSylow hf) hpar

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure

end
