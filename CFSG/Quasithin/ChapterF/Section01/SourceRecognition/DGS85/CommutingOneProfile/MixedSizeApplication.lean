module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryBranch
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.OuterTransport

/-!
# The mixed A₅/S₃ application of the elementary-row count

Apply the Chapter 11 seed count to R = O₂(B) for the full original Borel
and Qβ = O₂(Pβ₀) for the actual reduced cubic parabolic. The conjugation
is by an element of that reduced endpoint, so it preserves its actual core.
At (qα,qβ) = (4,2), R has order 64. The already proved original/reduced
Borel comparison gives |S| = 64 or 128 without identifying a completion.

The Chapter 11 seed, intersection, and core-generation premises are explicit;
this conditional application does not establish their exhaustion from F.1.1,
the Borel model, or full (11.7). The mixed-size owner retains that assembly.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.7)(c), printed p.174, and (15.1), printed p.226.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
variable {G : Type*} [Group G] [Finite G]

/-- The literal mixed-pair application of the binary elementary-row count.
Its source geometric premises remain with the Chapter 11 profile proof. -/
theorem mixed_binary_elementary_row_size
    (K U S Zα Zα₂ : Subgroup G) (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (g : G)
    (hg : g ∈ parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1)
    (hconj : Zα.map (MulAut.conj g).toMonoidHom = Zα₂)
    (hn : twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1) ≤
      normalizer (Zα : Set G))
    (hcore : twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1) =
      pairSpan Zα Zα₂ (twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1)))
    (hR : twoCore (commonBorel ![K,U] S) = Zα ⊔
      twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1))
    (hZ : Nat.card Zα = 16)
    (hindex : (Zα ⊓ twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1)).relIndex Zα = 2)
    (hinter : Nat.card ((Zα ⊓ twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1)) ⊓
      (Zα₂ ⊓ twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1)) : Subgroup G) = 2) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  have hQ := (mem_normalizer_iff_map_conj_eq.mp
    ((show parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1 ≤ normalizer
      (twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1) : Set G) from
        (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hg))
  have hRcard : Nat.card (twoCore (commonBorel ![K,U] S)) = 64 := by
    simpa using sylow_card_of_pair_core
      (twoCore (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1))
      Zα Zα₂ (twoCore (commonBorel ![K,U] S)) g hQ hconj hn hcore hR
      4 2 (by decide) (by decide) (by norm_num; exact hZ) hindex hinter
  have hRc : Nat.card (pCore 2 (commonBorel ![K,U] S)) = 64 :=
    (card_map_of_injective (commonBorel ![K,U] S).subtype_injective).symm.trans hRcard
  have hcases := h.mixed_sylow_card_borel_core_cases eK eU
  rw [hRc] at hcases
  exact ⟨hRcard,by simpa using hcases⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
