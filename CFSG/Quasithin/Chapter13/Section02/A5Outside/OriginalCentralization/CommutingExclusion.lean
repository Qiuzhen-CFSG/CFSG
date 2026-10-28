module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CommutingF11
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NativeLinear
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NativeSymplectic
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalG2Exclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairNativeSource

/-!
# Excluding the original commuting A5 pair without a core bound

The original pair supplies F.1.1 and its actual graph supplies the critical
pair. The native linear and symplectic comparisons force elementary whole
join-cores, contradicting the original pair. The native G2 comparisons
centralize the short-local core center, contradicting the original moved
central module. Both orientations are retained.

No normalized Borel, reduced catalogue, core bound, earlier5.2.3 theorem
or final-model exclusion is assumed.
Source: Aschbacher--Smith 13.2.8(1), p.880, and F.1.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The two genuine original modules cannot commute. The full local
actions and original Thompson movement suffice, at every core order. -/
theorem original_commuting_pair_impossible
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hVW : V ≤ centralizer (W : Set G)) : False := by
  have h := (original_commuting_pair_hypothesisF11
    d e hjoin hH hJd hJe q hq hk he hVW).2
  have a : ∀ i, Nonempty ((![L,K] i ⧸ pCore 2 (![L,K] i)) ≃*
      alternatingGroup (Fin 5)) := by
    intro i
    fin_cases i
    · exact ⟨d.quotient⟩
    · exact ⟨e.quotient⟩
  rcases a5_pair_native_comparisons_from_source h a with hsmall | hg | hg
  · obtain ⟨F,hField,hFinite,hChar,n,hn,hF,hsmall⟩ := hsmall
    let := hField
    let := hFinite
    let := hChar
    rcases hsmall with ⟨point,⟨c⟩⟩ | ⟨point,⟨c⟩⟩
    · exact original_commuting_pair_not_native_linear d e hjoin hH
        (d.localActor_surjective_of_thompson_moves hJd) q hq hk hVW h F hF hn point c
    · exact original_pair_not_reduced_symplectic d e hjoin hH hVW h F hF hn point c
  · obtain ⟨short,⟨c⟩⟩ := hg
    exact original_pair_not_reduced_g2 d e h (GaloisField 2 2) short c
  · obtain ⟨short,⟨c⟩⟩ := hg
    exact original_pair_not_reduced_g2 e d h.swap (GaloisField 2 2) short c

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
