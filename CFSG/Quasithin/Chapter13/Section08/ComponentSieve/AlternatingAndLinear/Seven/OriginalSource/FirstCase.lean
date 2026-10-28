module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Structure

/-!
# Excluding the transvection case from the original local setup

The intrinsic component quotient constructs the faithful seven-point action;
the ambient Sylow supplies the exact Sylow inside H. The proved 13.8.5 source
theorem supplies the compatible transvection models, with B.1.8 discharged.
The partition and parity argument therefore excludes each actual critical
actor. In particular the inverse endpoint conjugate Vβ is placed in the
local two-core by F.9.13, rather than by an assumed permutation marking.

The last theorem passes from the corrected 13.8.8 alternatives to its strict
second case. The earlier theta, solvable-overgroup, covered-local and endpoint
facts remain explicit; no `SourceExclusion.Earlier` or `LocalData` is assumed.
This completes the first case of the source argument, not the two subsequent
partition branches of 13.8.24.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.24, printed p.958/PDF p.975.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open TransvectionRecognition TransvectionRecognition.Component.RecognitionStep
open TransvectionRecognition.Component.ModelExtension CriticalGeometry

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
  (localEarlier : Solvable.EarlierLocalInputs (G := G))
  (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
  (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hKn : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
  (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
  (htheta : sourceOne L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
  (h13 : ∀ J : Subgroup G, sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
    Group.IsSolvable J → J ≤ M)
  [Group.IsSolvable (sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G)]
  (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
    Nonempty ((sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) ≃*
      Multiplicative (Fin 2 → ZMod 3)))
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ)

include d earlier localEarlier hG64 hH hKH hK hKn hKT e htheta h13 hcover hρ

/-- No elementary actor inside a conjugate of the actual local two-core can
contain a transvection. Both the seven-point action and the 13.8.5 model
callback are constructed from their original source inputs. -/
theorem no_transvection_actor (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hBH : B ≤ H) (hAB : A ≤ B)
    (hy : ∃ y : H, B.map (MulAut.conj (y : G)).toMonoidHom ≤
      (sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) :
    ¬ ∃ a ∈ Source.starImage H A, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1 := by
  obtain ⟨φ, hi, hm, _⟩ := LocalGeometry.source_action_exists H K (T : Subgroup G)
    hKH (le_sup_right.trans hH.1.2) hK hKn T.isPGroup' hKT e
  have hAlt : alternatingGroup (Fin 7) ≤ φ.range := by
    rw [← hm]
    exact map_le_range φ _
  obtain ⟨S, hS⟩ := source_sylow hH
  exact LocalGeometry.exclude_first_case_actor H L (sourceOne L T V₁) (T : Subgroup G)
    G₁ M A B hH.1.2 hH.2.1 htheta h13 S hS ρ φ hi hAlt
    (fun a _ hc => AlternatingAndLinear.TransvectionSource.transvection_models
      d earlier localEarlier hG64 hH ρ hρ a hc)
    hcover hBH hAB hy

/-- Both corrected critical actors are excluded, retaining β = g_b⁻¹γ₁
and the original Vγ. The β placement follows from the terminal edge core. -/
theorem no_critical_transvections (c : CriticalPair L (T : Subgroup G) H V)
    (hedge : (L ⊔ (T : Subgroup G)) ⊓ H = sourceOne L T V₁ ⊔ (T : Subgroup G))
    (hterminal : Source.VH H V ≤
      (edgeGroup L (T : Subgroup G) H c.gamma c.previous).pCoreIn 2)
    (hgamma : c.Vgamma ≤ H)
    (hplacement : ∃ y : H, c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
      (sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) :
    (¬ ∃ a ∈ Source.starImage H (CriticalReciprocity.Vbeta c),
      a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∧
    (¬ ∃ a ∈ Source.starImage H c.Vgamma,
      a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) := by
  let := vh_elementary d hH
  let : IsElementaryAbelian 2 (CriticalReciprocity.Vbeta c) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  constructor
  · apply no_transvection_actor d earlier localEarlier hG64 hH hKH hK hKn hKT e
      htheta h13 hcover ρ hρ (CriticalReciprocity.Vbeta c) (CriticalReciprocity.Vbeta c)
      (CriticalReciprocity.Vbeta_le_H c (sourceOne L T V₁) hedge hterminal) le_rfl
    refine ⟨1, ?_⟩
    change (CriticalReciprocity.Vbeta c).conjBy 1 ≤ _
    rw [conjBy_one]
    exact CriticalReciprocity.Vbeta_le_twoCore c (sourceOne L T V₁) hedge hterminal
  · exact no_transvection_actor d earlier localEarlier hG64 hH hKH hK hKn hKT e
      htheta h13 hcover ρ hρ c.Vgamma c.Vgamma hgamma le_rfl hplacement

/-- The original A₇ branch must use the strict alternative of 13.8.8.
Only the preceding geometric alternative is retained; its transvection
cases are discharged by the source recognition and actual core placement. -/
theorem second_case (c : CriticalPair L (T : Subgroup G) H V)
    (hedge : (L ⊔ (T : Subgroup G)) ⊓ H = sourceOne L T V₁ ⊔ (T : Subgroup G))
    (hterminal : Source.VH H V ≤
      (edgeGroup L (T : Subgroup G) H c.gamma c.previous).pCoreIn 2)
    (hgamma : c.Vgamma ≤ H)
    (hplacement : ∃ y : H, c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
      (sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2)
    (halt : (∃ a ∈ Source.starImage H (CriticalReciprocity.Vbeta c),
        a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∨
      (∃ a ∈ Source.starImage H c.Vgamma, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∨
      LocalGeometry.SecondCase H (sourceOne L T V₁) (T : Subgroup G)
        (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma (c.Aone V₁) V₁ ρ) :
    LocalGeometry.SecondCase H (sourceOne L T V₁) (T : Subgroup G)
      (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma (c.Aone V₁) V₁ ρ := by
  obtain ⟨hb, hg⟩ := no_critical_transvections d earlier localEarlier hG64 hH hKH hK hKn hKT e
    htheta h13 hcover ρ hρ c hedge hterminal hgamma hplacement
  exact (halt.resolve_left hb).resolve_left hg

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
