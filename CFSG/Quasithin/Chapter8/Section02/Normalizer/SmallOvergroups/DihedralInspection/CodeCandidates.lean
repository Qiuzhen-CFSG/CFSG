module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.Action
public import Theory.Representation.BinaryAlternatingSixPerfectOvergroups

/-!
# Candidate overgroups in the M₂₄-code row

An actual marking of U by the natural binary A₆ module transports the literal
image of K_U, preserving its included L_U action. Perfectness descends through
that action, so the concrete overgroup theorem gives equality or genuine A₇
and A₈ equivalences. Strict containment removes equality.

The simultaneous Aut_(T L_U)(U) image is retained in the same coordinates and
normalizes both marked groups, using only the original conjugation action on U.
No action of T on O²(I) or on Ω is assumed. This is the candidates step in
Aschbacher–Smith, Proposition 8.2.8(1), printed p.719/PDF p.736; the natural
marking comes from 8.2.6. The compatible representation exclusions and final
containment remain with the DihedralInspection assembly owner.
-/

public section
open Subgroup BinaryAlternatingSixPerfectOvergroups
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.DihedralInspection.CodeCandidates
variable {G : Type*} [Group G]

private theorem actionImage_perfect (K U : Subgroup G) [Group.IsPerfect K]
    (hKU : K ≤ normalizer (U : Set G)) : Group.IsPerfect (actionImage K U) := by
  let e := subgroupOfEquivOfLe hKU
  let : Group.IsPerfect (K.subgroupOf (normalizer (U : Set G))) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.map U.normalizerMonoidHom

private theorem actionImage_normalizes (H R U : Subgroup G)
    (hRU : R ≤ normalizer (U : Set G))
    (hHR : H ≤ normalizer (R : Set G)) :
    actionImage H U ≤ normalizer (actionImage R U : Set (MulAut U)) := by
  apply le_trans (map_mono (f := U.normalizerMonoidHom) ?_)
    (le_normalizer_map U.normalizerMonoidHom)
  rw [← subgroupOf_normalizer_eq hRU]
  exact subgroupOf_mono _ hHR

/-- Apply the concrete theorem to the actual action image, carrying the
8.2.6 marking through a genuine equivalence of U. -/
theorem actionImage_alternatives (L K U : Subgroup G) [Group.IsPerfect K]
    (e : U ≃* SixModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hRK : localResidual L U ≤ K) (hKU : K ≤ normalizer (U : Set G)) :
    actionImage K U = actionImage (localResidual L U) U ∨
      Nonempty (actionImage K U ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (actionImage K U ≃* alternatingGroup (Fin 8)) := by
  let c := MulAut.congr e
  let D := (actionImage K U).map c.toMonoidHom
  let : Group.IsPerfect (actionImage K U) := actionImage_perfect K U hKU
  let : Group.IsPerfect D := Group.IsPerfect.map _
  have hAD : alternatingImage ≤ D := by
    rw [← hmark]
    exact map_mono (map_mono (subgroupOf_mono _ hRK))
  rcases perfect_overgroup_alternatives D hAD with h | h | h
  · left
    exact map_injective c.injective (h.trans hmark.symm)
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨((actionImage K U).equivMapOfInjective
      c.toMonoidHom c.injective).trans f⟩)
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr ⟨((actionImage K U).equivMapOfInjective
      c.toMonoidHom c.injective).trans f⟩)

/-- If containment on the original U fails, its actual overgroup action is
A₇ or A₈. No extra premise classifying overgroups is retained. -/
theorem strict_actionImage_candidates (L K U : Subgroup G) [Group.IsPerfect K]
    (e : U ≃* SixModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hRK : localResidual L U ≤ K) (hKU : K ≤ normalizer (U : Set G))
    (hstrict : ¬ actionImage K U ≤ actionImage (localResidual L U) U) :
    Nonempty (actionImage K U ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (actionImage K U ≃* alternatingGroup (Fin 8)) := by
  rcases actionImage_alternatives L K U e hmark hRK hKU with h | h
  · exact (hstrict h.le).elim
  · exact h

/-- The original Aut_(T L_U)(U) marking normalizes both literal transported
action images. Only T-normalization of K is needed, as supplied after 8.2.6. -/
theorem marked_normalizer_actions (L K U T : Subgroup G)
    (e : U ≃* SixModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hRK : localResidual L U ≤ K) (hKU : K ≤ normalizer (U : Set G))
    (hTK : T ≤ normalizer (K : Set G))
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G)) :
    (actionImage (T ⊔ localResidual L U) U).map (MulAut.congr e).toMonoidHom ≤
        normalizer (alternatingImage : Set (MulAut SixModule)) ∧
      (actionImage (T ⊔ localResidual L U) U).map (MulAut.congr e).toMonoidHom ≤
        normalizer ((actionImage K U).map (MulAut.congr e).toMonoidHom :
          Set (MulAut SixModule)) := by
  constructor
  · have h := map_mono (f := (MulAut.congr e).toMonoidHom)
      (actionImage_normalizes (T ⊔ localResidual L U) (localResidual L U) U
        ((localResidual_le L U).trans inf_le_right)
        (sup_le (normalizes_localResidual L U T hTL hTU)
          (localResidual L U).le_normalizer))
    rwa [map_equiv_normalizer_eq, hmark] at h
  · have h := map_mono (f := (MulAut.congr e).toMonoidHom)
      (actionImage_normalizes (T ⊔ localResidual L U) K U hKU
        (sup_le hTK (hRK.trans K.le_normalizer)))
    rwa [map_equiv_normalizer_eq] at h

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.DihedralInspection.CodeCandidates
