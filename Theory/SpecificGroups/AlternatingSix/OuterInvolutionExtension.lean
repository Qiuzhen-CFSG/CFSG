module

public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.NaturalCoordinates
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.ActionTransport
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.Exceptional
public import Theory.AtlasPort.ExceptionalIsomorphisms.NineCoordinates
public import GorensteinWalter.Classification


/-!
# Recognizing transposition coordinates for an outer A₆ involution

An involution acting in the natural S₆ admits transposition coordinates,
possibly after the exceptional automorphism of S₆. Outside the natural
subgroup, the faithful generated extension is isomorphic to the canonical
exceptional subgroup of Aut(A₆).

The final theorem here is explicitly conditional on identifying that
canonical subgroup with the actual PGL₂ over the nine-element field.
Once this independent model comparison is supplied, the source exclusion
of PGL₂(9) forces the natural case. The matrix-model comparison remains an
obligation of the unconditional recognition theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

public section

open Subgroup Equiv
open AlternatingSix.ShadowLocal

namespace AlternatingSix.OuterInvolutionExtension

variable {G : Type*} [Group G] {L : Subgroup G} {r : G}

/-- Once the actor belongs to the natural S₆, a change of A₆ coordinates
makes it an actual transposition, with the full ambient action equation. -/
theorem exists_transposition_action_of_natural (e : L ≃* A6)
    (hrN : r ∈ normalizer (L : Set G)) (hr2 : r ^ 2 = 1)
    (hrout : r ∉ centralizer (L : Set G) ⊔ L)
    (hn : normalizerAction e ⟨r, hrN⟩ ∈ natural) :
    ∃ (e' : L ≃* alternatingGroup (Fin 6)) (s : Perm (Fin 6)), s.IsSwap ∧
      ∀ k : alternatingGroup (Fin 6),
        (e'.symm (MulAut.conjNormal s k) : G) = r * (e'.symm k : G) * r⁻¹ := by
  obtain ⟨a, s, hs, ha⟩ := natural_involution_transposition_coordinates
    (normalizerAction e ⟨r, hrN⟩) (normalizerAction_sq e hrN hr2) hn
    (normalizerAction_not_inner e hrN hrout)
  let e' := e.trans a
  have heq : normalizerAction e' ⟨r, hrN⟩ = MulAut.conjNormal s := by
    rw [← ha]
    apply MulEquiv.ext
    intro x
    rfl
  refine ⟨e', s, hs, ?_⟩
  intro k
  rw [← heq]
  change (e'.symm (e' (L.normalizerMonoidHom ⟨r, hrN⟩ (e'.symm k))) : G) = _
  rw [e'.symm_apply_apply]
  rfl

/-- The recognition step conditional only on the concrete exceptional-model
comparison. The comparison must be discharged before this is used as the
unconditional source recognition theorem. -/
theorem exists_transposition_action_of_exceptional_model [Finite G]
    (hPGL : Nonempty (canonicalExtension ≃*
      GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F))
    (e : L ≃* alternatingGroup (Fin 6))
    (hrN : r ∈ normalizer (L : Set G)) (hr2 : orderOf r = 2)
    (hrout : r ∉ centralizer (L : Set G) ⊔ L)
    (hexcl : ¬ Nonempty (↥(L ⊔ zpowers r) ≃*
      GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)) :
    ∃ (e' : L ≃* alternatingGroup (Fin 6)) (s : Perm (Fin 6)), s.IsSwap ∧
      ∀ k : alternatingGroup (Fin 6),
        (e'.symm (MulAut.conjNormal s k) : G) = r * (e'.symm k : G) * r⁻¹ := by
  have hrpow : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  apply exists_transposition_action_of_natural e hrN hrpow hrout
  by_contra hn
  obtain ⟨ec⟩ := exceptional_extension_equiv_canonical
    (normalizerAction e ⟨r, hrN⟩) (normalizerAction_sq e hrN hrpow) hn
  obtain ⟨ep⟩ := hPGL
  exact hexcl ⟨((extensionEquiv e hrN hr2 hrout).trans ec).trans ep⟩

end AlternatingSix.OuterInvolutionExtension
