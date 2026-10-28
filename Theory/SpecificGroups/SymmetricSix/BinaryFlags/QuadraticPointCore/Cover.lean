module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.Conjugation
public import Theory.Representation.BinaryPermutation.SixCorePoint
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient

/-!
# Quadratic subgroups of augmentation-cover point radicals

Every nonconstant point of the six-letter augmentation cover has a duad
stabilizer. Its two-core is a conjugate of the canonical point core, whose
quadratic subgroups have order at most four. For either fixed point, the
whole symmetric group is the stabilizer and its two-core is trivial.
Quadraticity passes through the actual natural projection; the cover and
its constant line are retained in the statement.

Source: Aschbacher--Smith, proof of 13.8.33, printed p.967.
-/

public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore

/-- A quadratic subgroup of any point radical on the full cover has order
at most four, including when the chosen point is fixed. -/
theorem cover_point_core_bound (A : Subgroup S) (v : core (Fin 6))
    (hA : A ≤ (SixCorePoint.stabilizer v).pCoreIn 2)
    (hq : ∀ g ∈ A, ∀ h ∈ A, ∀ w : core (Fin 6),
      coreRepresentation (Fin 6) g (coreRepresentation (Fin 6) h w - w) =
        coreRepresentation (Fin 6) h w - w) : Nat.card A ≤ 4 := by
  have hn : Quadratic A := by
    intro g hg h hh w
    obtain ⟨x,rfl⟩ := coreToNatural_surjective w
    have he := congrArg (coreToNatural (Fin 6)) (hq g hg h hh x)
    simpa only [coreToNatural_equivariant,map_sub] using he
  by_cases hv : ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a v = v
  · have hall : ∀ g : S, coreRepresentation (Fin 6) g v = v := by
      rcases (sixCore_fixed_iff v).mp hv with rfl | rfl
      · exact fun g => map_zero _
      · intro g
        apply Subtype.ext
        funext i
        rfl
    have htop : SixCorePoint.stabilizer v = ⊤ := by
      apply top_unique
      exact fun g _ => hall g
    have hcore : (⊤ : Subgroup S).pCoreIn 2 = ⊥ := by
      change (pCore 2 (⊤ : Subgroup S)).map (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom = ⊥
      rw [pCore_map_iso,s6_twoCore_eq_bot]
    have he : A = ⊥ := bot_unique (hA.trans_eq (htop ▸ hcore))
    rw [he,card_bot]
    decide
  · obtain ⟨g,hg⟩ := SixCorePoint.exists_point_stabilizer v hv
    have hc : A ≤ pointCore.map (MulAut.conj g.val).toMonoidHom := by
      apply hA.trans_eq
      rw [hg,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g.val).injective,H1_core_eq_pointCore]
    exact conjugate_core_bound A g.val hc hn

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
