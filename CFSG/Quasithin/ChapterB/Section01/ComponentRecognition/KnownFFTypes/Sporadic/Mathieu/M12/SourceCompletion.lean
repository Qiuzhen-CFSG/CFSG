module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M12.SourceDegree

/-!
# The degree-ten source M₁₂ module and its native ambient action

The proved cubic degree bound discharges the last premise of marked heart
recognition. The original component quotient marking identifies F*(G) with
M₁₂, and the literal G-action is equivariantly a restriction of the fixed
faithful Aut(M₁₂) action on the ten-dimensional heart. Its inner-automorphism
preimage is exactly F*(G). The source group alternatives and the complete
`Recognition` witness are re-exported from the preceding modules.

The ambient extension has a private implementation. Uniqueness of linear
implementers on the heart identifies its action with the native one without
unfolding that implementation. No degree, recognition, absolute-irreducibility
or full-linear-normalizer premise remains. Local geometry and ratio estimates
are separate source obligations.

Source: Aschbacher--Smith, Chapter K introduction and K.4, printed pp.451,
457--460, and H.11, printed pp.392--393 (1 March 2004 manuscript). The M₁₂
entry of Guralnick--Malle, *Classification of 2F-modules, I*, Theorem 6.6 and
Table 6.7, has binary degree ten and permits the outer automorphism. The
degree proof imported here uses concrete generation and binary degree-gap
theorems, rather than assuming that classification. The original paper is at
https://agag-malle.math.rptu.de/~malle/download/failfact.dvi.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
open Subgroup Theory.GroupTheory
open _root_.Sporadic.Mathieu
open CFSG.Quasithin.ChapterH.Section10To12
open CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

private theorem heart_extension_eq
    (σ : Representation (ZMod 2) (MulAut M12) M12Heart)
    (hσ : σ.comp MulAut.conj = m12HeartRepresentation) :
    σ = Ambient.automorphismRepresentation := by
  have implements (τ : Representation (ZMod 2) (MulAut M12) M12Heart)
      (hτ : τ.comp MulAut.conj = m12HeartRepresentation)
      (a : MulAut M12) (x : M12) (v : M12Heart) :
      τ a (m12HeartRepresentation x v) = m12HeartRepresentation (a x) (τ a v) := by
    have hx : a * MulAut.conj x = MulAut.conj (a x) * a := by
      ext y
      simp [MulAut.conj_apply]
    have hi (y : M12) : τ (MulAut.conj y) = m12HeartRepresentation y :=
      congrArg (fun r : Representation (ZMod 2) M12 M12Heart => r y) hτ
    have he := congrArg τ hx
    rw [map_mul, map_mul, hi, hi] at he
    exact congrArg (fun l : Module.End (ZMod 2) M12Heart => l v) he
  apply MonoidHom.ext
  intro a
  have he := Ambient.heart_intertwiner_unique a
    (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom a))
    (LinearMap.GeneralLinearGroup.toLinearEquiv (Ambient.automorphismRepresentation.asGroupHom a))
    (implements σ hσ a)
    (implements Ambient.automorphismRepresentation Ambient.automorphismRepresentation_inner a)
  exact congrArg LinearEquiv.toLinearMap he

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : Hypotheses ρ)
  (e : (generalizedFitting G ⧸ center (generalizedFitting G)) ≃* M12)

include h e in
/-- The source M₁₂ action has binary degree exactly ten. -/
theorem source_degree_eq_ten : Module.finrank (ZMod 2) V = 10 := by
  obtain ⟨r⟩ := source_recognition ρ h e
  exact r.moduleInput.finrank_eq_ten ρ

include h in
/-- Identify the literal source action with the fixed native automorphism-group
action. The original quotient marking is preserved, and precisely F*(G) induces
inner automorphisms. In particular the equivalence includes every outer actor. -/
theorem source_native_ambient_equiv :
    ∃ (f : generalizedFitting G ≃* M12) (ι : G →* MulAut M12),
      (∀ l, f l = e (QuotientGroup.mk' (center (generalizedFitting G)) l)) ∧
      Function.Injective ι ∧
      (∀ l : generalizedFitting G, ι (l : G) = MulAut.conj (f l)) ∧
      (MulAut.innerSubgroup M12).comap ι = generalizedFitting G ∧
      Nonempty (ρ.Equiv (Ambient.automorphismRepresentation.comp ι)) := by
  obtain ⟨r⟩ := source_recognition ρ h e
  let c := MulEquiv.subgroupCongr r.residual_eq.symm
  let f : generalizedFitting G ≃* M12 := c.trans r.moduleInput.residualEquiv
  let d := ambientExtension ρ r.moduleInput
  refine ⟨f, d.embedding, ?_, d.embedding_injective, ?_,
    d.comap_inner.trans r.residual_eq, ?_⟩
  · intro l
    exact r.quotient_mark (c l)
  · intro l
    exact d.embedding_residual (c l)
  · refine ⟨{ toLinearEquiv := r.moduleInput.moduleEquiv.toLinearEquiv,
              isIntertwining' := ?_ }⟩
    intro g
    apply LinearMap.ext
    intro v
    have hv := d.equivariant g v
    rw [heart_extension_eq d.automorphismRepresentation d.inner_action] at hv
    exact hv

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
