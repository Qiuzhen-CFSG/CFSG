module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.NaturalSum.Span
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.NaturalSum.ModelSpan

/-!
# The natural direct sum in the selected closure

For K=L₁ and L₁T ≤ H₁ ≤ G₁, the actual image of ⟨V₃^H₁⟩ in G₁/V₁
is a finite direct sum of natural modules for K/O₂(K). The preceding flag
and natural seed marking remain explicit; the closure's elementary structure,
two-core kernel, conjugate markings, generation and decomposition are proved.
All summands use the seed's same group identification. Inner and field twists
are absorbed by binary-linear equivalences, including at q=4.

Source: Aschbacher--Smith 11.5.5(3), printed p.780; the specialization to
H₁=G₁ is the one used at the start of 11.5.7, printed p.781.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry.ClosureFlag
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (f : E.ClosureFlag)
    (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁) (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁)
    {hK : E.K = E.L₁} (m : f.NaturalSeed hK)

/-- Reparametrize the constructed quotient action by the seed's group marking. -/
def modelAction : Representation (ZMod 2)
    (NaturalSum.Actor E.input.field.Carrier) (f.Space H₁ hH hLH) :=
  (f.quotientAction H₁ hH hLH hK).comp m.groupEquiv.symm.toMonoidHom

/-- The source seed is an actual intertwiner for this same group marking. -/
def modelSeed : (NaturalSum.natural E.input.field.Carrier).IntertwiningMap
    (f.modelAction H₁ hH hLH m) where
  toLinearMap := f.markedSeedMap H₁ hH hLH m
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) (m.groupEquiv.symm g)
    have hg : m.groupEquiv (QuotientGroup.mk' (pCore 2 E.K) k) = g := by
      rw [hk, m.groupEquiv.apply_symm_apply]
    change f.markedSeedMap H₁ hH hLH m (linearNatural E.input.field 2 g v) = _
    rw [← hg, f.markedSeedMap_intertwines]
    change f.restrictedAction H₁ hH hLH hK k _ =
      f.quotientAction H₁ hH hLH hK
        (m.groupEquiv.symm (m.groupEquiv (QuotientGroup.mk' (pCore 2 E.K) k))) _
    rw [m.groupEquiv.symm_apply_apply]
    rfl

/-- Ambient conjugation induces genuine automorphisms of the marked matrix actor. -/
theorem modelAction_normalized : ∀ h : H₁,
    ∃ a : MulAut (NaturalSum.Actor E.input.field.Carrier), ∀ g v,
      f.action H₁ hH hLH h (f.modelAction H₁ hH hLH m g v) =
        f.modelAction H₁ hH hLH m (a g) (f.action H₁ hH hLH h v) := by
  intro h
  let a₀ := Subgroup.quotientAut (pCore 2 E.K) (actorConjugation H₁ hH h)
  refine ⟨MulAut.congr m.groupEquiv a₀, ?_⟩
  intro g v
  change f.action H₁ hH hLH h
    (f.quotientAction H₁ hH hLH hK (m.groupEquiv.symm g) v) =
      f.quotientAction H₁ hH hLH hK
        (m.groupEquiv.symm (m.groupEquiv (a₀ (m.groupEquiv.symm g)))) _
  rw [m.groupEquiv.symm_apply_apply]
  exact f.quotientAction_conjugation H₁ hH hLH hK h _ v

/-- Each actual H₁-conjugate of Ṽ₃ retains a natural marking for the
same K/O₂(K) identification. The image equality specifies the conjugate
seed itself, and the model theorem absorbs all induced field twists. -/
theorem conjugateSeed_marking (h : H₁) :
    ∃ j : (NaturalSum.natural E.input.field.Carrier).IntertwiningMap
      (f.modelAction H₁ hH hLH m), Function.Injective j ∧
      j.range.toSubmodule = (f.modelSeed H₁ hH hLH m).range.toSubmodule.map
        (f.action H₁ hH hLH h) :=
  NaturalSum.exists_conjugate_natural_embedding
    (f.action H₁ hH hLH) (f.modelAction H₁ hH hLH m)
    (f.modelAction_normalized H₁ hH hLH m) (f.modelSeed H₁ hH hLH m)
    (f.markedSeedMap_injective H₁ hH hLH m) h

include m in
/-- Source 11.5.5(3), on the literal closure quotient and actual K/O₂(K).
The output includes one common group marking and a compatible binary-linear
equivalence with a finite direct sum of standard natural modules. -/
theorem localClosure_natural_sum :
    ∃ n : ℕ, Nonempty (ActionEquiv (f.quotientAction H₁ hH hLH hK)
      (repeated (linearNatural E.input.field 2) n)) := by
  let : FiniteDimensional (ZMod 2) (f.Space H₁ hH hLH) := Module.Finite.of_finite
  obtain ⟨n, e, he⟩ := NaturalSum.natural_span_coordinates
    (f.action H₁ hH hLH) (f.modelAction H₁ hH hLH m)
    (f.modelAction_normalized H₁ hH hLH m) (f.modelSeed H₁ hH hLH m)
    (fun P hp => f.markedSeedMap_generates H₁ hH hLH m P hp)
  refine ⟨n, ⟨{ groupEquiv := m.groupEquiv, linearEquiv := e, intertwines := ?_ }⟩⟩
  intro k v
  have h := he (m.groupEquiv k) v
  change e (f.quotientAction H₁ hH hLH hK (m.groupEquiv.symm (m.groupEquiv k)) v) = _ at h
  rw [m.groupEquiv.symm_apply_apply] at h
  exact h

/-- The H₁=G₁ application used in 11.5.7. The underlying source subgroup
is E.U=⟨V₃^G₁⟩, and both original quotient maps are retained. -/
theorem globalClosure_natural_sum {hK : E.K = E.L₁} (m : f.NaturalSeed hK) :
    ∃ n : ℕ, Nonempty (ActionEquiv
      (f.quotientAction E.G₁ le_rfl (sup_le E.L₁_le_G₁ f.sylow_normalizes_point) hK)
      (repeated (linearNatural E.input.field 2) n)) :=
  f.localClosure_natural_sum E.G₁ le_rfl
    (sup_le E.L₁_le_G₁ f.sylow_normalizes_point) m

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry.ClosureFlag
