module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.Transport
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Theory.Representation.RepEquiv

/-!
# Transporting the endpoint actor estimate through an actual equivalence

Conjugation by an intertwining linear equivalence identifies the action images
and their full linear normalizers. The induced map preserves nontrivial
elementary actors, cubic action, rank and the literal common-fixed-space
codimension. Consequently a bound proved on the concrete adjoint quotient
applies to the original representation, including its outer actors.

Faithfulness and irreducibility also transport, allowing the concrete actor
calculation to use precisely the hypotheses supplied by the source.

Source application: Aschbacher–Smith, K.3.2, printed pp.454–455;
Guralnick–Malle author manuscript, Lemma 4.5 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) Group V} {τ : Representation (ZMod 2) Group W}

theorem injective_of_equiv (e : σ.Equiv τ) (hf : Function.Injective σ) :
    Function.Injective τ := by
  intro a b hab
  apply hf
  apply e.toLinearEquiv.conjRingEquiv.injective
  change e.toLinearEquiv.conj (σ a) = e.toLinearEquiv.conj (σ b)
  rw [e.conj_apply_self, e.conj_apply_self, hab]

theorem irreducible_of_equiv (e : σ.Equiv τ) (hi : IsIrreducible σ) :
    IsIrreducible τ :=
  (RepEquiv.ofRepresentationEquiv e.symm).irreducible_of_euqiv hi

private def unitConj (e : σ.Equiv τ) :
    (Module.End (ZMod 2) V)ˣ ≃* (Module.End (ZMod 2) W)ˣ :=
  Units.mapEquiv e.toLinearEquiv.conjRingEquiv.toMulEquiv

private theorem unitConj_action (e : σ.Equiv τ) (g : Group) :
    unitConj e (σ.asGroupHom g) = τ.asGroupHom g := by
  apply Units.ext
  exact e.conj_apply_self g

private theorem unitConj_image (e : σ.Equiv τ) :
    (actionImage σ).map (unitConj e).toMonoidHom = actionImage τ := by
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, (unitConj_action e g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨σ.asGroupHom g, ⟨g, rfl⟩, unitConj_action e g⟩

private theorem unitConj_normalizer (e : σ.Equiv τ) :
    (linearNormalizer σ).map (unitConj e).toMonoidHom = linearNormalizer τ := by
  change (Subgroup.normalizer (actionImage σ : Set (Module.End (ZMod 2) V)ˣ)).map
    (unitConj e).toMonoidHom = Subgroup.normalizer
      (actionImage τ : Set (Module.End (ZMod 2) W)ˣ)
  rw [Subgroup.map_equiv_normalizer_eq, unitConj_image]

/-- An actual representation equivalence conjugates the full linear normalizers. -/
noncomputable def normalizerEquiv (e : σ.Equiv τ) :
    linearNormalizer σ ≃* linearNormalizer τ :=
  ((unitConj e).subgroupMap (linearNormalizer σ)).trans
    (MulEquiv.subgroupCongr (unitConj_normalizer e))

/-- The normalizer equivalence intertwines the tautological vector actions. -/
theorem normalizerEquiv_intertwines (e : σ.Equiv τ)
    (g : linearNormalizer σ) (v : V) :
    e (normalizerRepresentation σ g v) =
      normalizerRepresentation τ (normalizerEquiv e g) (e v) := by
  change e (g.val.val v) = e (g.val.val (e.toLinearEquiv.symm (e.toLinearEquiv v)))
  rw [e.toLinearEquiv.symm_apply_apply]

/-- Transport the strict common-fixed-space bound, retaining every outer actor. -/
theorem actor_gap_of_equiv (e : σ.Equiv τ)
    (hmodel : ∀ A : Subgroup (linearNormalizer τ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation τ) A → rank A ≤ 4 →
      2 * rank A < fixedCodim (normalizerRepresentation τ) A)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation σ) A) (hr : rank A ≤ 4) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  let f := (normalizerEquiv e).toMonoidHom
  have hf : Function.Injective f := (normalizerEquiv e).injective
  have he := normalizerEquiv_intertwines e
  let : IsElementaryAbelian 2 A := hA.2
  have hAm : IsElementaryTwo (A.map f) := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hb
    exact hA.1 (Subgroup.map_injective hf (by simpa using hb))
  have hcm : IsCubic (normalizerRepresentation τ) (A.map f) :=
    Exceptional.cubic_map_equivariant _ _ f e.toLinearEquiv he hc
  have hgap := hmodel (A.map f) hAm hcm (by rwa [rank_map_injective f hf])
  rw [rank_map_injective f hf,
    ← fixedCodim_map_equivariant _ _ f e.toLinearEquiv he] at hgap
  exact hgap

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

