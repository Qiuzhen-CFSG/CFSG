module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Normalizer
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Transport
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Faithful ambient extensions of the six-dimensional A₈ module

Conjugate the original action into the actual deleted permutation module.
Relative normality puts every ambient actor in the computed linear normalizer,
which is exactly the faithful S₈ image. Inverting this image identification
constructs a homomorphism preserving both the restricted A₈ marking and the
pointwise action. An odd permutation makes its image all of S₈; otherwise the
original group equals its marked A₈ subgroup.

Source: Aschbacher–Smith, K.3.2.2, printed p.455/PDF p.466, and
B.4.2(10), printed p.86/PDF p.97. The normalizer calculation is imported
from OrthogonalSix.Normalizer, with its attributed ATLAS comparisons.
-/

public section

open Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.OrthogonalSix

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- Embed every faithful normal extension in the full symmetric group,
preserving the specified alternating subgroup and its actual intertwiner. -/
theorem faithful_extension [L.Normal] (hf : Function.Injective ρ)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNaturalRepresentation (Fin 8))) :
    ∃ f : G →* Equiv.Perm (Fin 8), Function.Injective f ∧
      (∀ l : L, f l.val = (e.groupEquiv l).val) ∧
      (∀ g v, e.linearEquiv (ρ g v) =
        naturalRepresentation (Fin 8) (f g) (e.linearEquiv v)) := by
  let τ : Representation (ZMod 2) G (natural (Fin 8)) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  have ht (l : L) : τ.asGroupHom l.val =
      (alternatingNaturalRepresentation (Fin 8)).asGroupHom (e.groupEquiv l) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact (e.intertwines l (e.linearEquiv.symm v)).trans
      (congrArg (alternatingNaturalRepresentation (Fin 8) (e.groupEquiv l))
        (e.linearEquiv.apply_symm_apply v))
  have himage : actionImage (τ.comp L.subtype) =
      actionImage (alternatingNaturalRepresentation (Fin 8)) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨e.groupEquiv l, (ht l).symm⟩
    · rintro ⟨l, rfl⟩
      refine ⟨e.groupEquiv.symm l, ?_⟩
      change τ.asGroupHom (e.groupEquiv.symm l).val = _
      rw [ht, e.groupEquiv.apply_symm_apply]
  have hmem (g : G) : τ.asGroupHom g ∈ actionImage (naturalRepresentation (Fin 8)) := by
    have h := actionImage_le_linearNormalizer τ L ⟨g, rfl⟩
    change τ.asGroupHom g ∈ Subgroup.normalizer
      (actionImage (τ.comp L.subtype) : Set _) at h
    rw [himage] at h
    exact linearNormalizer_alternatingNatural_eq ▸ h
  have hi : Function.Injective (naturalRepresentation (Fin 8)).asGroupHom := by
    intro x y h
    apply naturalRepresentation_injective (Fin 8) (by decide)
    exact congrArg Units.val h
  let a := MonoidHom.ofInjective hi
  let f : G →* Equiv.Perm (Fin 8) :=
    a.symm.toMonoidHom.comp (τ.asGroupHom.codRestrict _ hmem)
  have he (g : G) : (naturalRepresentation (Fin 8)).asGroupHom (f g) = τ.asGroupHom g :=
    congrArg Subtype.val (a.apply_symm_apply ⟨τ.asGroupHom g, hmem g⟩)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x y h
    apply hf
    apply e.linearEquiv.conjRingEquiv.injective
    change τ x = τ y
    exact congrArg Units.val ((he x).symm.trans ((congrArg _ h).trans (he y)))
  · intro l
    apply hi
    exact (he l.val).trans (ht l)
  · intro g v
    have h := congrArg (fun u : (Module.End (ZMod 2) (natural (Fin 8)))ˣ =>
      u.val (e.linearEquiv v)) (he g)
    change naturalRepresentation (Fin 8) (f g) (e.linearEquiv v) =
      e.linearEquiv (ρ g (e.linearEquiv.symm (e.linearEquiv v))) at h
    rw [e.linearEquiv.symm_apply_apply] at h
    exact h.symm

/-- The specified normal A₈ action has exactly its own action and its marked
S₈ extension as faithful ambient possibilities. -/
theorem extension_alternatives [L.Normal] (hf : Function.Injective ρ)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNaturalRepresentation (Fin 8))) :
    L = ⊤ ∨ (L ≠ ⊤ ∧ Nonempty (MarkedActionEquiv ρ ⊤ L
      (naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8)))) := by
  classical
  obtain ⟨f, hfi, hfl, hfv⟩ := faithful_extension ρ L hf e
  have hpre (g : G) : f g ∈ alternatingGroup (Fin 8) ↔ g ∈ L := by
    constructor
    · intro hg
      let l := e.groupEquiv.symm ⟨f g, hg⟩
      have hx : f l.val = f g := by
        rw [hfl]
        exact congrArg Subtype.val (e.groupEquiv.apply_symm_apply ⟨f g, hg⟩)
      exact (hfi hx) ▸ l.property
    · intro hg
      rw [hfl ⟨g, hg⟩]
      exact (e.groupEquiv ⟨g, hg⟩).property
  have hr : alternatingGroup (Fin 8) ≤ f.range := by
    intro g hg
    refine ⟨(e.groupEquiv.symm ⟨g, hg⟩).val, ?_⟩
    rw [hfl, e.groupEquiv.apply_symm_apply]
  by_cases hL : L = ⊤
  · exact Or.inl hL
  refine Or.inr ⟨hL, ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ L := by
    by_contra h
    apply hL
    ext g
    simp_all
  have hodd : f g ∉ alternatingGroup (Fin 8) := fun h => hg ((hpre g).mp h)
  have hs : Function.Surjective f := by
    intro x
    by_cases hx : x ∈ alternatingGroup (Fin 8)
    · exact hr hx
    · have hy : x * (f g)⁻¹ ∈ alternatingGroup (Fin 8) := by
        rw [Subgroup.mul_mem_iff_of_index_two alternatingGroup.index_eq_two,
          Subgroup.inv_mem_iff]
        simp [hx, hodd]
      simpa using f.range.mul_mem (hr hy) (show f g ∈ f.range from ⟨g, rfl⟩)
  let a : G ≃* Equiv.Perm (Fin 8) := MulEquiv.ofBijective f ⟨hfi, hs⟩
  exact ⟨{
    action := {
      groupEquiv := Subgroup.topEquiv.trans a
      linearEquiv := e.linearEquiv
      intertwines := fun g v => hfv g.val v }
    contained := le_top
    subgroupEquiv := e.groupEquiv
    compatible := fun l => hfl l }⟩

end CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
