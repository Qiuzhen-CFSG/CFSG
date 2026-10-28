module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Action.Internal
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# Field coordinates for an internal natural Sylow action

An internal action on the full commutator layer U(L), together with the
natural block model, determines a homomorphism from S(R) to SL₂(F).
Faithfulness of the natural representation makes the choice of internal
representative immaterial. The image is the image of the prescribed Sylow
subgroup S(R) ∩ L. The short-group centrality condition shows that its
kernel centralizes the full U(L), including the central covering layer.

Sylow conjugacy puts this image in the upper-unipotent subgroup. Applying
the same change of basis to the actual quotient projection gives the
literal action (a,b) ↦ (a + tb,b), with both maps surjective and their
centralizer kernels retained. The result uses the two-dimensional natural
L₂(4) module, as specified by `IsL2EvenBlock`, also when the quotient group
is abstractly isomorphic to A₅.

This proves the conditional natural-module calculation. The source's
internal Sylow assertion remains an input, owned by the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2),(4),
printed p.155, and C.5.6 (*), printed p.156; the block model is C.1.12.
-/

public section

open Subgroup
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
variable {G : Type*} [Group G] {F : Type*} [Field F]

/-- Equality of the natural actions determines all matrix entries. -/
private theorem natural_faithful
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (hρ : ∀ g v, (ρ g v).toAdd = Representation.specialLinearNatural 2 g v.toAdd) :
    Function.Injective ρ := by
  intro g k he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact (hρ g (Multiplicative.ofAdd v)).symm.trans
    ((congrArg (fun a => (a (Multiplicative.ofAdd v)).toAdd) he).trans
      (hρ k (Multiplicative.ofAdd v)))

/-- Internal representatives give a well-defined matrix action. Core centrality
identifies its kernel on the full covering module, and the internal Sylow
hypothesis identifies its image. -/
private theorem exists_matrixAction [Finite G]
    {R L : Subgroup G} (hshort : ChapterC.IsShort L) (h : InternalSylowAction R L)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (hρ : ∀ g v, (ρ g v).toAdd = Representation.specialLinearNatural 2 g v.toAdd)
    (m : ChapterC.BlockModuleModel L ρ) :
    ∃ σ : S R →* Matrix.SpecialLinearGroup (Fin 2) F,
      (∀ s v, quotientProjection L m.moduleIso (moduleConjugate h.normalizes s v) =
        ρ (σ s) (quotientProjection L m.moduleIso v)) ∧
      (∀ s, σ s = 1 ↔ (s : G) ∈ centralizer (U L : Set G)) ∧
      (∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), σ.range = P) ∧
      (∀ s : S R, ∃ t : S R, (t : G) ∈ L ∧ σ t = σ s) := by
  classical
  let q := quotientProjection L m.moduleIso
  let f : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hext {g k : Matrix.SpecialLinearGroup (Fin 2) F}
      (he : ∀ v : U L, ρ g (q v) = ρ k (q v)) : g = k := by
    apply natural_faithful ρ hρ
    apply MulEquiv.ext
    intro w
    obtain ⟨v, rfl⟩ := quotientProjection_surjective L m.moduleIso w
    exact he v
  choose t ht hact using h.internal
  let a (s : S R) := f ⟨t s, ht s⟩
  have ha (s : S R) (v : U L) :
      q (moduleConjugate h.normalizes s v) = ρ (a s) (q v) := by
    rw [hact s]
    exact quotientProjection_conjugate m h.normalizes (t s) (ht s) v
  let σ : S R →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := a
      map_one' := by
        apply hext
        intro v
        rw [← ha]
        simp [moduleConjugate]
      map_mul' := by
        intro s r
        apply hext
        intro v
        rw [← ha, map_mul]
        change q (moduleConjugate h.normalizes (s * r) v) = ρ (a s) (ρ (a r) (q v))
        rw [← ha, ← ha]
        congr 1
        apply Subtype.ext
        simp [moduleConjugate, mul_assoc] }
  have haσ (s : S R) (v : U L) :
      q (moduleConjugate h.normalizes s v) = ρ (σ s) (q v) := ha s v
  have hi (s : S R) (hs : (s : G) ∈ L) : σ s = f ⟨s, hs⟩ := by
    apply hext
    intro v
    rw [← haσ]
    exact quotientProjection_conjugate m h.normalizes s hs v
  refine ⟨σ, ha, ?_, ?_, ?_⟩
  · intro s
    constructor
    · intro hs
      have hf : f ⟨t s, ht s⟩ = 1 := hs
      have hc : (⟨(t s : G), ht s⟩ : L) ∈ pCore 2 L := by
        have he : QuotientGroup.mk' (pCore 2 L) ⟨t s, ht s⟩ = 1 :=
          m.quotientIso.map_eq_one_iff.mp hf
        have hk : (⟨(t s : G), ht s⟩ : L) ∈ (QuotientGroup.mk' (pCore 2 L)).ker := he
        rwa [QuotientGroup.ker_mk'] at hk
      intro v hv
      obtain ⟨w, hw⟩ := (intrinsicModuleEquiv L).surjective ⟨v, hv⟩
      have hc' := hshort.core_centralizes_blockU hc (w : L) w.property
      have htfix : moduleConjugate h.normalizes (t s) (intrinsicModuleEquiv L w) =
          intrinsicModuleEquiv L w := by
        apply Subtype.ext
        change (t s : G) * ((w : L) : G) * (t s : G)⁻¹ = ((w : L) : G)
        have he := congrArg Subtype.val hc'
        change ((w : L) : G) * (t s : G) = (t s : G) * ((w : L) : G) at he
        rw [← he, mul_inv_cancel_right]
      have hsfix := (hact s (intrinsicModuleEquiv L w)).trans htfix
      rw [hw] at hsfix
      have he := congrArg (fun z : U L => (z : G) * (s : G)) hsfix
      simpa [moduleConjugate, mul_assoc] using he.symm
    · intro hs
      apply hext
      intro v
      rw [← haσ]
      have hv : moduleConjugate h.normalizes s v = v := by
        apply Subtype.ext
        change (s : G) * (v : G) * (s : G)⁻¹ = (v : G)
        rw [← hs (v : G) v.property, mul_inv_cancel_right]
      simp [hv]
  · obtain ⟨P, hP⟩ := h.sylow
    have hp (l : L) : l ∈ P ↔ (l : G) ∈ S R := by
      constructor
      · intro hl
        have hm : (l : G) ∈ (P : Subgroup L).map L.subtype := ⟨l, hl, rfl⟩
        exact (hP ▸ hm).1
      · intro hl
        have hm : (l : G) ∈ (P : Subgroup L).map L.subtype :=
          hP.symm ▸ ⟨hl, l.property⟩
        obtain ⟨k, hk, he⟩ := hm
        exact (Subtype.ext he : k = l) ▸ hk
    let Q := P.mapSurjective (f := f)
      (m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)))
    refine ⟨Q, ?_⟩
    change σ.range = (P : Subgroup L).map f
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨t s, ht s⟩, (hp _).mpr (t s).property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, (hp l).mp hl⟩, hi _ l.property⟩
  · intro s
    exact ⟨t s, ht s, hi (t s) (ht s)⟩

/-- Conjugate the Sylow image and change the module basis by the same matrix. -/
private theorem exists_coordinates [Finite G] [Finite F] [CharP F 2]
    {R L : Subgroup G} (hshort : ChapterC.IsShort L) (h : InternalSylowAction R L)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (hρ : ∀ g v, (ρ g v).toAdd = Representation.specialLinearNatural 2 g v.toAdd)
    (m : ChapterC.BlockModuleModel L ρ) :
    ∃ c : ActionCoordinates R L F, c.IsInternal := by
  classical
  obtain ⟨σ, hσ, hk, ⟨P, hP⟩, hi⟩ := exists_matrixAction hshort h ρ hρ m
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) F) P (upperUnipotentSylow F 2)
  let τ := (MulAut.conj g).toMonoidHom.comp σ
  have hτ : τ.range = upperUnipotent F := by
    rw [MonoidHom.range_comp, hP]
    exact congrArg (fun Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) =>
      (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) hg
  let e := MonoidHom.ofInjective (upperUnipotentHom_injective F)
  let f := τ.codRestrict (upperUnipotent F) (fun s => hτ ▸ (show τ s ∈ τ.range from ⟨s, rfl⟩))
  let p : S R →* Multiplicative F := e.symm.toMonoidHom.comp f
  have hp (s : S R) : upperUnipotentHom F (p s) = τ s :=
    MonoidHom.apply_ofInjective_symm (upperUnipotentHom_injective F) (f s)
  have hp_surj : Function.Surjective p := by
    intro x
    have hx : upperUnipotentHom F x ∈ τ.range := hτ.symm ▸ ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, upperUnipotentHom_injective F ?_⟩
    rw [hp, hs]
  have hp_ker (s : S R) : p s = 1 ↔ (s : G) ∈ centralizer (U L : Set G) := by
    rw [← (upperUnipotentHom_injective F).eq_iff, hp, map_one]
    exact (MulAut.conj g).map_eq_one_iff.trans (hk s)
  let q := quotientProjection L m.moduleIso
  let q' : U L →* Multiplicative (Fin 2 → F) := (ρ g).toMonoidHom.comp q
  have heq (s : S R) (v : U L) :
      q' (moduleConjugate h.normalizes s v) = ρ (τ s) (q' v) := by
    change ρ g (q (moduleConjugate h.normalizes s v)) = ρ (τ s) (ρ g (q v))
    rw [hσ]
    have hm : τ s * g = g * σ s := by
      simp [τ, MulAut.conj_apply, mul_assoc]
    calc
      ρ g (ρ (σ s) (q v)) = ρ (g * σ s) (q v) := by simp
      _ = ρ (τ s * g) (q v) := by rw [hm]
      _ = ρ (τ s) (ρ g (q v)) := by simp
  let c : ActionCoordinates R L F :=
    { normalizes := h.normalizes
      parameter := p
      parameter_surjective := hp_surj
      parameter_kernel := hp_ker
      projection := q'
      projection_surjective := (ρ g).surjective.comp (quotientProjection_surjective L m.moduleIso)
      projection_kernel := by
        intro v
        change ρ g (q v) = 1 ↔ _
        rw [(ρ g).map_eq_one_iff]
        exact quotientProjection_kernel L m.moduleIso v
      equivariant := by
        intro s v
        rw [heq, ← hp, hρ]
        ext i
        fin_cases i <;>
          simp [Representation.specialLinearNatural_apply, upperUnipotentHom,
            transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two] }
  refine ⟨c, ?_⟩
  intro s
  obtain ⟨t, ht, he⟩ := hi s
  refine ⟨t, ht, ?_⟩
  change p t = p s
  apply upperUnipotentHom_injective F
  rw [hp, hp]
  exact congrArg (MulAut.conj g) he

/-- The exact conditional natural-module coordinate contract: the field and both
maps are constructed from the block model and the internal Sylow action. -/
theorem linearSylowCoordinatesInput [Finite G] : LinearSylowCoordinatesInput (G := G) := by
  intro R L n hL h
  obtain ⟨_, hshort, F, instF, finF, hF, _, ρ, ⟨m⟩, hρ⟩ := hL
  let := instF
  let := finF
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨F, instF, finF, hF, exists_coordinates hshort h ρ hρ m⟩

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

end
