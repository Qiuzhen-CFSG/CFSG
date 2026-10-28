module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.CoverReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.Symplectic.NaturalNormalizer

/-!
# Natural symplectic offenders in the original acting group

An actual action equivalence conjugates every ambient operator into the
binary general linear group. Normality of the component makes these
operators normalize its image. For fields larger than two, the component
image is exactly the derived natural image by perfectness.

Transporting the offender inequality to this literal normalizer and using
faithfulness brings containment back to the original component. The only
pending input is the explicitly quantified outer-centralizer rank bound;
no outer classification or offender-containment premise is assumed.

Source: Aschbacher--Smith B.5.1, final irreducible paragraph, printed p.100.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Transfer the natural normalizer calculation along an actual action equivalence. -/
theorem offender_le_natural_component_of_centralizer_bound
    [Finite G] (σ : Representation (ZMod 2) G V) (hfaith : Function.Injective σ)
    (L : Subgroup G) [L.Normal] (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv (σ.comp L.subtype) (binarySymplectic F))
    (hbound : ∀ a : naturalNormalizer (F := F.Carrier), orderOf a = 2 →
      a.val ∉ naturalDerivedImage →
      primeRank 2 (centralizer ({a} : Set (naturalNormalizer (F := F.Carrier)))) ≤
        2 * F.degree)
    {A : Subgroup G} (hA : IsOffender σ A) : A ≤ L := by
  let E := e.linearEquiv
  let σ' : Representation (ZMod 2) G (Vector F.Carrier) :=
    E.conjRingEquiv.toMonoidHom.comp σ
  let φ := linearAction σ'
  have hφ (g : G) (v : Vector F.Carrier) : φ g v = E (σ g (E.symm v)) := rfl
  have hfaith' : Function.Injective φ :=
    linearAction_injective σ' (fun x y hh => hfaith (E.conjRingEquiv.injective hh))
  have hnat (g : L) : φ g = linearAction (binarySymplectic F) (e.groupEquiv g) := by
    apply LinearEquiv.ext
    intro v
    rw [hφ]
    change e.linearEquiv (σ.comp L.subtype g (e.linearEquiv.symm v)) = _
    rw [e.intertwines, e.linearEquiv.apply_symm_apply]
    rfl
  have hcard : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  have hall (g : Sp F.Carrier) : g ∈ commutator (Sp F.Carrier) := by
    rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard]
    trivial
  have himage : L.map φ = naturalDerivedImage (F := F.Carrier) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨⟨e.groupEquiv ⟨g, hg⟩, hall _⟩, ?_⟩
      exact (hnat ⟨g, hg⟩).symm
    · rintro _ ⟨g, rfl⟩
      let x := e.groupEquiv.symm g.val
      refine ⟨x, x.property, ?_⟩
      have hx := hnat x
      rw [e.groupEquiv.apply_symm_apply] at hx
      exact hx
  have hnorm (g : G) : φ g ∈ naturalNormalizer := by
    change φ g ∈ normalizer (naturalDerivedImage (F := F.Carrier))
    rw [← himage]
    apply Subgroup.le_normalizer_map φ
    exact mem_map_of_mem φ (by rw [L.normalizer_eq_top]; trivial)
  let ψ : G →* naturalNormalizer (F := F.Carrier) := φ.codRestrict _ hnorm
  have hψ : Function.Injective ψ := fun x y hh => hfaith' (congrArg Subtype.val hh)
  have htransport (g : G) (v : V) : E (σ g v) = naturalNormalizerAction (ψ g) (E v) := by
    change E (σ g v) = φ g (E v)
    rw [hφ, E.symm_apply_apply]
  have ho := hA.map_equivariant σ naturalNormalizerAction ψ hψ E htransport
  have hc := naturalNormalizer_offender_le_of_centralizer_bound F.card_eq hn hbound ho
  intro a ha
  have hm : φ a ∈ naturalDerivedImage := hc (mem_map_of_mem ψ ha)
  rw [← himage] at hm
  obtain ⟨b, hb, hba⟩ := hm
  exact hfaith' hba ▸ hb

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
