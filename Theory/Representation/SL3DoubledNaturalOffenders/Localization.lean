module
public import Theory.Representation.SL3DoubledNaturalOffenders
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Offenders on an identically marked doubled component

A faithful binary representation with a normal SL₃ component acting on two
identical natural copies transports to the literal doubled-module normalizer.
In odd binary field degree its offenders therefore lie in that component.
The component marking and the linear coordinates are retained explicitly.
This is the coordinate argument used in the B.5.10 product localization,
exposed at the representation layer for the C.1.34 whole-core application.

Source: Aschbacher--Smith B.5.9--10, printed pp.107--109; the existing
ProductGeometry.Localization proof and SL3DoubledNaturalOffenders estimates.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.SL3DoubledNaturalOffenders
variable {G U F : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  [Field F] [Finite F] [Algebra (ZMod 2) F] {n : ℕ}
/-- Every offender lies in the original normal component; the whole actor may have a nontrivial two-core. -/
theorem offender_le_normal_component (σ : Representation (ZMod 2) G U)
    (hfaith : Function.Injective σ) (L : Subgroup G) [L.Normal]
    (hF : Nat.card F = 2^n) (hn : 0 < n) (ho : Odd n)
    (mark : L ≃* SL F) (E : U ≃ₗ[ZMod 2] Space F)
    (he : ∀ l : L, ∀ v, E (σ l v) = representation F (mark l) (E v))
    {D : Subgroup G} (hD : IsOffender σ D) : D ≤ L := by
  let τ : Representation (ZMod 2) G (SL3DoubledNaturalOffenders.Space F) :=
    E.conjRingEquiv.toMonoidHom.comp σ
  let f := τ.asGroupHom
  have hf : Function.Injective f := by
    intro g h he
    apply E.conjRingEquiv.injective.comp hfaith
    exact congrArg Units.val he
  have ht (g : G) (v : U) :
      E (σ g v) = SL3DoubledNaturalOffenders.action F (f g)
        (E v) := by
    change _ = E (σ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hmark (g : L) : f g =
      (SL3DoubledNaturalOffenders.representation F).asGroupHom (mark g) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (σ g (E.symm v)) = _
    exact (he g (E.symm v)).trans
      (congrArg (representation F (mark g))
        (E.apply_symm_apply v))
  have he : L.map f = SL3DoubledNaturalOffenders.component F := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact ⟨mark ⟨g, hg⟩, (hmark ⟨g, hg⟩).symm⟩
    · rintro _ ⟨g, rfl⟩
      exact ⟨mark.symm g, (mark.symm g).property,
        (hmark (mark.symm g)).trans
          (congrArg (SL3DoubledNaturalOffenders.representation F).asGroupHom
            (mark.apply_symm_apply g))⟩
  have hDN : D.map f ≤ SL3DoubledNaturalOffenders.normalizer F := by
    change D.map f ≤ Subgroup.normalizer (SL3DoubledNaturalOffenders.component F)
    rw [← he]
    exact (Subgroup.map_mono (show D ≤ Subgroup.normalizer L by
      rw [Subgroup.normalizer_eq_top]; exact le_top)).trans (Subgroup.le_normalizer_map f)
  have hd := SL3DoubledNaturalOffenders.offender_le_component_of_le_normalizer
    hF hn ho
    (hD.map_equivariant σ (SL3DoubledNaturalOffenders.action F) f hf E ht) hDN
  rw [← he] at hd
  intro g hg
  obtain ⟨l, hl, heq⟩ := hd (Subgroup.mem_map_of_mem f hg)
  exact hf heq ▸ hl


end Representation.SL3DoubledNaturalOffenders
