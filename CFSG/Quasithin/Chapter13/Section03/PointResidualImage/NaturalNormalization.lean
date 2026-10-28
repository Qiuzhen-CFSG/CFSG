module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Covered
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.GroupTheory.TINormalizerControl
public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Section08
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

theorem source_natural_TI (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V := by
  let := SourceCompletion.local_elementary d
  let e : Additive V ≃ₗ[ZMod 2] natural (Fin 6) :=
    d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  intro g hg
  let Vg := V.map (MulAut.conj g).toMonoidHom
  let U := V ⊓ Vg
  have hLV : L ≤ normalizer (V:Set G) := le_sup_left.trans d.normalizes_V
  have hLg : L.map (MulAut.conj g).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (d.local_normalizer ▸ hg)
  have hLVg : L ≤ normalizer (Vg:Set G) := by
    rw [←hLg]
    exact (map_mono hLV).trans (V.le_normalizer_map _)
  have hLU : L ≤ normalizer (U:Set G) := by
    intro l hl
    rw [mem_normalizer_iff]
    intro x
    exact and_congr (mem_normalizer_iff.mp (hLV hl) x) (mem_normalizer_iff.mp (hLVg hl) x)
  let W : Subrepresentation (alternatingNaturalRepresentation (Fin 6)) := {
    toSubmodule := (AddSubgroup.toZModSubmodule 2 (U.subgroupOf V).toAddSubgroup).map e.toLinearMap
    apply_mem_toSubmodule := by
      rintro a w ⟨v,hv,rfl⟩
      obtain ⟨l,rfl⟩ := hα a
      have he := d.conjugation l v.toMul
      change e (Additive.ofMul (V.normalizerMonoidHom
        ⟨l.val,hLV l.property⟩ v.toMul)) = alternatingNaturalRepresentation (Fin 6) (α l) (e v) at he
      change alternatingNaturalRepresentation (Fin 6) (α l) (e v) ∈ _
      rw [←he]
      refine ⟨Additive.ofMul (V.normalizerMonoidHom ⟨l.val,hLV l.property⟩ v.toMul),?_,rfl⟩
      exact (mem_normalizer_iff.mp (hLU l.property) v.toMul.val).mp hv }
  let := alternatingNatural_isIrreducible (Ω := Fin 6) (by decide)
  rcases eq_bot_or_eq_top W with hb | ht
  · left
    apply bot_unique
    intro x hx
    let v : Additive V := Additive.ofMul ⟨x,hx.1⟩
    have hm : e v ∈ W := ⟨v,hx,rfl⟩
    rw [hb] at hm
    have he : e v = 0 := hm
    exact congrArg (fun w:Additive V => w.toMul.val) (e.injective (he.trans e.map_zero.symm))
  · right
    have hle : V ≤ Vg := by
      intro x hx
      let v : Additive V := Additive.ofMul ⟨x,hx⟩
      have hm : e v ∈ W := by rw [ht]; trivial
      obtain ⟨w,hw,he⟩ := hm
      have hew : w = v := e.injective he
      subst w
      exact hw.2
    exact (eq_of_le_of_card_ge hle
      (Nat.card_congr (V.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm.le).symm

theorem source_point_normalizes (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    {v : G} (hv : v∈V₁) (hne : v∉V⊓centralizer (L:Set G)) :
    M ⊓ centralizer ({v}:Set G) ≤ normalizer (V:Set G) := by
  have hvV : v∈V := (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) hv
  have hv0 : v≠1 := by intro he; exact hne (he ▸ one_mem _)
  exact inf_elementCentralizer_le_normalizer_of_trivial_intersections (source_natural_TI d) hvV hv0
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
