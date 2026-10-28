module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.Comparison
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension
import Mathlib.Tactic.NormNum

/-!
# Extending the A₅ transfer kernel to the full second centralizer

The normal index-four kernel and the prescribed local C₂ × S₄ generate the
whole centralizer: the local A₄ has the same index four. On the target, the
literal subgroup {1} × A₅ and the first-four-letters C₂ × S₄ likewise generate
C₂ × S₅, with exactly the same local intersection.

The A₅ marking-extension and faithful-restriction assertions then align the
kernel maps and their conjugation actions. Normal-supplement gluing gives an
actual equivalence retaining the entire prescribed local inclusion. The
existing comparison theorem supplies the central mark and ambient fusion.

The intrinsic A₅ marking and restriction assertions are discharged by
`Theory.SpecificGroups.Alternating.FiveSubgroupExtension`.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.2, printed p.39.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Equiv Equiv.Perm
namespace FiveExtension

/-- The actual alternating factor, with trivial central coordinate. -/
def modelKernel (n : ℕ) : Subgroup (Model n) :=
  (⊥ : Subgroup (Multiplicative (ZMod 2))).prod (alternatingGroup (Fin n))

instance (n : ℕ) : (modelKernel n).Normal := inferInstanceAs
  (((⊥ : Subgroup (Multiplicative (ZMod 2))).prod (alternatingGroup (Fin n))).Normal)

theorem mem_modelKernel (n : ℕ) (x : Model n) :
    x ∈ modelKernel n ↔ x.1 = 1 ∧ sign x.2 = 1 := by
  change (x.1 ∈ (⊥ : Subgroup (Multiplicative (ZMod 2))) ∧
    x.2 ∈ alternatingGroup (Fin n)) ↔ _
  rw [mem_bot, mem_alternatingGroup]

def modelKernelEquiv (n : ℕ) : modelKernel n ≃* alternatingGroup (Fin n) where
  toFun x := ⟨x.val.2, x.property.2⟩
  invFun a := ⟨(1, a.val), ⟨by simp, a.property⟩⟩
  left_inv x := Subtype.ext (Prod.ext (mem_bot.mp x.property.1).symm rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem modelKernel_index (n : ℕ) (hn : 2 ≤ n) : (modelKernel n).index = 4 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [modelKernel, index_prod, index_bot, alternatingGroup.index_eq_two]
  norm_num [Nat.card_eq_fintype_card]

theorem modelKernel_comap (n : ℕ) (hn : 4 ≤ n) :
    (modelKernel n).comap (modelInclusion n hn) = modelKernel 4 := by
  ext x
  rw [mem_comap, mem_modelKernel, mem_modelKernel]
  change (x.1 = 1 ∧ sign (x.2.extendDomain (firstFour n hn)) = 1) ↔ _
  rw [sign_extendDomain]

private theorem sup_range_eq_top {H A : Type*} [Group H] [Group A]
    (N : Subgroup H) [N.Normal] (f : A →* H)
    (hN : N.index = 4) (hf : (N.comap f).index = 4) : N ⊔ f.range = ⊤ := by
  apply index_eq_one.mp
  have h := relIndex_mul_index (show N ≤ N ⊔ f.range from le_sup_left)
  rw [relIndex_sup_left, ← index_comap, hf, hN] at h
  omega

/-- The prescribed local inclusion supplements the target A₅. -/
theorem model_generation : modelKernel 5 ⊔ (modelInclusion 5 (by decide)).range = ⊤ := by
  apply sup_range_eq_top
  · exact modelKernel_index 5 (by decide)
  · rw [modelKernel_comap]
    exact modelKernel_index 4 (by decide)

variable {G : Type*} [Group G] {z t : G} {s : LocalSeed z t}

theorem kernel_comap (d : TransferKernel s) : d.K.comap s.embed = modelKernel 4 := by
  ext x
  exact (d.local_mem x).trans (mem_modelKernel 4 x).symm

/-- The transfer kernel and the original local image generate the centralizer. -/
theorem kernel_generation (d : TransferKernel s) : d.K ⊔ s.embed.range = ⊤ := by
  let := d.normal
  apply sup_range_eq_top d.K s.embed d.index
  rw [kernel_comap]
  exact modelKernel_index 4 (by decide)

theorem kernel_intersection (d : TransferKernel s) :
    s.embed.range.subgroupOf d.K = d.evenMap.range := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    have hxK : s.embed x ∈ d.K := hx.symm ▸ a.property
    obtain ⟨hfst, hsign⟩ := (d.local_mem x).mp hxK
    let b : A4 := ⟨x.2, mem_alternatingGroup.mpr hsign⟩
    refine ⟨b, Subtype.ext ?_⟩
    change s.embed (evenEmbed b) = a.val
    have hb : evenEmbed b = x := Prod.ext hfst.symm rfl
    rw [hb, hx]
    rfl
  · rintro ⟨b, rfl⟩
    exact ⟨evenEmbed b, rfl⟩

theorem kernel_intersection_card (d : TransferKernel s) :
    Nat.card (s.embed.range.subgroupOf d.K) = 12 := by
  rw [kernel_intersection, d.evenMap_range_card]

/-- The literal local map, transported along the given injective seed. -/
noncomputable def localMap (s : LocalSeed z t) : s.embed.range →* Model 5 :=
  (modelInclusion 5 (by decide)).comp (MonoidHom.ofInjective s.injective).symm.toMonoidHom

theorem localMap_apply (s : LocalSeed z t) (x : Model 4) :
    localMap s ⟨s.embed x, ⟨x, rfl⟩⟩ = modelInclusion 5 (by decide) x := by
  change modelInclusion 5 (by decide)
    ((MonoidHom.ofInjective s.injective).symm ((MonoidHom.ofInjective s.injective) x)) = _
  rw [MulEquiv.symm_apply_apply]

theorem localMap_injective (s : LocalSeed z t) : Function.Injective (localMap s) :=
  (modelInclusion_injective 5 (by decide)).comp (MonoidHom.ofInjective s.injective).symm.injective

theorem localMap_range (s : LocalSeed z t) :
    (localMap s).range = (modelInclusion 5 (by decide)).range := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    exact ⟨(MonoidHom.ofInjective s.injective).symm a, rfl⟩
  · rintro x ⟨a, rfl⟩
    exact ⟨⟨s.embed a, ⟨a, rfl⟩⟩, localMap_apply s a⟩

theorem localMap_intersection (d : TransferKernel s) (a : s.embed.range) :
    localMap s a ∈ modelKernel 5 ↔ (a : Centralizer t) ∈ d.K := by
  obtain ⟨x, hx⟩ := a.property
  have ha : a = ⟨s.embed x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
  rw [ha, localMap_apply]
  change modelInclusion 5 (by decide) x ∈ modelKernel 5 ↔ s.embed x ∈ d.K
  rw [← mem_comap, modelKernel_comap, mem_modelKernel, d.local_mem]

/-- Gluing preserves every local element, including the central coordinate. -/
theorem localExtension_of_marking (d : TransferKernel s)
    (eK : d.K ≃* alternatingGroup (Fin 5)) :
    Nonempty (LocalExtension s 5 (by decide)) := by
  let := d.normal
  obtain ⟨E, hE⟩ := AlternatingFiveSubgroupExtension.exists_equiv_normal_supplement
    AlternatingFiveSubgroupExtension.markingExtension
    AlternatingFiveSubgroupExtension.restrictionFaithful
    d.K s.embed.range (modelKernel 5) eK (modelKernelEquiv 5)
    (localMap s) (localMap_injective s) (kernel_generation d)
    (by rw [localMap_range]; exact model_generation)
    (localMap_intersection d) (kernel_intersection_card d)
  exact ⟨⟨E, fun x => (hE ⟨s.embed x, ⟨x, rfl⟩⟩).trans (localMap_apply s x)⟩⟩

variable [Finite G]
/-- The actual consumer adds no ambient fusion assumption. -/
theorem markedModel_of_marking (d : TransferKernel s)
    (eK : d.K ≃* alternatingGroup (Fin 5)) (hz : orderOf z = 2) :
    Nonempty (MarkedModel z t 5) := by
  obtain ⟨c⟩ := localExtension_of_marking d eK
  exact ⟨c.markedModel hz⟩

end FiveExtension
end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
end
