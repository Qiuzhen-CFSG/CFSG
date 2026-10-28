module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionDefs
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The actual natural layer inside the full automizer

The conjugation marking identifies the image of L on B with L/O₂(L),
then with the specified matrix group. The coordinate equivalence intertwines
that same image with the faithful automizer representation. Normality here
is relative to N_G(B); it follows from N_G(B) ≤ N_G(L).

Source: Aschbacher--Smith, 6.1.10--11, printed p.670, and B.4.2(1), p.86.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
variable {G : Type*} [Group G] {L B : Subgroup G}

noncomputable def layerAction (hLB : L ≤ normalizer (B : Set G)) :
    L →* ChapterE.inducedAutomizer B L :=
  ((B.normalizerMonoidHom.rangeRestrict).comp (inclusion hLB)).codRestrict _
    (fun l => ⟨⟨l, hLB l.property⟩, l.property, rfl⟩)

theorem layerAction_coe (hLB : L ≤ normalizer (B : Set G)) (l : L) :
    (layerAction hLB l : ChapterE.Automizer B) =
      B.normalizerMonoidHom.rangeRestrict ⟨l,hLB l.property⟩ := by rfl

theorem layerAction_surjective (hLB : L ≤ normalizer (B : Set G)) :
    Function.Surjective (layerAction hLB) := by
  rintro ⟨a, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem induced_normal (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G)) :
    (ChapterE.inducedAutomizer B L).Normal := by
  let : (L.subgroupOf (normalizer (B : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer hNL
  exact Subgroup.Normal.map inferInstance _ B.normalizerMonoidHom.rangeRestrict_surjective

variable [IsElementaryAbelian 2 B]
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

omit [Finite F] in
theorem marking
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (b : B),
      ((f.symm (Multiplicative.ofAdd
        (Representation.specialLinearNatural 2 (e (QuotientGroup.mk' (pCore 2 L) l))
          (f b).toAdd))) : G) = (l : G) * (b : G) * (l : G)⁻¹) :
    ∃ (j : ChapterE.inducedAutomizer B L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
      (E : Additive B ≃ₗ[ZMod 2] (Fin 2 → F)),
      ∀ (a : ChapterE.inducedAutomizer B L) (v : Additive B),
        E (ChapterE.automizerRepresentation B a v) =
          Matrix.mulVec (j a).val (E v) := by
  have hm : IsConjugationModel L B (Representation.specialLinearNatural (k := F) 2) := ⟨e,f,hf⟩
  let q := layerAction hm.normalizes
  have hq := layerAction_surjective hm.normalizes
  have hk : q.ker = pCore 2 L := by
    ext l
    have hc := hm.centralizer_eq_core (Representation.specialLinearNatural_injective 2)
    have hmem : q l = 1 ↔ (l : G) ∈ centralizer (B : Set G) := by
      constructor
      · intro h b hb
        have hh := congrArg (fun a : ChapterE.inducedAutomizer B L => ((a.val.val) ⟨b,hb⟩ : G)) h
        change (l : G) * b * (l : G)⁻¹ = b at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      · intro h
        apply Subtype.ext
        apply Subtype.ext
        apply MulEquiv.ext
        intro b
        apply Subtype.ext
        change (l : G) * (b : G) * (l : G)⁻¹ = b
        rw [← h b b.property, mul_inv_cancel_right]
    rw [MonoidHom.mem_ker, hmem]
    have hh : ((l : G) ∈ L ⊓ centralizer (B : Set G)) ↔ l ∈ pCore 2 L := by
      rw [hc]
      constructor
      · rintro ⟨x,hx,hxl⟩
        exact (L.subtype_injective hxl) ▸ hx
      · exact fun hl => mem_map_of_mem L.subtype hl
    simpa only [mem_inf, l.property, true_and] using hh
  let d : (L ⧸ pCore 2 L) ≃* ChapterE.inducedAutomizer B L :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hd (l : L) : d (QuotientGroup.mk' (pCore 2 L) l) = q l := rfl
  let j := d.symm.trans e
  let E : Additive B ≃ₗ[ZMod 2] (Fin 2 → F) :=
    LinearEquiv.ofBijective (f.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) f.bijective
  refine ⟨j,E,?_⟩
  intro a v
  obtain ⟨l,rfl⟩ := hq a
  have hj : j (q l) = e (QuotientGroup.mk' (pCore 2 L) l) := by
    rw [← hd]; exact congrArg e (d.symm_apply_apply _)
  rw [hj]
  apply Multiplicative.ofAdd.injective
  apply f.symm.injective
  apply Subtype.ext
  change (f.symm (f (B.normalizerMonoidHom ⟨l,hm.normalizes l.property⟩ v.toMul)) : G) = _
  rw [f.symm_apply_apply]
  exact (hf l v.toMul).symm
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
