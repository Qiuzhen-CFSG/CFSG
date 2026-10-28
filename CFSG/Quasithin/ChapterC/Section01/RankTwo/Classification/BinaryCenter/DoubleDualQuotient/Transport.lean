module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover.Transport

/-!
Transport the exact full-center doubled-dual quotient through a group
isomorphism. The simultaneous transport retains its common component marking
with the distance-four full cover, as required by original source 15.3.23.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.NaturalCenterDoubleDualQuotient
universe u
variable {A B : Type u} [Group A] [Group B]
private theorem block_map (e : B ≃* A) : (blockU B).map e.toMonoidHom = blockU A := by
  rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
private def blockEquiv (e : B ≃* A) : blockU B ≃* blockU A :=
  (e.subgroupMap (blockU B)).trans (MulEquiv.subgroupCongr (block_map e))
private theorem blockEquiv_conj (e : B ≃* A) (b : B) (x : blockU B) :
    blockEquiv e (blockConjugate B b x) = blockConjugate A (e b) (blockEquiv e x) := by
  apply Subtype.ext
  change e (b * (x : B) * b⁻¹) = e b * e (x : B) * (e b)⁻¹
  simp only [map_mul,map_inv]

private def layerEquiv (c : NaturalCenterDoubleDualQuotient A) (e : B ≃* A) :
    (c.layer.comap e.toMonoidHom) ≃* c.layer where
  toFun x := ⟨e x,x.property⟩
  invFun x := ⟨e.symm x,by simpa only [mem_comap,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)


/-- Transport the full-center quotient with its original component marking. -/
def comap (c : NaturalCenterDoubleDualQuotient A) (e : B ≃* A) : NaturalCenterDoubleDualQuotient B := by
  let := c.normal
  refine {
    marking := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans c.marking
    layer := c.layer.comap e.toMonoidHom
    normal := inferInstance
    center_le := ?_
    projection := c.projection.comp (layerEquiv c e).toMonoidHom
    action := ?_
    kernel_central := ?_
    quotient := c.quotient.comp (blockEquiv e).toMonoidHom
    onto := c.onto.comp (blockEquiv e).surjective
    kernel := ?_
    quotient_action := ?_ }
  · rintro _ ⟨z,hz,rfl⟩
    exact c.center_le (mem_map_of_mem _ ((Subgroup.centerCongr (blockEquiv e)) ⟨z,hz⟩).property)
  · intro b x
    change (c.projection (layerEquiv c e ⟨b * (x : B) * b⁻¹,_⟩)).toAdd = _
    have he := c.action (e b) (layerEquiv c e x)
    convert he using 1
    · apply congrArg (fun z : c.layer => (c.projection z).toAdd)
      apply Subtype.ext
      change e (b * (x : B) * b⁻¹) = e b * e x * (e b)⁻¹
      simp only [map_mul,map_inv]
    · rfl
  · intro x hx
    have hc := c.kernel_central (layerEquiv c e x) hx
    have hz := ((Subgroup.centerCongr e).symm ⟨e x,hc⟩).property
    change e.symm (e x) ∈ center B at hz
    simpa only [e.symm_apply_apply] using hz
  · rw [← MonoidHom.comap_ker,c.kernel]
    ext x
    change blockEquiv e x ∈ center (blockU A) ↔ x ∈ center (blockU B)
    constructor
    · intro hx
      have hh := (centerCongr (blockEquiv e).symm ⟨blockEquiv e x,hx⟩).property
      change (blockEquiv e).symm (blockEquiv e x) ∈ _ at hh
      simpa only [MulEquiv.symm_apply_apply] using hh
    · intro hx
      exact (centerCongr (blockEquiv e) ⟨x,hx⟩).property
  · intro b x
    change (c.quotient (blockEquiv e (blockConjugate B b x))).toAdd = _
    rw [blockEquiv_conj]
    exact c.quotient_action (e b) (blockEquiv e x)

private theorem comap_marking_internal (n : NaturalCenterDoubleDualQuotient A) (e : B ≃* A) :
    (n.comap e).marking = (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans n.marking := rfl

/-- Simultaneous transport preserves the source pair's common marking. -/
theorem same_marking_comap (c : FullCoreDoubleDualCover A)
    (n : NaturalCenterDoubleDualQuotient A) (h : c.marking = n.marking) (e : B ≃* A) :
    (c.comap e).marking = (n.comap e).marking := by
  rw [FullCoreDoubleDualCover.comap_marking,comap_marking_internal]
  rw [h]
end CFSG.Quasithin.ChapterC.BinaryMS.NaturalCenterDoubleDualQuotient
