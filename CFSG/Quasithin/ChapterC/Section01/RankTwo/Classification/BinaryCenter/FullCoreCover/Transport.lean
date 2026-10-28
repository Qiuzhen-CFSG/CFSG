module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover

/-!
# Transport of the full nonabelian binary cover

A group isomorphism carries the two-core, its commutator and derived subgroup
to the corresponding intrinsic groups. Pull back the original center section,
its fixed kernel, and the full-cover projection through these literal maps.
Both the natural derived action and doubled-dual cover retain one quotient
marking. This changes only the carrier of the MS output used in15.3.31.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.FullCoreDoubleDualCover
universe u
variable {A B : Type u} [Group A] [Group B]

private theorem block_map (e : B ≃* A) : (blockU B).map e.toMonoidHom = blockU A := by
  rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
private def blockEquiv (e : B ≃* A) : blockU B ≃* blockU A :=
  (e.subgroupMap (blockU B)).trans (MulEquiv.subgroupCongr (block_map e))
private theorem derived_map (e : B ≃* A) :
    (_root_.commutator (blockU B)).map (blockEquiv e).toMonoidHom =
      _root_.commutator (blockU A) := by
  rw [map_commutator_eq,MonoidHom.range_eq_top.mpr (blockEquiv e).surjective,
    ← _root_.commutator_def]
private def derivedEquivMap (e : B ≃* A) :
    _root_.commutator (blockU B) ≃* _root_.commutator (blockU A) :=
  ((blockEquiv e).subgroupMap _).trans (MulEquiv.subgroupCongr (derived_map e))
private theorem blockEquiv_conj (e : B ≃* A) (b : B) (x : blockU B) :
    blockEquiv e (blockConjugate B b x) = blockConjugate A (e b) (blockEquiv e x) := by
  apply Subtype.ext
  change e (b * (x : B) * b⁻¹) = e b * e (x : B) * (e b)⁻¹
  simp only [map_mul,map_inv]

private def layerEquiv (c : FullCoreDoubleDualCover A) (e : B ≃* A) :
    (c.layer.comap e.toMonoidHom) ≃* c.layer where
  toFun x := ⟨e x,x.property⟩
  invFun x := ⟨e.symm x,by simpa only [mem_comap,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- Pull the genuine full-cover data back along the actual component isomorphism. -/
def comap (c : FullCoreDoubleDualCover A) (e : B ≃* A) : FullCoreDoubleDualCover B := by
  let := c.normal
  refine {
    marking := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans c.marking
    layer := c.layer.comap e.toMonoidHom
    normal := inferInstance
    center_le := ?_
    projection := c.projection.comp (layerEquiv c e).toMonoidHom
    action := ?_
    kernel_central := ?_
    Space := c.Space
    representation := c.representation
    coreProjection := c.coreProjection.comp (blockEquiv e).toMonoidHom
    coreOnto := c.coreOnto.comp (blockEquiv e).surjective
    coreKernel := ?_
    coreAction := ?_
    cover := c.cover
    isCover := c.isCover
    derivedEquiv := (derivedEquivMap e).trans c.derivedEquiv
    derivedAction := ?_ }
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
  · rw [← MonoidHom.comap_ker,c.coreKernel]
    apply map_injective (f := (blockEquiv e).toMonoidHom) (blockEquiv e).injective
    rw [map_comap_eq_self_of_surjective (blockEquiv e).surjective,derived_map]
  · intro b x
    change (c.coreProjection (blockEquiv e (blockConjugate B b x))).toAdd = _
    rw [blockEquiv_conj]
    exact c.coreAction (e b) (blockEquiv e x)
  · intro b x y hy
    apply c.derivedAction (e b) (derivedEquivMap e x) (derivedEquivMap e y)
    change blockEquiv e (y : blockU B) = blockConjugate A (e b) (blockEquiv e (x : blockU B))
    rw [hy,blockEquiv_conj]

private theorem comap_marking_internal (c : FullCoreDoubleDualCover A) (e : B ≃* A) :
    (c.comap e).marking = (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans c.marking := rfl

/-- The pulled-back cover retains the quotient marking induced by the given isomorphism. -/
theorem comap_marking (c : FullCoreDoubleDualCover A) (e : B ≃* A) :
    (c.comap e).marking = (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans c.marking :=
  comap_marking_internal c e

end CFSG.Quasithin.ChapterC.BinaryMS.FullCoreDoubleDualCover
