module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeFrattiniGeometry
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFrattiniIntersection
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFrattiniGeometry

/-!
# The original M22 normal closure has four-dimensional confinement

The selected pair's normal closure E intersects the literal B/U in exactly
[B/U,R]. In source case I the existing two-core commutator bound consequently
confines all V-displacements of E to this surviving moved four-space.
This gives the original group containment needed before selecting the active
chief section's natural projection.

Source: Aschbacher--Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MonoidAlgebra
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction
  Normalizer.SmallOvergroups Normalizer.ParabolicReduction.RankSieve
open MathieuCode.NormalizedShadowRows.M22CodeSection
set_option backward.isDefEq.respectTransparency false

variable {G : Type*} [Group G] [Finite G]

/-- The seed-generated two-group meets the literal original five-space in
exactly its moved four-space. The nonsplit fifth dimension cannot enter E. -/
theorem selected_m22_normalClosure_intersection
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 U]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hTH : (T : Subgroup G) ≤ H)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (I.pCoreIn 2 : Set G))
    (hPH : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hHU : H ≤ normalizer (U : Set G))
    {f : R →* MathieuCode.M22Quintet.Q}
    (hs : M22FiveSection R (V ⊓ I.pCoreIn 2) U f) :
    let J := SmallRows.localImage U (R ⊔ H)
    let B := SmallRows.localImage U (V ⊓ I.pCoreIn 2)
    let D := SmallRows.localImage U R
    let W := ⁅B.subgroupOf J,D.subgroupOf J⁆
    normalClosure (W : Set J) ⊓ B.subgroupOf J = W := by
  obtain ⟨hE,hRB,hRU,hBU,hEl,σ,hσ,j,a,hji,hjr,har,hjq,haq,hja,hg⟩ :=
    selected_m22_normalClosure_geometry s hTH hTV hHR hRP hPH hHU hs
  let := hBU
  let := hEl
  let B₀ := V ⊓ I.pCoreIn 2
  let J := SmallRows.localImage U (R ⊔ H)
  let B := SmallRows.localImage U B₀
  let D := SmallRows.localImage U R
  let W := ⁅B.subgroupOf J,D.subgroupOf J⁆
  have hjσ (r : R) (x : B₀ ⧸ U.subgroupOf B₀) :
      j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹ := by
    rw [hσ]
    exact hja r x
  have hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W := by
    rw [moved_image_commutator σ j a hjσ,hjr,har]
  obtain ⟨_,_,_,hphi⟩ := selected_m22_moved_normalClosure s hTH hTV hHR hRP hPH hHU hs
  obtain ⟨_,_,_,_,hd⟩ := m22_chief_four_space f hs
    (W := Additive (B₀ ⧸ U.subgroupOf B₀))
  obtain ⟨hd5,hd4,_⟩ := hd σ (LinearEquiv.refl (ZMod 2) _) (fun x w => hσ x w.toMul)
  obtain ⟨_,_,_,r,eB,hrs,_,_,hact,_⟩ := hs
  let e : Additive (B₀ ⧸ U.subgroupOf B₀) ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K :=
    LinearEquiv.ofBijective (eB.toAdditive.toAddMonoidHom.toZModLinearMap 2) eB.bijective
  have he (r' : R) (v : Additive (B₀ ⧸ U.subgroupOf B₀)) :
      e (σ r' v) = MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r r') (e v) :=
    (congrArg (fun w => Additive.ofMul (eB w.toMul)) (hσ r' v.toMul)).trans (hact r' v.toMul)
  have hi := normalClosure_intersection σ hd5 hd4 r hrs e he j a hjσ W hW hE hphi hg
  rw [hjr] at hi
  exact hi

/-- In source case I, every V-displacement of the seed-generated two-group
is confined to the surviving four-space, rather than the whole quintet. -/
theorem selected_m22_normalClosure_displacement
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 U]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (I.pCoreIn 2 : Set G))
    (hPH : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hHU : H ≤ normalizer (U : Set G))
    (hinter : V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2)
    {f : R →* MathieuCode.M22Quintet.Q}
    (hs : M22FiveSection R (V ⊓ I.pCoreIn 2) U f) :
    let J := SmallRows.localImage U (R ⊔ H)
    let B := SmallRows.localImage U (V ⊓ I.pCoreIn 2)
    let D := SmallRows.localImage U R
    let W := ⁅B.subgroupOf J,D.subgroupOf J⁆
    let E := normalClosure (W : Set J)
    ⁅E,(SmallRows.localImage U V).subgroupOf J⁆ ≤ W := by
  let J := SmallRows.localImage U (R ⊔ H)
  let B := SmallRows.localImage U (V ⊓ I.pCoreIn 2)
  let D := SmallRows.localImage U R
  let W := ⁅B.subgroupOf J,D.subgroupOf J⁆
  let E := normalClosure (W : Set J)
  let Vq := SmallRows.localImage U V
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hVH : V ≤ H := (s.generate ▸ le_sup_left).trans s.family.le_ambient
  have hVJ : Vq ≤ J := map_mono (subgroupOf_mono _ (hVH.trans le_sup_right))
  obtain ⟨hEcore,_,_,_⟩ := selected_m22_moved_normalClosure
    s hTH hTV hHR hRP hPH hHU hs
  have hconf := (selected_one_hstar_core_displacement s hH hTV hHU
    hs.choose_spec.choose hinter).2.2
  have hmap : (⁅E,Vq.subgroupOf J⁆).map J.subtype ≤ B := by
    rw [map_commutator,map_subgroupOf_eq_of_le hVJ]
    exact (commutator_mono (map_mono hEcore) le_rfl).trans hconf
  have hcB : ⁅E,Vq.subgroupOf J⁆ ≤ B.subgroupOf J := by
    intro x hx
    exact hmap (mem_map_of_mem J.subtype hx)
  have hcE : ⁅E,Vq.subgroupOf J⁆ ≤ E := commutator_le_left _ _
  have hI := selected_m22_normalClosure_intersection s hTH hTV hHR hRP hPH hHU hs
  exact (le_inf hcE hcB).trans hI.le

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
