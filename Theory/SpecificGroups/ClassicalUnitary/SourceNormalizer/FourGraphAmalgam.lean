module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# The whole fixed amalgam of a unitary graph involution

The same matrix centralizer isomorphism restricts to the point, flag and
plane stabilizers. It therefore identifies the fixed local diagram with
the native symplectic diagram times the original central graph C₂.
Transport of all three centralizers along an amalgam isomorphism preserves
both commuting squares. Middle conjugation is treated simultaneously,
so a graph involution may subsequently be placed in the original Sylow.

Source: Aschbacher–Smith F.4.37(2–3), printed p.293 of `refs/quasithin.pdf`.
These are native and transport results, not ambient centralizer control.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph

variable {L B R L' B' R' : Type*}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']

@[expose] def centralizerMap {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (x : X) :
    centralizer ({x} : Set X) →* centralizer ({f x} : Set Y) :=
  (f.comp (centralizer ({x} : Set X)).subtype).codRestrict _ (by
    intro y
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MonoidHom.comp_apply, Subgroup.coe_subtype] using congrArg f (mem_centralizer_singleton_iff.mp y.property))

/-- Centralize the same marked middle element in all three groups. -/
@[expose] def centralizerDiagram (α : RankTwoAmalgam L B R) (b : B) :
    RankTwoAmalgam (centralizer ({α.left b} : Set L))
      (centralizer ({b} : Set B)) (centralizer ({α.right b} : Set R)) :=
  ⟨centralizerMap α.left b, centralizerMap α.right b⟩

private def centralizerEquivOf {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (x : X) (y : Y) (he : e x = y) :
    centralizer ({x} : Set X) ≃* centralizer ({y} : Set Y) :=
  { toFun := fun z => ⟨e z, mem_centralizer_singleton_iff.mpr (by
      rw [←he,←map_mul,←map_mul]
      exact congrArg e (mem_centralizer_singleton_iff.mp z.property))⟩
    invFun := fun z => ⟨e.symm z, mem_centralizer_singleton_iff.mpr (by
      apply e.injective
      rw [map_mul,map_mul,e.apply_symm_apply,he]
      exact mem_centralizer_singleton_iff.mp z.property)⟩
    left_inv := fun z => Subtype.ext (e.symm_apply_apply z)
    right_inv := fun z => Subtype.ext (e.apply_symm_apply z)
    map_mul' := fun z w => Subtype.ext (e.map_mul z w) }

@[expose] def centralPoint {X : Type*} [Group X] (x : X) :
    centralizer ({x} : Set X) := ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩

/-- Whole-overlap agreement is preserved on the three element centralizers. -/
def centralizerTransport {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : RankTwoAmalgam.Iso α β) (b : B') :
    RankTwoAmalgam.Iso (centralizerDiagram α (e.middle.symm b)) (centralizerDiagram β b) where
  left := centralizerEquivOf e.left _ _ (by rw [e.left_commutes,e.middle.apply_symm_apply])
  middle := centralizerEquivOf e.middle _ _ (e.middle.apply_symm_apply b)
  right := centralizerEquivOf e.right _ _ (by rw [e.right_commutes,e.middle.apply_symm_apply])
  left_commutes x := by apply Subtype.ext; exact e.left_commutes x.val
  right_commutes x := by apply Subtype.ext; exact e.right_commutes x.val

theorem centralizerTransport_self {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : RankTwoAmalgam.Iso α β) (b : B') :
    (centralizerTransport e b).middle (centralPoint (e.middle.symm b)) = centralPoint b := by
  apply Subtype.ext
  exact e.middle.apply_symm_apply b

/-- Conjugating the middle element conjugates both local centralizers coherently. -/
def centralizerConjugate (α : RankTwoAmalgam L B R) (b c : B) :
    RankTwoAmalgam.Iso (centralizerDiagram α (c*b*c⁻¹)) (centralizerDiagram α b) where
  left := centralizerEquivOf (MulAut.conj ((α.left c)⁻¹)) _ _ (by
    change (α.left c)⁻¹ * α.left (c*b*c⁻¹) * ((α.left c)⁻¹)⁻¹ = α.left b
    simp only [map_mul,map_inv]
    group)
  middle := centralizerEquivOf (MulAut.conj (c⁻¹)) _ _ (by
    simp only [MulAut.conj_apply]; group)
  right := centralizerEquivOf (MulAut.conj ((α.right c)⁻¹)) _ _ (by
    change (α.right c)⁻¹ * α.right (c*b*c⁻¹) * ((α.right c)⁻¹)⁻¹ = α.right b
    simp only [map_mul,map_inv]
    group)
  left_commutes x := by
    apply Subtype.ext
    change (α.left c)⁻¹ * α.left x.val * ((α.left c)⁻¹)⁻¹ = α.left (c⁻¹*x.val*(c⁻¹)⁻¹)
    simp only [map_mul,map_inv]
  right_commutes x := by
    apply Subtype.ext
    change (α.right c)⁻¹ * α.right x.val * ((α.right c)⁻¹)⁻¹ = α.right (c⁻¹*x.val*(c⁻¹)⁻¹)
    simp only [map_mul,map_inv]

theorem centralizerConjugate_self (α : RankTwoAmalgam L B R) (b c : B) :
    (centralizerConjugate α b c).middle (centralPoint (c*b*c⁻¹)) = centralPoint b := by
  apply Subtype.ext
  change c⁻¹*(c*b*c⁻¹)*(c⁻¹)⁻¹ = b
  group

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
open UnitaryFourFlag UnitaryFourOuter
/-- The graph centralizer's native fixed local diagram, with its central graph factor. -/
@[expose] def productDiagram :
    RankTwoAmalgam ((SymplecticFour.pointParabolic (F := K)) × C2)
      ((SymplecticFour.borel (F := K)) × C2) ((SymplecticFour.planeParabolic (F := K)) × C2) :=
  ⟨(inclusion (inf_le_left : SymplecticFour.borel (F := K) ≤ SymplecticFour.pointParabolic)).prodMap (MonoidHom.id C2),
    (inclusion (inf_le_right : SymplecticFour.borel (F := K) ≤ SymplecticFour.planeParabolic)).prodMap (MonoidHom.id C2)⟩

@[expose] def matrixDiagram := RankTwoAmalgam.ofSubgroups
  (point F σ hσ) (overlap F σ hσ) (plane F σ hσ) inf_le_left inf_le_right

@[expose] def graphElement : overlap F σ hσ := ⟨sigma F σ hσ,sigma_mem_overlap F σ hσ⟩

private def localHom (P : Subgroup (Extension F σ hσ))
    (Q : Subgroup (SymplecticFour.Sp K)) (hf : sigma F σ hσ ∈ P)
    (hmem : ∀ x, centralizerHom F σ hσ x ∈ P ↔ x.1 ∈ Q) :
    Q × C2 →* centralizer ({⟨sigma F σ hσ,hf⟩} : Set P) :=
  let f : Q × C2 →* P :=
    ((centralizerHom F σ hσ).comp (Q.subtype.prodMap (MonoidHom.id C2))).codRestrict P
      (fun x => (hmem (x.1.val,x.2)).mpr x.1.property)
  f.codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hx := (centralizerEquiv F σ hσ (x.1.val,x.2)).property
    rw [centralizerEquiv_coe] at hx
    exact mem_centralizer_singleton_iff.mp hx)

private def localEquiv (P : Subgroup (Extension F σ hσ))
    (Q : Subgroup (SymplecticFour.Sp K)) (hf : sigma F σ hσ ∈ P)
    (hmem : ∀ x, centralizerHom F σ hσ x ∈ P ↔ x.1 ∈ Q) :
    Q × C2 ≃* centralizer ({⟨sigma F σ hσ,hf⟩} : Set P) :=
  MulEquiv.ofBijective (localHom F σ hσ P Q hf hmem) ⟨by
    intro x y h
    have hh := centralizerHom_injective F σ hσ
      (congrArg (fun x : centralizer ({⟨sigma F σ hσ,hf⟩} : Set P) => x.val.val) h)
    change (x.1.val,x.2) = (y.1.val,y.2) at hh
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun z : SymplecticFour.Sp K × C2 => z.2) hh), by
    intro x
    have hx : x.val.val ∈ centralizer ({sigma F σ hσ} : Set (Extension F σ hσ)) := by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)
    obtain ⟨y,hy⟩ := (centralizerEquiv F σ hσ).surjective ⟨x.val.val,hx⟩
    have he : centralizerHom F σ hσ y = x.val.val :=
      (centralizerEquiv_coe F σ hσ y).symm.trans (congrArg Subtype.val hy)
    refine ⟨(⟨y.1,(hmem y).mp (he.symm ▸ x.val.property)⟩,y.2),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact he⟩

/-- The graph fixed endpoint isomorphisms agree on the entire fixed overlap. -/
def graphDiagramIso : RankTwoAmalgam.Iso (productDiagram F σ)
    (centralizerDiagram (matrixDiagram F σ hσ) (graphElement F σ hσ)) where
  left := localEquiv F σ hσ _ _ (sigma_mem_overlap F σ hσ).1
    (centralizerHom_mem_point F σ hσ)
  middle := localEquiv F σ hσ _ _ (sigma_mem_overlap F σ hσ)
    (fun x => and_congr (centralizerHom_mem_point F σ hσ x)
      (centralizerHom_mem_plane F σ hσ x))
  right := localEquiv F σ hσ _ _ (sigma_mem_overlap F σ hσ).2
    (centralizerHom_mem_plane F σ hσ)
  left_commutes x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_commutes x := by apply Subtype.ext; apply Subtype.ext; rfl

/-- The central factor is the original marked graph element, so quotienting
by that element retains its literal kernel. -/
theorem graphDiagramIso_graph :
    (graphDiagramIso F σ hσ).middle (1,UnitaryFourOuter.generator) =
      centralPoint (graphElement F σ hσ) := by
  apply Subtype.ext
  apply Subtype.ext
  change centralizerHom F σ hσ (1,UnitaryFourOuter.generator) = sigma F σ hσ
  apply SemidirectProduct.ext
  · rw [centralizerHom_left,map_one]
    rfl
  · rw [centralizerHom_right]
    rfl

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
