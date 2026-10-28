module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Geometry.Pencil
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking

/-!
# Recognizing the literal G₂ flag in whole-module coordinates

Pulling back the original plane through an injective module embedding preserves
its order. Its component Sylow remains a genuine derived Sylow under the
surjective actor map, and [V,A]=V becomes equality with the displacement span.
These are the exact inputs to the concrete natural and Weyl line recognizers.
Once the line is recognized, its order-two subgroup is a singular point and
the actual point-fixing normalizer action gives the pencil bound.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
The imported octonion line calculations use the attributed ATLAS models,
LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
open ChapterC Atlas.G2 Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Chapter14.Section07.G2Exclusion.MarkedGeometry
open Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
open Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
open Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

def coordinatePlane (i : Multiplicative W →* G) (V : Subgroup G) : Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm (V.comap i))

theorem coordinatePlane_image (i : Multiplicative W →* G) (V : Subgroup G)
    (hV : V ≤ i.range) : spaceImage i (coordinatePlane i V) = V :=
  Subgroup.map_comap_eq_self hV

theorem coordinatePlane_card (i : Multiplicative W →* G) (hi : Function.Injective i)
    (V : Subgroup G) (hV : V ≤ i.range) : Nat.card (coordinatePlane i V) = Nat.card V := by
  calc
    _ = Nat.card (spaceImage i (coordinatePlane i V)) :=
      (Subgroup.card_map_of_injective hi).symm
    _ = _ := congrArg (fun P : Subgroup G => Nat.card P) (coordinatePlane_image i V hV)

/-- The plane in literal whole-module coordinates retains its Sylow invariance. -/
theorem coordinatePlane_sylow {K V Z J : Subgroup G} (d : FlagData K V Z J)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : Multiplicative W →* G) (k : K →* commutator (Model (ZMod 2)))
    (hk : Function.Surjective k)
    (hact : ∀ (x : K) (w : W), i (Multiplicative.ofAdd (ρ (k x).val w)) =
      x.val * i (Multiplicative.ofAdd w) * x.val⁻¹) :
    ∃ S : Sylow 2 (commutator (Model (ZMod 2))),
      (S : Subgroup (commutator (Model (ZMod 2)))).map
        (commutator (Model (ZMod 2))).subtype ≤ subspaceStabilizer ρ (coordinatePlane i V) := by
  let := d.block.short.finite
  obtain ⟨S,hS,_⟩ := d.sylow
  refine ⟨S.mapSurjective hk, ?_⟩
  apply le_subspaceStabilizer
  rintro _ ⟨_, ⟨x,hx,rfl⟩,rfl⟩ w hw
  change i (Multiplicative.ofAdd (ρ (k x).val w)) ∈ V
  rw [hact]
  exact le_normalizer_iff.mp hS x.val (mem_map_of_mem _ hx) _ hw

/-- Generation by an actual subgroup of K becomes the plane's displacement span. -/
theorem coordinatePlane_commutator {K V Z J : Subgroup G} (d : FlagData K V Z J)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : Multiplicative W →* G) (hi : Function.Injective i) (hV : V ≤ i.range)
    (k : K →* commutator (Model (ZMod 2)))
    (hact : ∀ (x : K) (w : W), i (Multiplicative.ofAdd (ρ (k x).val w)) =
      x.val * i (Multiplicative.ofAdd w) * x.val⁻¹) :
    ∃ X : Subgroup (Model (ZMod 2)),
      subspaceCommutator ρ (coordinatePlane i V) X = coordinatePlane i V := by
  obtain ⟨A,hAK,hA⟩ := d.seed
  let f : A →* Model (ZMod 2) :=
    (commutator (Model (ZMod 2))).subtype.comp (k.comp (Subgroup.inclusion hAK))
  let P := coordinatePlane i V
  let C := subspaceCommutator ρ P f.range
  have hd (x : A) (w : W) :
      i (Multiplicative.ofAdd (ρ (f x) w - w)) =
        x.val * i (Multiplicative.ofAdd w) * x.val⁻¹ * (i (Multiplicative.ofAdd w))⁻¹ := by
    rw [sub_eq_add_neg]
    change i (Multiplicative.ofAdd (ρ (f x) w) * (Multiplicative.ofAdd w)⁻¹) = _
    rw [map_mul,map_inv]
    change i (Multiplicative.ofAdd (ρ (k (Subgroup.inclusion hAK x)).val w)) * _ = _
    rw [hact]
    rfl
  have hCP : C ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨x,rfl⟩,w,hw,rfl⟩
    change i (Multiplicative.ofAdd (ρ (f x) w - w)) ∈ V
    rw [hd, ← hA, commutator_comm]
    exact commutator_mem_commutator x.property hw
  have hVC : V ≤ spaceImage i C := by
    rw [← hA, commutator_comm]
    apply commutator_le.mpr
    intro x hx v hv
    obtain ⟨w,hw,hiv⟩ := (coordinatePlane_image i V hV).symm ▸ hv
    refine ⟨Multiplicative.ofAdd (ρ (f ⟨x,hx⟩) w.toAdd - w.toAdd), ?_, ?_⟩
    · change ρ (f ⟨x,hx⟩) w.toAdd - w.toAdd ∈ C
      exact Submodule.subset_span ⟨f ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩,w.toAdd,hw,rfl⟩
    · rw [hd]
      change x * i w * x⁻¹ * (i w)⁻¹ = _
      rw [hiv]
      rfl
  refine ⟨f.range, le_antisymm hCP ?_⟩
  intro w hw
  obtain ⟨v,hv,he⟩ := hVC hw
  have hvw : v = Multiplicative.ofAdd w := hi he
  change Multiplicative.ofAdd w ∈ C.toAddSubgroup.toSubgroup
  rw [← hvw]
  exact hv

/-- The line marking and the actual ambient action discharge the pencil bound
for the original flag, including its literal point subgroup. -/
theorem flag_card_of_line [Finite G] {K V Z J : Subgroup G} (d : FlagData K V Z J)
    (f : SingularMap W) (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant ρ) (i : Multiplicative W →* G) (hi : Function.Injective i)
    (hV : V ≤ i.range) (L : ZeroProductLine (ZMod 2))
    (hL : f.line L = coordinatePlane i V)
    (hact : ∀ j ∈ J, ∃ g : Model (ZMod 2), ∀ w : W,
      i (Multiplicative.ofAdd (ρ g w)) = j * i (Multiplicative.ofAdd w) * j⁻¹) :
    Nat.card (conjugateSpanBy V J) = 8 := by
  have hZ : Z ≤ i.range := d.point_le.trans hV
  have hc : Nat.card (Z.comap i) = 2 :=
    (coordinatePlane_card i hi Z hZ).trans d.point_card
  obtain ⟨p,hp,hpL⟩ := point_of_card_two_le_line f (MulEquiv.refl (Multiplicative W))
    (Z.comap i) hc L (by
      intro w hw
      change w ∈ (f.line L).toAddSubgroup.toSubgroup.map (MonoidHom.id _)
      rw [Subgroup.map_id,hL]
      exact d.point_le hw)
  change (f.point p).toAddSubgroup.toSubgroup.map (MonoidHom.id _) = Z.comap i at hp
  rw [Subgroup.map_id] at hp
  have hpZ : Z = spaceImage i (f.point p) := by
    rw [spaceImage,hp,Subgroup.map_comap_eq_self hZ]
  have hLV : V = spaceImage i (f.line L) := by
    rw [hL, coordinatePlane_image i V hV]
  exact conjugateSpan_card_of_pencil f ρ hf i hi V J p d.plane_card d.moves
    (conjugateSpan_le_pencil f ρ hf i hi V Z J L p hLV hpZ hpL d.fixes hact)

end CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
