module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Basic
public import Theory.Representation.PSL3Two.ParabolicCyclic

/-!
# The original plane inside S/V

The original fixed-kernel calculation identifies the image of U in S/V as a
binary plane when U₀ = V₁. This is the literal quotient image, with membership
and kernel formulas on representatives. Its L-conjugates generate S/V because
S was defined as the conjugate span of U. The point-parabolic action preserves
this plane. These facts prepare the cyclic seed in the application of H.6.5;
they do not yet prove its local irreducibility or choose a point/line marking.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
and H.6.5, printed p.388 (PDF p.399), manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- The image of U in the literal S/V quotient. -/
def plane : Submodule (ZMod 2) (Additive (S F L ⧸ V.subgroupOf (S F L))) :=
  AddSubgroup.toZModSubmodule 2
    (((F.U).subgroupOf (S F L)).map quotientCoordinates).toAddSubgroup'

omit [Finite G] in
/-- Every plane vector retains an actual U-representative. -/
theorem mem_plane_iff (v : Additive (S F L ⧸ V.subgroupOf (S F L))) :
    v ∈ plane (F := F) (L := L) (V := V) ↔
      ∃ s : S F L, (s : G) ∈ F.U ∧ (quotientCoordinates s).toAdd = v := by
  change Multiplicative.ofAdd v ∈ ((F.U).subgroupOf (S F L)).map quotientCoordinates ↔ _
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, congrArg Multiplicative.toAdd he⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, Multiplicative.toAdd.injective he⟩

omit [Finite G] in
/-- Every U-element maps to the literal quotient plane. -/
theorem coordinates_mem_plane (s : S F L) (hs : (s : G) ∈ F.U) :
    (quotientCoordinates s).toAdd ∈ plane (F := F) (L := L) (V := V) :=
  (mem_plane_iff _).mpr ⟨s, hs, rfl⟩

variable (d : Data T L V F W)

/-- In the permitted U₀ = V₁ branch, the actual quotient image has four elements. -/
theorem card_plane (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) :
    Nat.card (plane (F := F) (L := L) (V := V)) = 4 := by
  change Nat.card (((F.U).subgroupOf (S F L)).map quotientCoordinates) = 4
  rw [← relIndex_ker, quotientCoordinates_ker, relIndex_subgroupOf U_le_S]
  have h := CriticalIntersections.fixed_product_index d hs
  rwa [hU₀, sup_eq_right.mpr (F.le_seed 1)] at h

/-- The plane dimension is derived from the original projection and fixed kernel. -/
theorem finrank_plane (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) :
    Module.finrank (ZMod 2) (plane (F := F) (L := L) (V := V)) = 2 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := plane (F := F) (L := L) (V := V))
  rw [Nat.card_zmod, card_plane d hs hU₀] at h
  exact h.symm

/-- The full original point parabolic preserves the literal plane. -/
theorem plane_stable (a : QuotientAction d) (l : L) (hl : (l : G) ∈ F.H)
    (v : Additive (S F L ⧸ V.subgroupOf (S F L)))
    (hv : v ∈ plane (F := F) (L := L) (V := V)) :
    a.representation (d.qL l) v ∈ plane (F := F) (L := L) (V := V) := by
  obtain ⟨s, hs, rfl⟩ := (mem_plane_iff v).mp hv
  rw [← a.equivariant]
  apply coordinates_mem_plane
  exact (mem_normalizer_iff.mp (d.conjugationSection.normalized hl) s).mp hs

/-- Any L-invariant subspace containing this plane is the whole S/V. -/
theorem eq_top_of_plane_le (a : QuotientAction d)
    (A : Submodule (ZMod 2) (Additive (S F L ⧸ V.subgroupOf (S F L))))
    (hA : plane (F := F) (L := L) (V := V) ≤ A)
    (hstable : ∀ g v, v ∈ A → a.representation g v ∈ A) : A = ⊤ := by
  let B : Subgroup (S F L) := A.toAddSubgroup.toSubgroup.comap quotientCoordinates
  have hSB : S F L ≤ B.map (S F L).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨l, hl, u, hu, rfl⟩
    let s : S F L := ⟨u, U_le_S hu⟩
    let c : S F L := ⟨l * u * l⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_S hl) u).mp s.property⟩
    refine ⟨c, ?_, rfl⟩
    change (quotientCoordinates c).toAdd ∈ A
    rw [a.equivariant ⟨l, hl⟩ s]
    exact hstable _ _ (hA (coordinates_mem_plane s hu))
  apply top_unique
  intro v _
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective (V.subgroupOf (S F L)) v.toMul
  obtain ⟨b, hb, he⟩ := hSB s.property
  have hbs : b = s := Subtype.ext he
  subst b
  change (quotientCoordinates s).toAdd ∈ A at hb
  exact (show (quotientCoordinates s).toAdd = v from hs) ▸ hb

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
