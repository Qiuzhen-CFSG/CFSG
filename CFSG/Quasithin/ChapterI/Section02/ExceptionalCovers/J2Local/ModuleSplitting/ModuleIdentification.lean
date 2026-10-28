module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.ModuleSplitting.ElementaryQuotient
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.Restriction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalModule

/-!
# The actual projective module in the local J₂ double cover

Restriction to the two-core, followed by the checked augmentation coordinates
of the literal Hall--Janko radical, gives a surjective equivariant map with
kernel precisely the distinguished square subgroup joined with the covering
center. Thus the source module is identified using the original quotient and
its five-block A₅ action. The independent splitting argument consumes this map.

Source: Aschbacher--Smith I.2.2(5), printed pp.411--412 / PDF pp.422--423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
open Sporadic.LeechRelated.J2
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.FirstParabolic
variable {K : Type*} [Group K] [Finite K]
variable (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)

/-- Restriction of the original central quotient to the two-core. -/
noncomputable def coreRestriction : pCore 2 (preimage e) →* pCore 2 l₁ :=
  ((restriction e).comp (pCore 2 (preimage e)).subtype).codRestrict _ (fun x => by
    change restriction e x.val ∈ pCore 2 l₁
    have h := x.property
    exact (le_of_eq (core_preimage e hZ).symm) h)

theorem coreRestriction_surjective : Function.Surjective (coreRestriction e hZ) := by
  intro y
  obtain ⟨x, hx⟩ := restriction_surjective e y.val
  have hm : x ∈ pCore 2 (preimage e) := by
    rw [← core_preimage e hZ]
    change restriction e x ∈ pCore 2 l₁
    rw [hx]
    exact y.property
  exact ⟨⟨x, hm⟩, Subtype.ext hx⟩

theorem coreRestriction_conjugation (h : preimage e) (x : pCore 2 (preimage e)) :
    coreRestriction e hZ (MulAut.conjNormal h x) =
      MulAut.conjNormal (restriction e h) (coreRestriction e hZ x) := by
  apply Subtype.ext
  change restriction e (h * x.val * h⁻¹) =
    restriction e h * restriction e x.val * (restriction e h)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- The concrete augmentation coordinates of the covering radical. -/
noncomputable def coreModuleMap :
    pCore 2 (preimage e) →* Multiplicative (BinaryPermutation.core (Fin 5)) :=
  RadicalModule.b.comp (coreRestriction e hZ)

theorem coreModuleMap_surjective : Function.Surjective (coreModuleMap e hZ) :=
  RadicalModule.b_surjective.comp (coreRestriction_surjective e hZ)

theorem coreModuleMap_equivariant (h : preimage e) (x : pCore 2 (preimage e)) :
    (coreModuleMap e hZ (MulAut.conjNormal h x)).toAdd =
      BinaryPermutation.alternatingCoreRepresentation (Fin 5) (a5Action e h)
        (coreModuleMap e hZ x).toAdd := by
  change (RadicalModule.b (coreRestriction e hZ (MulAut.conjNormal h x))).toAdd = _
  rw [coreRestriction_conjugation]
  exact RadicalModule.b_equivariant (restriction e h) (coreRestriction e hZ x)

variable [Group.IsPerfect (preimage e)]
variable (hex : ∃ r ∈ pCore 2 l₁, r ^ 2 = marked)
variable (horbit : ∀ r ∈ pCore 2 l₁, ∀ s ∈ pCore 2 l₁,
  r ^ 2 = marked → s ^ 2 = marked → IsConj r s)

/-- The preimage of the marked central line is the square line joined with
exactly the original covering center. -/
theorem markedLine_preimage :
    (zpowers marked).comap (restriction e) =
      squareSubgroup e hZ hex horbit ⊔ (center K).subgroupOf (preimage e) := by
  have hm : (squareSubgroup e hZ hex horbit).map (restriction e) = zpowers marked := by
    rw [squareSubgroup, MonoidHom.map_zpowers,
      (distinguishedSquare_spec e hZ hex horbit).2.1]
  rw [← hm, comap_map_eq, restriction_ker]

/-- Exact kernel of the map consumed by the projective splitting argument. -/
theorem coreModuleMap_ker :
    (coreModuleMap e hZ).ker =
      (squareSubgroup e hZ hex horbit ⊔ (center K).subgroupOf (preimage e)).subgroupOf
        (pCore 2 (preimage e)) := by
  ext x
  change coreRestriction e hZ x ∈ RadicalModule.b.ker ↔ _
  rw [RadicalModule.b_ker]
  change restriction e x.val ∈ zpowers marked ↔ _
  change x.val ∈ (zpowers marked).comap (restriction e) ↔ _
  rw [markedLine_preimage e hZ hex horbit]
  rfl

/-- The source's literal map, its kernel and its specified conjugation action. -/
theorem coreModuleMap_spec :
    Function.Surjective (coreModuleMap e hZ) ∧
    (coreModuleMap e hZ).ker =
      (squareSubgroup e hZ hex horbit ⊔ (center K).subgroupOf (preimage e)).subgroupOf
        (pCore 2 (preimage e)) ∧
    ∀ (h : preimage e) (x : pCore 2 (preimage e)),
      (coreModuleMap e hZ (MulAut.conjNormal h x)).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) (a5Action e h)
          (coreModuleMap e hZ x).toAdd :=
  ⟨coreModuleMap_surjective e hZ, coreModuleMap_ker e hZ hex horbit,
    coreModuleMap_equivariant e hZ⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
