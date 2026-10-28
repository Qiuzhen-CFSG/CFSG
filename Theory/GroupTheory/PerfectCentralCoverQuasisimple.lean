module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.Covering

/-!
# Perfect central covers of quasisimple groups

A perfect central cover of a quasisimple group is quasisimple: uniqueness of
maps out of a perfect group shows that the preimage of the center is central,
so the two groups have isomorphic quotients by their centers. This identifies
the universal perfect central cover with the existing quasisimple covering API.

This is the central-extension argument underlying A1 33.4--33.6 and the
covering formalism in `Theory.GroupTheory.Covering`.
-/

namespace PerfectCentralCovering

public section

open Theory.GroupTheory

universe u v w

variable {L : Type u} {G : Type v} [Group L] [Group G]

/-- The preimage of the center under a perfect central cover is the center. -/
theorem Cover.comap_center (f : Cover L G) :
    (Subgroup.center G).comap f.toMonoidHom = Subgroup.center L := by
  let := f.isPerfect
  apply le_antisymm
  · intro x hx
    have heq : (MulAut.conj x).toMonoidHom = MonoidHom.id L := by
      apply monoidHom_eq_of_isPerfect_of_comp_eq f.toMonoidHom f.ker_le_center
      ext y
      change f.toMonoidHom (x * y * x⁻¹) = f.toMonoidHom y
      rw [map_mul, map_mul, map_inv]
      rw [← Subgroup.mem_center_iff.mp hx (f.toMonoidHom y)]
      simp [mul_assoc]
    rw [Subgroup.mem_center_iff]
    intro y
    have h := DFunLike.congr_fun heq y
    change x * y * x⁻¹ = y at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro x hx
    change f.toMonoidHom x ∈ Subgroup.center G
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := f.surjective y
    exact (map_mul f.toMonoidHom y x).symm.trans
      ((congrArg f.toMonoidHom (Subgroup.mem_center_iff.mp hx y)).trans
        (map_mul f.toMonoidHom x y))

/-- Perfect central covers preserve the quotient by the center. -/
@[expose] noncomputable def Cover.quotientCenterEquiv (f : Cover L G) :
    L ⧸ Subgroup.center L ≃* G ⧸ Subgroup.center G := by
  let q := (QuotientGroup.mk' (Subgroup.center G)).comp f.toMonoidHom
  have hker : q.ker = Subgroup.center L := by
    change ((QuotientGroup.mk' (Subgroup.center G)).comp f.toMonoidHom).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_center
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp f.surjective))

/-- A perfect central cover of a quasisimple group is quasisimple. -/
theorem Cover.isQuasisimple [IsQuasisimple G] (f : Cover L G) : IsQuasisimple L where
  toIsPerfect := f.isPerfect
  simple := by
    let : IsSimpleGroup (G ⧸ Subgroup.center G) := IsQuasisimple.simple
    exact f.quotientCenterEquiv.isSimpleGroup

/-- Regard a quasisimple covering as a perfect central cover. -/
@[expose] def ofCovering [Finite L] [Finite G] [IsQuasisimple L] [IsQuasisimple G]
    (f : Covering L G) : Cover L G where
  toMonoidHom := f.toMonoidHom
  surjective := f.surjective
  isPerfect := inferInstance
  ker_le_center := f.ker_le_center

/-- Regard a perfect central cover between finite quasisimple groups as a covering. -/
@[expose] def Cover.toCovering [Finite L] [Finite G] [IsQuasisimple L] [IsQuasisimple G]
    (f : Cover L G) : Covering L G where
  toMonoidHom := f.toMonoidHom
  surjective := f.surjective

/-- Universality for perfect central covers implies quasisimple universality,
with the same arbitrary target universe. -/
theorem IsUniversal.toCovering [Finite L] [Finite G]
    [IsQuasisimple L] [IsQuasisimple G] (f : Cover L G)
    (hf : IsUniversal.{u, v, w} f) :
    Covering.IsUniversal.{v, u, w} f.toCovering := by
  intro M _ _ _ g
  obtain ⟨h, hh, huniq⟩ := hf M (ofCovering g)
  have hsurj : Function.Surjective h := by
    apply surjective_of_comp_surjective_of_ker_le_center_of_isPerfect g.toMonoidHom h
    · rw [show g.toMonoidHom.comp h = f.toMonoidHom from hh]
      exact f.surjective
    · exact g.ker_le_center
  let h' : Covering L M := { toMonoidHom := h, surjective := hsurj }
  refine ⟨h', ?_, ?_⟩
  · apply Covering.ext
    intro x
    exact DFunLike.congr_fun hh x
  · intro k hk
    have hk' : g.toMonoidHom.comp k.toMonoidHom = f.toMonoidHom :=
      congrArg Covering.toMonoidHom hk
    have heq := huniq k.toMonoidHom hk'
    apply Covering.ext
    intro x
    exact DFunLike.congr_fun heq x

variable (G)

instance universalGroup_isQuasisimple [IsQuasisimple G] :
    IsQuasisimple (UniversalGroup G) := (universalCover G).isQuasisimple

/-- The constructed universal cover, packaged in the quasisimple covering API. -/
@[expose] def universalQuasisimpleCover [Finite G] [IsQuasisimple G] :
    Covering (UniversalGroup G) G := (universalCover G).toCovering

/-- The concrete quasisimple covering has the existing API's universal property. -/
theorem universalQuasisimpleCover_isUniversal [Finite G] [IsQuasisimple G] :
    Covering.IsUniversal.{v, v, w} (universalQuasisimpleCover G) :=
  IsUniversal.toCovering (universalCover G) universalCover_isUniversal

end
end PerfectCentralCovering
