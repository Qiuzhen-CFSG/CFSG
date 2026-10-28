module
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SolvableResidual

/-!
# Central covers above a core commutator

If a perfect group acts through a quotient with kernel O₂(X), quotienting
by a normal subgroup containing [O₂(X),X] produces a perfect central cover.
The construction retains the original homomorphism and its exact kernel.
A separate transport lemma pulls full core commutator generation back through
any surjection with a two-group kernel.

The Hermitian source application uses W = V in Aschbacher–Smith 8.2.10(3),
printed p.721, before eliminating the remaining central kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CoreCommutatorCover
variable {X Y : Type*} [Group X] [Group Y]
  (W : Subgroup X) [W.Normal]
  (f : X →* Y) (hf : Function.Surjective f)
  (hW : W ≤ pCore 2 X) (hk : f.ker = pCore 2 X)
  (hcomm : ⁅pCore 2 X,(⊤ : Subgroup X)⁆ ≤ W)

/-- Factor the original map through the specified normal module. -/
@[expose] def projection : X ⧸ W →* Y := QuotientGroup.lift W f (hW.trans hk.ge)

/-- The factored map agrees on every original representative. -/
theorem projection_mk (x : X) : projection W f hW hk (QuotientGroup.mk' W x) = f x := rfl

include hf in
/-- Surjectivity is preserved by the factorization. -/
theorem projection_surjective : Function.Surjective (projection W f hW hk) :=
  QuotientGroup.lift_surjective_of_surjective W f hf _

/-- The kernel is the full original two-core image. -/
theorem projection_ker : (projection W f hW hk).ker =
    (pCore 2 X).map (QuotientGroup.mk' W) := by
  rw [projection,QuotientGroup.ker_lift,hk]

include hcomm in
/-- The core commutator containment centralizes the quotient kernel. -/
theorem projection_central : (projection W f hW hk).ker ≤ center (X ⧸ W) := by
  rw [projection_ker]
  rintro _ ⟨x,hx,rfl⟩
  apply mem_center_iff.mpr
  intro y
  induction y using QuotientGroup.induction_on with
  | H y =>
    symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅(QuotientGroup.mk' W) x,(QuotientGroup.mk' W) y⁆ = 1
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr
      (hcomm (commutator_mem_commutator hx (mem_top y)))

variable [Group.IsPerfect X]
/-- The actual perfect central covering, with its original projection. -/
def cover : PerfectCentralCovering.Cover (X ⧸ W) Y where
  toMonoidHom := projection W f hW hk
  surjective := projection_surjective W f hf hW hk
  isPerfect := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective W)
  ker_le_center := projection_central W f hW hk hcomm

/-- The covering uses the specified factored homomorphism. -/
theorem cover_toMonoidHom : (cover W f hf hW hk hcomm).toMonoidHom =
    projection W f hW hk := by rfl

variable [Finite X] [Finite Y]
include hf hW hk hcomm in
/-- Over a simple quasisimple target the full center is the two-core image. -/
theorem center_eq_core_image [IsQuasisimple Y] [IsSimpleGroup Y] :
    center (X ⧸ W) = (pCore 2 X).map (QuotientGroup.mk' W) := by
  let c := cover W f hf hW hk hcomm
  let : IsQuasisimple (X ⧸ W) := c.isQuasisimple
  exact c.toCovering.ker_eq_center_of_isSimple.symm.trans (projection_ker W f hW hk)

end CoreCommutatorCover

namespace MonoidHom
variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
/-- Full core movement lifts modulo exactly the original kernel. -/
theorem core_commutator_sup_kernel (f : X →* Y) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker)
    (hcomm : ⁅pCore 2 Y,(⊤ : Subgroup Y)⁆ = pCore 2 Y) :
    ⁅pCore 2 X,(⊤ : Subgroup X)⁆ ⊔ f.ker = pCore 2 X := by
  have hm : (pCore 2 X).map f = pCore 2 Y := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self_of_surjective hf]
  have he : (⁅pCore 2 X,(⊤ : Subgroup X)⁆).map f = (pCore 2 X).map f := by
    rw [map_commutator,hm,←MonoidHom.range_eq_map,f.range_eq_top_of_surjective hf,hcomm]
  have hh := congrArg (Subgroup.comap f) he
  rw [comap_map_eq,comap_map_eq,sup_of_le_left (show f.ker ≤ pCore 2 X from
    le_sSup ⟨inferInstance,hk⟩)] at hh
  exact hh

/-- Pull full core generation back through the actual solvable residual. -/
theorem residual_core_commutator_sup_kernel (f : X →* Y) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) [Group.IsPerfect Y]
    (hcomm : ⁅pCore 2 Y,(⊤ : Subgroup Y)⁆ = pCore 2 Y) :
    ⁅(solvableResidual X).pCoreIn 2,solvableResidual X⁆ ⊔ f.ker = pCore 2 X := by
  let R := solvableResidual X
  let g := f.comp R.subtype
  have hg : Function.Surjective g := by
    have hh : R.map f=⊤ := (map_solvableResidual_eq f hf).trans solvableResidual_eq_top
    intro y
    obtain ⟨x,hx,hxy⟩ := hh.symm ▸ mem_top y
    exact ⟨⟨x,hx⟩,hxy⟩
  have hgk : IsPGroup 2 g.ker := hk.comap_of_injective R.subtype R.subtype_injective
  have hm : (pCore 2 X).map f=pCore 2 Y := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self_of_surjective hf]
  have hmg : (pCore 2 R).map g=pCore 2 Y := by
    rw [←g.comap_pCore_of_ker_isPGroup hg hgk,map_comap_eq_self_of_surjective hg]
  have he : ((⁅pCore 2 R,(⊤ : Subgroup R)⁆).map R.subtype).map f =
      (pCore 2 X).map f := by
    rw [map_map,map_commutator,hmg,←MonoidHom.range_eq_map,g.range_eq_top_of_surjective hg,hm]
    exact hcomm
  have hh := congrArg (Subgroup.comap f) he
  rw [comap_map_eq,comap_map_eq,sup_of_le_left (show f.ker ≤ pCore 2 X from
    le_sSup ⟨inferInstance,hk⟩)] at hh
  rw [map_commutator,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh
end MonoidHom
