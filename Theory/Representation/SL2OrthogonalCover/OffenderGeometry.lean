module

public import Theory.Representation.BinaryOffender.GeneratedLayerQuotient
public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.Representation.SL2OrthogonalCover.Sylow
public import Theory.Representation.SL2NaturalOffenders.PairPointwiseFixer
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Offenders on generated natural SL₂ covers

The fixed-space quotient of a faithful generated cover is faithful. Natural
SL₂ offender recognition therefore identifies a genuine ambient offender
with the Sylow intersection in the normal layer. Over the field of order
four, full-cover Sylow geometry identifies fixed and moved spaces. Hence
that offender moves every vector fixed by the layer.

Source: Aschbacher–Smith B.4.2(1) and 13.7.21, printed pp.86 and 945.
-/

public section
open Subgroup Representation Representation.BinaryOffender

namespace Representation.SL2NaturalOffenders
variable {H V F : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Every offender on a generated natural cover is the layer Sylow intersection. -/
theorem offender_eq_sylowInf_of_generated_cover
    (α : Representation (ZMod 2) H V) (hα : Function.Injective α)
    (L : Subgroup H) [L.Normal] (e : L ≃* NoStrong.Actor F)
    (hF : 2 < Nat.card F)
    (f : V →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (hk : f.ker = fixedSpace α L)
    (he : ∀ (g : L) v, f (α (g : H) v) = Matrix.mulVec (e g).val (f v))
    (hwhole : subspaceCommutator α ⊤ L = ⊤)
    (T : Sylow 2 H) {A : Subgroup H} (hAT : A ≤ T) (hA : IsOffender α A) :
    A = (T : Subgroup H) ⊓ L := by
  let τ := (NoStrong.natural (F := F)).comp e.toMonoidHom
  have hτ : Function.Injective τ := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun hab v
  obtain ⟨ρ,hρ,hfull,hnat⟩ := exists_faithful_action_of_generated_layer_quotient
    α hα L τ hτ f hf hk he hwhole
  have hAρ : IsOffender ρ A :=
    ⟨hA.1,(fixedCodim_le_of_equivariant_surjection α ρ f hf hfull A).trans hA.2⟩
  exact (Ratios.offender_iff_eq_sylowInf L e ρ hnat hF hρ T hAT).mp hAρ

end Representation.SL2NaturalOffenders

namespace Representation.SL2OrthogonalCover
open Representation.OneCohomology
variable {H V F : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite H] [FiniteDimensional (ZMod 2) V] in
private theorem moved_eq_coinvariants (α : Representation (ZMod 2) H V) (L : Subgroup H) :
    subspaceCommutator α ⊤ L = Coinvariants.ker (α.comp L.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g,hg,w,_,rfl⟩
    exact ⟨(⟨g,hg⟩,w),rfl⟩
  · rintro ⟨⟨g,w⟩,rfl⟩
    exact ⟨g,g.property,w,Submodule.mem_top,rfl⟩

/-- In a full field-four natural cover, a Sylow subgroup has equal fixed and moved spaces. -/
theorem cover_sylow_fixed_eq_moved
    (hF : Nat.card F = 4) [CharP F 2]
    {σ : Representation (ZMod 2) (SL F) V}
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p)
    (S : Sylow 2 (SL F)) :
    fixedSpace σ (S : Subgroup (SL F)) = subspaceCommutator σ ⊤ (S : Subgroup (SL F)) := by
  have hg := cover_sylow_geometry 2 (by decide) (by simpa using hF) p hp S
  have he := cover_sylow_preimage p hp S
  change fixed (σ.comp S.toSubgroup.subtype) = _
  rw [moved_eq_coinvariants]
  exact he.symm.trans hg.2.1

end Representation.SL2OrthogonalCover
namespace Representation.SL2NaturalOffenders
open Representation.OneCohomology Representation.SL2OrthogonalCover
variable {H V F : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite H] [FiniteDimensional (ZMod 2) V] [Finite F] in
private theorem cover_kernel_eq_fixed
    (α : Representation (ZMod 2) H V) (L : Subgroup H)
    (e : L ≃* NoStrong.Actor F)
    (p : Representation.IntertwiningMap
      (α.comp (L.subtype.comp e.symm.toMonoidHom)) (binaryNatural (F := F)))
    (hp : IsCover p) : p.toLinearMap.ker = fixedSpace α L := by
  ext v
  constructor
  · intro hv g
    have hh := hp.2.1 hv (e g)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hh
  · intro hv
    apply natural_fixed_all_eq_zero
    intro a
    change (binaryNatural (F := F)) a (p v) = p v
    rw [← IntertwiningMap.isIntertwining _ _ p]
    have hh := hv (e.symm a)
    change α (e.symm a : H) v = v at hh
    rw [show (α.comp (L.subtype.comp e.symm.toMonoidHom)) a v = v from hh]

/-- The fixed space of the normal layer lies in every ambient offender moved space. -/
theorem fixed_le_moved_of_cover_offender
    (α : Representation (ZMod 2) H V) (hα : Function.Injective α)
    (L : Subgroup H) [L.Normal] (e : L ≃* NoStrong.Actor F)
    (hF : Nat.card F = 4)
    (p : Representation.IntertwiningMap
      (α.comp (L.subtype.comp e.symm.toMonoidHom)) (binaryNatural (F := F))) (hp : IsCover p)
    (T : Sylow 2 H) {A : Subgroup H} (hAT : A ≤ T) (hA : IsOffender α A) :
    fixedSpace α L ≤ subspaceCommutator α ⊤ A := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hwhole : subspaceCommutator α ⊤ L = ⊤ := by
    apply top_unique
    have hh : Coinvariants.ker (α.comp (L.subtype.comp e.symm.toMonoidHom)) ≤
        subspaceCommutator α ⊤ L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,v⟩,rfl⟩
      exact Submodule.subset_span ⟨e.symm a,(e.symm a).property,v,Submodule.mem_top,rfl⟩
    rwa [hp.2.2] at hh
  have he (g : L) (v : V) : p (α (g : H) v) = Matrix.mulVec (e g).val (p v) := by
    change p (α (g : H) v) = (binaryNatural (F := F)) (e g) (p v)
    have hh := IntertwiningMap.isIntertwining _ _ p (e g) v
    change p (α (L.subtype g) v) = (binaryNatural (F := F)) (e g) (p v)
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hh
  have hAe := offender_eq_sylowInf_of_generated_cover α hα L e
    (by omega) p.toLinearMap hp.1 (cover_kernel_eq_fixed α L e p hp) he hwhole T hAT hA
  obtain ⟨P,hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let β := α.comp (L.subtype.comp e.symm.toMonoidHom)
  have hmap : (S : Subgroup (NoStrong.Actor F)).map (L.subtype.comp e.symm.toMonoidHom) = A := by
    change ((P : Subgroup L).map e.toMonoidHom).map (L.subtype.comp e.symm.toMonoidHom) = A
    rw [Subgroup.map_map]
    have heq : (L.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = L.subtype := by
      ext x
      simp
    rw [heq,hP,← hAe]
  have hgeom := cover_sylow_fixed_eq_moved hF p hp S
  have hm : subspaceCommutator β ⊤ (S : Subgroup (NoStrong.Actor F)) =
      subspaceCommutator α ⊤ A := by
    rw [subspaceCommutator_comp_map,hmap]
  have hf : fixedSpace β (S : Subgroup (NoStrong.Actor F)) = fixedSpace α A := by
    rw [fixedSpace_comp_map,hmap]
  rw [hf,hm] at hgeom
  rw [← hgeom]
  rw [hAe]
  exact fixedSpace_antitone α inf_le_right

end Representation.SL2NaturalOffenders
