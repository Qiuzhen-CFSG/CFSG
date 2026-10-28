module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Bounds

/-!+# The actual quotient for the initial natural-section argument

The quotient V_a/Z_a is formed inside the finite vertex stabilizer. Its
kernel is normal relative to that stabilizer, not in the free amalgam.
`ElementaryRadiusQuotient` names the elementary-abelian assertion needed
before dualizing this quotient; its proof is in Elementary.lean.

The quotient projection onto SL₃(2) is constructed by conjugating the
specified source projection. Its kernel is exactly the neighborhood kernel.
The remaining representation argument must prove the triple commutator,
fixed/moving splitting and actual natural coordinates from the small
displacement bound. These conclusions are not part of the definition below.

Source: Meierfrankenfeld--Stellmacher (1993), notation p.881 and
(4.3.1)(iii), pp.882--883; the cited module results are (1.4)--(1.5), pp.842--843.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The literal elementary-abelian quotient required before taking the dual module.
The normality instance comes from the actual local geometry. -/
def ElementaryRadiusQuotient (geometry : Geometry R) (a : Vertex R) : Prop :=
  letI := geometry.Z_normal a
  IsElementaryAbelian 2
    ((V R a).subgroupOf (stabilizer R a) ⧸
      ((Z R a).subgroupOf (stabilizer R a)).subgroupOf
        ((V R a).subgroupOf (stabilizer R a)))

/-- V is normal in its local stabilizer, independently of representation recognition. -/
theorem radius_normal (a : Vertex R) :
    ((V R a).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (V_normalized a)

variable [Finite M]

/-- The given source quotient transported to any M-type vertex, with its exact kernel. -/
theorem exists_localProjection (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f :=
    (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le
      (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl,
      ← map_map, ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  refine ⟨source.projection.comp e.symm.toMonoidHom,
    source.projection_surjective.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, source.projection_kernel, ← hQ]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change e.symm (e y) ∈ pCore 2 M
    rw [MulEquiv.symm_apply_apply]
    exact hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
