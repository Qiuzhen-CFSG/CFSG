module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.FourElementField
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants

public import Theory.SpecificGroups.SU3.ProjectiveLinearEmbedding

/-!
# The three-dimensional model centralizers for E.6.23

In PSL₃(4), the full centralizer of an involution is a two-group. The same
holds for the centralizer of a noncentral involution in every central
two-cover: project to PSL₃(4), then use the two-group kernel.

PSU₃(4) embeds in PSL₃(16), using the actual projective matrix groups.
Every involution centralizer in the latter has order 20480, prime to three.
The embedding therefore gives the required prime-to-three assertion for
PSU₃(4). Its parameter remains the fixed-field order four, so its matrices
are over a field of order sixteen. No outer-automorphism table is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265), inspecting the models in E.6.8(1).
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional

variable {H D : Type*} [Group H] [Group D]

private def centralizerMap (f : H →* D) (t : H) :
    centralizer ({t} : Set H) →* centralizer ({f t} : Set D) :=
  (f.comp (centralizer ({t} : Set H)).subtype).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    change f x * f t = f t * f x
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp x.property))

private theorem centralizerMap_injective (f : H →* D) (hf : Function.Injective f) (t : H) :
    Function.Injective (centralizerMap f t) := by
  intro x y he
  exact Subtype.ext (hf (congrArg Subtype.val he))

/-- Every involution centralizer in the actual PSL₃(4) model is a two-group. -/
theorem linear_four_centralizer_isTwoGroup
    (hm : ClassicalGroup.IsPSL H 3 4) (t : H) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsPGroup 2 (centralizer ({t} : Set H)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have he : e t ≠ 1 := fun hh => ht (e.injective (hh.trans (map_one e).symm))
  have he2 : (e t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  let c := Matrix.PSL3.EvenInnerCentralizers.involutionCentralizerEquiv
    F (n := 2) (by decide) hF (e t) he he2
  have hp := (Matrix.PSL3.EvenInnerCentralizers.centralizer_isTwoGroup_of_card_four
    F hF).of_equiv c.symm
  exact hp.of_injective (centralizerMap e.toMonoidHom t)
    (centralizerMap_injective e.toMonoidHom e.injective t)

/-- No factor three occurs in the centralizer of an involution in PSU₃(4). -/
theorem unitary_four_centralizer_three_free
    (hm : ClassicalGroup.IsPSU H 3 4) (t : H) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ¬ 3 ∣ Nat.card (centralizer ({t} : Set H)) := by
  obtain ⟨F, _, _, J, hF, _, ⟨e⟩⟩ := hm
  let f := (J.projectiveLinearEmbedding).comp e.toMonoidHom
  have hf : Function.Injective f := (J.projectiveLinearEmbedding_injective).comp e.injective
  have he : f t ≠ 1 := fun hh => ht (hf (hh.trans (map_one f).symm))
  have he2 : (f t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  let c := Matrix.PSL3.EvenInnerCentralizers.involutionCentralizerEquiv
    F (n := 4) (by decide) hF (f t) he he2
  have hcard : Nat.card (centralizer ({f t} : Set PSL(3,F))) = 20480 := by
    rw [Nat.card_congr c.toEquiv,
      Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants.centralizer_card F (n := 4) hF (by decide) (by decide)]
    norm_num
  have hd := card_dvd_of_injective (centralizerMap f t) (centralizerMap_injective f hf t)
  rw [hcard] at hd
  exact fun h3 => (by decide : ¬ 3 ∣ 20480) (h3.trans hd)

/-- The entire central two-cover is retained; only the involution is required
to have nonidentity image in its central quotient. -/
theorem cover_linear_four_centralizer_isTwoGroup
    (hz : IsPGroup 2 (center H)) (hm : ClassicalGroup.IsPSL (H ⧸ center H) 3 4)
    (t : H) (ht : t ∉ center H) (ht2 : t ^ 2 = 1) :
    IsPGroup 2 (centralizer ({t} : Set H)) := by
  let q := QuotientGroup.mk' (center H)
  have he : q t ≠ 1 := fun hh => ht ((QuotientGroup.eq_one_iff t).mp hh)
  have he2 : (q t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hp := linear_four_centralizer_isTwoGroup hm (q t) he he2
  have hk : IsPGroup 2 q.ker := by rwa [QuotientGroup.ker_mk']
  apply (hp.comap_of_ker_isPGroup q hk).to_le
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul] using congrArg q (mem_centralizer_singleton_iff.mp hx)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional
