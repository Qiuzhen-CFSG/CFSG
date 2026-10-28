module
public import CFSG.Quasithin.ChapterD.Section02.Conjugacy
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy
/-!
# Normality of the minimum cubic actor subgroup

Conjugation preserves cubicity, rank, fixed codimension and inclusion.
It therefore preserves the literal minimum family and its minimal members.
Their generated subgroup Jhat is normal in the original actor.

Source: Aschbacher--Smith, D.2.15--17, printed pp.187--188; used in
original 14.6.12 to supplement Jhat by the mapped Sylow subgroup.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem QhatMin.map_conj {A : Subgroup G} (hA : A ∈ QhatMin ρ) (g : G) :
    A.map (MulAut.conj g).toMonoidHom ∈ QhatMin ρ := by
  refine ⟨hA.1,hA.2.1.map_conj g,?_,?_⟩
  · exact (Representation.OrthogonalFourMinus.RankOne.InnerTransport.cubic_conj_iff
      ρ A g).mpr hA.2.2.1
  · rw [actionRatio_map_conj]
    exact hA.2.2.2

theorem QhatStar.map_conj {A : Subgroup G} (hA : A ∈ QhatStar ρ) (g : G) :
    A.map (MulAut.conj g).toMonoidHom ∈ QhatStar ρ := by
  let e := (MulAut.conj g).mapSubgroup
  refine ⟨QhatMin.map_conj ρ hA.1 g,?_⟩
  intro B hB hBA
  have hC : e.symm B ∈ QhatMin ρ := by
    have hi : (MulAut.conj g).symm = MulAut.conj g⁻¹ := by
      ext x
      simp
    change B.map (MulAut.conj g).symm.toMonoidHom ∈ QhatMin ρ
    rw [hi]
    exact QhatMin.map_conj ρ hB g⁻¹
  have he := hA.2 _ hC (e.symm_apply_le.mpr hBA)
  change B = e A
  rw [←he,e.apply_symm_apply]

theorem Jhat_normal : (Jhat ρ).Normal := by
  constructor
  intro x hx g
  have hm : (Jhat ρ).map (MulAut.conj g).toMonoidHom ≤ Jhat ρ := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA a ha
    exact le_sSup (QhatStar.map_conj ρ hA g) (mem_map_of_mem _ ha)
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
end CFSG.Quasithin.ChapterD
