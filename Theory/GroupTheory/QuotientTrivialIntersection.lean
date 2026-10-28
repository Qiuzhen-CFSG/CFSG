module

public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.MarkedConjugateGeneration

/-!
# Trivial intersection after a kernel quotient

Conjugation commutes with a group homomorphism. A surjection therefore
carries subgroups intersecting in precisely its kernel to subgroups with
trivial intersection. The normalizer exception and the original quotient
map are retained. This is the quotient transport in Aschbacher45.9,p246.
-/

public section
open Subgroup
namespace Subgroup
variable {G H:Type*} [Group G] [Group H]
theorem ti_image_of_kernel_intersections (f:G→*H) (hf:Function.Surjective f)
    (S:Subgroup G) (hk:f.ker≤S)
    (hTI:∀g:G,g∉normalizer (S:Set G)→S⊓S.map (MulAut.conj g).toMonoidHom=f.ker) :
    ∀g:H,g∉normalizer (S.map f:Set H)→Disjoint (S.map f) ((S.map f).map (MulAut.conj g).toMonoidHom) := by
  intro b hb
  obtain ⟨g,rfl⟩:=hf b
  have hg:g∉normalizer (S:Set G):=fun hh=>hb (S.le_normalizer_map f (mem_map_of_mem f hh))
  have hkg:f.ker≤S.map (MulAut.conj g).toMonoidHom:=by
    have hh: f.ker.map (MulAut.conj g).toMonoidHom=f.ker:=Normal.map_conj_eq _ _
    exact hh.ge.trans (map_mono hk)
  rw [disjoint_iff]
  apply (comap_injective hf)
  rw [comap_inf,comap_map_eq_self hk,←image_conjugate,comap_map_eq_self hkg,
    MonoidHom.comap_bot,hTI g hg]
end Subgroup
