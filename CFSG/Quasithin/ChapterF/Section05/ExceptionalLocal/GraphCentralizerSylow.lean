module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCore
public import Theory.GroupTheory.CentralizerSylowConjugacy

/-!
# The marked Sylow centralizer at the start of F.5.5

Choose the graph-to-short conjugator to carry the actual Sylow R onto
C_T(t). Pulling the root back gives an involution u with C_G(f,u)=R,
while u is a root and fu belongs to the graph class. These marks are
retained for the quotient by the central graph involution.

Source: Aschbacher--Smith F.5.5, printed pp.301--302.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)
include hf

/-- The source graph-to-short conjugator can simultaneously carry R to Tt. -/
theorem exists_graph_short_sylow_conjugator (R : Sylow 2 (C c i)) :
    ∃ g : G, MulAut.conj g (Source.graphElement c i) = t ∧
      (Rimage c i R).map (MulAut.conj g).toMonoidHom = Tcentralizer c i t := by
  obtain ⟨S,hS⟩ := hf.t_sylow
  obtain ⟨g,hg,he⟩ := Sylow.exists_conj_element_and_centralizer_sylow
    (Source.graphElement c i) t hf.graph_fuses_t R S
  refine ⟨g,hg,?_⟩
  rw [hS,subgroupOf_map_subtype] at he
  exact he

/-- The literal graph centralizer contains a Sylow-central root whose
product with f belongs to the other ambient involution class. -/
theorem exists_graph_centralizer_root (R : Sylow 2 (C c i))
    (hj : centralizer ({rootElement c i z,t} : Set G) = Tcentralizer c i t) :
    ∃ u : G, u ∈ Rimage c i R ∧ IsConj (rootElement c i z) u ∧
      IsConj (Source.graphElement c i) (Source.graphElement c i*u) ∧
      C c i ⊓ centralizer ({u} : Set G) = Rimage c i R := by
  obtain ⟨g,hg,hR⟩ := exists_graph_short_sylow_conjugator c i z t hf R
  let e := MulAut.conj g
  have hgt : e (Source.graphElement c i) = t := hg
  let u := e.symm (rootElement c i z)
  have hu : e u = rootElement c i z := e.apply_symm_apply _
  have hmem (x : G) : x ∈ Rimage c i R ↔ e x ∈ Tcentralizer c i t := by
    rw [←hR]
    exact (mem_map_iff_mem e.injective).symm
  have huR : u ∈ Rimage c i R := (hmem u).mpr (by
    rw [hu]
    exact ⟨((TfImage_eq c i).le (normalizer_A_le_TfImage c i z t hf false
      (hf.root_mem_A false))).1,
      mem_centralizer_singleton_iff.mpr hf.t_commutes_root.symm.eq⟩)
  have hzu : IsConj (rootElement c i z) u := isConj_iff.mpr ⟨g⁻¹,by simp [u,e]⟩
  have hfu : IsConj (Source.graphElement c i) (Source.graphElement c i*u) := by
    obtain ⟨y,_,hy⟩ := hf.t_fuses_t_root
    have hty : IsConj t (t*rootElement c i z) := isConj_iff.mpr ⟨y,hy⟩
    have hc := e.symm.toMonoidHom.map_isConj hty
    have hgf : e.symm t = Source.graphElement c i := e.symm_apply_eq.mpr hg.symm
    simpa only [map_mul,MulEquiv.coe_toMonoidHom,hgf] using hc
  refine ⟨u,huR,hzu,hfu,?_⟩
  ext x
  rw [hmem,←hj]
  change (x ∈ C c i ∧ x ∈ centralizer ({u} : Set G)) ↔
    e x ∈ centralizer ({rootElement c i z,t} : Set G)
  constructor
  · rintro ⟨hxf,hxu⟩ y hy
    have hy : y=rootElement c i z ∨ y=t := by simpa using hy
    rcases hy with rfl|rfl
    · have hh := congrArg e (mem_centralizer_singleton_iff.mp hxu)
      simpa only [map_mul,hu] using hh.symm
    · have hh := congrArg e (mem_centralizer_singleton_iff.mp hxf)
      simpa only [map_mul,hgt] using hh.symm
  · intro hx
    constructor
    · apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul,hgt] using (hx t (by simp)).symm
    · apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul,hu] using (hx (rootElement c i z) (by simp)).symm

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
