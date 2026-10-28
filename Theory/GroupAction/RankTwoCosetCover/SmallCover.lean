module

public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth

/-!
# Injectivity of small coset coverings

A covering is injective on vertices when its source diameter is smaller
than every target cycle: the image of a shortest path between two vertices
in one fiber is a short nonbacktracking closed walk. Local injectivity on
a vertex group then kills the group-homomorphism kernel.

This is the geometry-to-group comparison used for small completions in
Aschbacher–Smith F.4.8 and F.4.26, printed pp.278 and 288.
-/

@[expose] public section

open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
namespace Subgroup.CosetGeometry.RankTwo.CoverData
variable {A B : Type*} [Group A] [Group B]
variable {F : Bool → Subgroup A} {E : Bool → Subgroup B} {f : A →* B}
variable (c : CoverData F E f)

theorem vertex_injective_of_diameter_lt_girth {n : ℕ}
    (hconn : (graph F).Connected)
    (hdiam : ∀v w,(graph F).dist v w ≤ n)
    (hgirth : ∀v (p : (graph E).Walk v v),p.IsCycle → n<p.length) :
    Function.Injective c.vertex := by
  intro v w he
  obtain ⟨p,hp,hlen⟩ := hconn.exists_path_of_dist v w
  let q := (BasedWalk.ofWalk p).map c.hom
  have hq : q.Nonbacktracking :=
    (BasedWalk.nonbacktracking_map_iff c.hom (fun v => (c.neighbor_bijective v).1) _).mpr
      (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
  have hpath := isPath_of_nonbacktracking_of_cycle_bound hgirth q hq
    (by simpa only [hlen] using hdiam v w)
  have hqend : q.endpoint=c.vertex v := by
    rw [BasedWalk.endpoint_map]
    rw [BasedWalk.endpoint_ofWalk]
    exact (show c.hom w = c.vertex w from rfl).trans he.symm
  have hnil := hpath.nil_iff_eq.mpr hqend.symm
  have hz : p.length=0 := by
    have hh := hnil.length_eq_zero
    simpa only [BasedWalk.length_toWalk] using hh
  exact p.eq_of_length_eq_zero hz

include c in
theorem injective_of_diameter_lt_girth {n : ℕ}
    (hconn : (graph F).Connected)
    (hdiam : ∀v w,(graph F).dist v w ≤ n)
    (hgirth : ∀v (p : (graph E).Walk v v),p.IsCycle → n<p.length) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro a ha
  have ha1 : f a=1 := ha
  have hfix : a • base F false=base F false := by
    apply c.vertex_injective_of_diameter_lt_girth hconn hdiam hgirth
    rw [c.vertex_smul,ha1,one_smul]
  have hmem : a∈F false := by
    change a ∈ stabilizer F (base F false) at hfix
    simpa only [stabilizer,base,CosetGeometry.stabilizer_base] using hfix
  have he := c.injective false (a₁ := ⟨a,hmem⟩) (a₂ := 1) (by simpa using ha1)
  exact congrArg Subtype.val he
end Subgroup.CosetGeometry.RankTwo.CoverData
