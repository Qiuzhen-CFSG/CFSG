module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackNormalization
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerCentralizer

/-!
# A cubic centralizer for every source track

Normalize an arbitrary track onto the original base edge, keeping its full
pointwise fixer under conjugation. The proved normalizer conclusion of (5.3)
gives a cubic divisor in the actual finite vertex centralizer. Cauchy and
conjugation produce an order-three element at one of the original track
endpoints, centralizing its entire fixer. Goldschmidt (6.11), printed p.402,
applies precisely this form to newly constructed tracks.
-/

public section

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup Theory.GroupTheory Theory.GroupAction.CubicTree SimpleGraph
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- For any original track with nontrivial fixer, a cubic element centralizes
that entire fixer at one of the first two vertices. This is the unbased form
of (5.3) used for the new tracks in Goldschmidt (6.11). -/
theorem CubicTreeAction.track_centralizer_exists_three
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) (hv : v.type = false)
    (t : Track (RankTwo.graph F) G) (hQ : t.fixer ≠ ⊥) :
    ∃ (i : Fin 2) (x : G), orderOf x = 3 ∧
      x ∈ RankTwo.stabilizer F (t.vertex (i : ℤ)) ∧
      x ∈ centralizer (t.fixer : Set G) := by
  obtain ⟨u,g,i,hu0,hu1,hui,huQ⟩ := exists_base_track_conjugate t
  have hu : u.fixer ≠ ⊥ := by
    intro hb
    apply hQ
    rw [← huQ,hb,Subgroup.map_bot]
  let : Finite (F false) := h.finite false
  have hd := normalizer_centralizer_three_dvd h u hu0 hu1 hu hs hsodd hshort p hp hn hv
  let C := (centralizer (u.fixer : Set G)).subgroupOf (F false)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hd
  let f : C →* G := (F false).subtype.comp C.subtype
  have hf : Function.Injective f := (F false).subtype_injective.comp C.subtype_injective
  let c : MulAut G := MulAut.conj g
  refine ⟨i,c (f x),?_,?_,?_⟩
  · exact (orderOf_injective c.toMonoidHom c.injective (f x)).trans
      ((orderOf_injective f hf x).trans hx)
  · change c (f x) • t.vertex (i : ℤ) = t.vertex (i : ℤ)
    have hfix : f x • u.vertex 0 = u.vertex 0 := by
      rw [hu0]
      change f x ∈ MulAction.stabilizer G (RankTwo.base F false)
      rw [RankTwo.base,stabilizer_base]
      exact x.1.2
    rw [← hui]
    change (g*f x*g⁻¹) • (g • u.vertex 0) = g • u.vertex 0
    simp only [mul_smul,inv_smul_smul,hfix]
  · intro y hy
    rw [← huQ] at hy
    obtain ⟨y,hy,rfl⟩ := hy
    have hh : y*f x = f x*y := x.property y hy
    exact (map_mul c y (f x)).symm.trans ((congrArg c hh).trans (map_mul c (f x) y))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
