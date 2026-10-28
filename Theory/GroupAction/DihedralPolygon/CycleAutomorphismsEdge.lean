module

public import Theory.GroupAction.DihedralPolygon.CycleAutomorphisms
public import Theory.GroupAction.DihedralPolygon

/-!
# The full automorphism group of the F.3.6 embedded polygon

The exact `edgeEmbedding` has an induced image with a proper bipartition given
by `BipartiteAction.color`. Transporting the cycle computation identifies its
full type-preserving automorphism group with `DihedralGroup m`. Consequently,
any injective homomorphism from that dihedral group onto an action on this
image is surjective. The faithful quotient action is intentionally an input;
its construction belongs to the F.3.6 assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), F.3.6, printed p.272, `refs/quasithin.pdf`.
-/

public section

namespace GroupAction.DihedralPolygon.CycleAutomorphisms
open SimpleGraph
variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

/-- The full group of type-preserving automorphisms on the literal range of the
F.3.6 construction, with its inherited colors. -/
noncomputable def edgeEmbeddingDihedralEquiv (D : BipartiteAction G Γ)
    {s t : G} {x l : V} {m n : ℕ}
    (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m) (hn : 0 < n) (hnm : n ≤ m)
    (hxl : Γ.Adj x l) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsx : s • x = x) (hsl : s • l ≠ l) (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) :
    DihedralGroup m ≃* colorPreserving
      (Γ.induce (Set.range (edgeEmbedding D hm hu hn hnm hxl hs ht hsx hsl htl htx hx hl)))
      (fun v => D.color v.1) :=
  inducedDihedralEquiv hm (edgeEmbedding D hm hu hn hnm hxl hs ht hsx hsl htl htx hx hl)
    D.color D.adjacent_color

/-- The faithful action produced by the F.3.6 quotient proof is the full
color-preserving automorphism group of this exact induced polygon. -/
theorem edgeEmbedding_surjective_of_injective (D : BipartiteAction G Γ)
    {s t : G} {x l : V} {m n : ℕ}
    (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m) (hn : 0 < n) (hnm : n ≤ m)
    (hxl : Γ.Adj x l) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsx : s • x = x) (hsl : s • l ≠ l) (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l)
    (ρ : DihedralGroup m →* colorPreserving
      (Γ.induce (Set.range (edgeEmbedding D hm hu hn hnm hxl hs ht hsx hsl htl htx hx hl)))
      (fun v => D.color v.1)) (hρ : Function.Injective ρ) : Function.Surjective ρ :=
  surjective_of_injective_induced hm
    (edgeEmbedding D hm hu hn hnm hxl hs ht hsx hsl htl htx hx hl)
    D.color D.adjacent_color ρ hρ

end GroupAction.DihedralPolygon.CycleAutomorphisms
