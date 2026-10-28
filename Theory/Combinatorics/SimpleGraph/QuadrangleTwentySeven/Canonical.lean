module

public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Coordinates

/-!
# Canonical coordinates for the 27-point quadrangle

The point, ten line-neighbor, and sixteen even-word coordinates form a graph
with the same adjacency relation as any SRG(27,10,1,5). The coordinate map is
constructed from a frame and is proved to be a graph isomorphism.
-/

public section


open SimpleGraph
namespace Theory.Combinatorics.QuadrangleTwentySeven
abbrev Vertex := Option ((Fin 5×Bool)⊕EvenWord)
def canonicalAdj : Vertex→Vertex→Prop
  | none,some (.inl _) => True
  | some (.inl _),none => True
  | some (.inl (i,b)),some (.inl (j,c)) => i=j ∧b≠c
  | some (.inl (i,b)),some (.inr w) => w.val i=b
  | some (.inr w),some (.inl (i,b)) => w.val i=b
  | some (.inr v),some (.inr w) => ∃i,w.val=flip i v.val
  | _,_=>False

def canonical : SimpleGraph Vertex where
  Adj:=canonicalAdj
  symm:=by
    constructor
    intro a b h
    rcases a with _|a
    · rcases b with _|b
      · exact h
      rcases b with p|w
      · trivial
      · exact h
    rcases b with _|b
    · rcases a with p|w
      · trivial
      · exact h
    rcases a with ⟨i,c⟩|v <;> rcases b with ⟨j,d⟩|w
    · exact ⟨h.1.symm,h.2.symm⟩
    · exact h
    · exact h
    · obtain ⟨i,hi⟩:=h
      exact ⟨i,by rw [hi];exact (flip_involutive i v.val).symm⟩
  loopless:=by
    constructor
    intro a
    rcases a with _|a
    · exact not_false
    rcases a with ⟨i,b⟩|w
    · exact fun h=>h.2 rfl
    · rintro ⟨i,hi⟩
      exact flip_ne i w.val hi.symm

namespace Frame
variable {V:Type*} [Fintype V] {Γ:SimpleGraph V} [DecidableRel Γ.Adj]
 {x y:V} (D:Frame (Γ:=Γ) x y) (h:Γ.IsSRGWith 27 10 1 5) (hy:Γᶜ.Adj x y)
include D h hy

noncomputable def decode : Vertex→V
  | none=>x
  | some (.inl p)=>D.point p.1 p.2
  | some (.inr w)=>((D.labelEquiv h hy).symm w).val

private theorem decode_near_ne (p:Fin 5×Bool) : D.decode h hy (some (.inl p))≠x :=
  (D.near p.1 p.2).ne.symm
private theorem decode_far_ne (w:EvenWord) : D.decode h hy (some (.inr w))≠x :=
  ((D.labelEquiv h hy).symm w).property.1.symm
private theorem decode_far_not_adj (w:EvenWord) : ¬Γ.Adj x (D.decode h hy (some (.inr w))) :=
  ((D.labelEquiv h hy).symm w).property.2

theorem decode_injective : Function.Injective (D.decode h hy) := by
  intro a b hab
  rcases a with _|a <;> rcases b with _|b
  · rfl
  · rcases b with p|w
    · exact (D.decode_near_ne h hy p hab.symm).elim
    · exact (D.decode_far_ne h hy w hab.symm).elim
  · rcases a with p|w
    · exact (D.decode_near_ne h hy p hab).elim
    · exact (D.decode_far_ne h hy w hab).elim
  · rcases a with p|v <;> rcases b with q|w
    · exact congrArg (some ∘ Sum.inl) (D.point_injective hab)
    · have hh:Γ.Adj x (D.decode h hy (some (.inr w))) := hab ▸ D.near p.1 p.2
      exact (D.decode_far_not_adj h hy w hh).elim
    · have hh:Γ.Adj x (D.decode h hy (some (.inr v))) := hab.symm ▸ D.near q.1 q.2
      exact (D.decode_far_not_adj h hy v hh).elim
    · have hvw:v=w := (D.labelEquiv h hy).symm.injective (Subtype.ext hab)
      exact congrArg (some ∘ Sum.inr) hvw

theorem decode_surjective : Function.Surjective (D.decode h hy) := by
  intro v
  by_cases hx:v=x
  · exact ⟨none,hx.symm⟩
  by_cases hn:Γ.Adj x v
  · obtain ⟨i,b,hv⟩:=D.near_cases hn
    exact ⟨some (.inl (i,b)),hv⟩
  · let z:Far Γ x:=⟨v,Ne.symm hx,hn⟩
    exact ⟨some (.inr (D.labelEquiv h hy z)),
      congrArg Subtype.val ((D.labelEquiv h hy).symm_apply_apply z)⟩

theorem decode_adj (a b:Vertex) : Γ.Adj (D.decode h hy a) (D.decode h hy b)↔canonical.Adj a b := by
  rcases a with _|a <;> rcases b with _|b
  · exact iff_false_intro (Γ.irrefl)
  · rcases b with p|w
    · exact iff_true_intro (D.near p.1 p.2)
    · exact iff_false_intro (D.decode_far_not_adj h hy w)
  · rcases a with p|w
    · exact iff_true_intro (D.near p.1 p.2).symm
    · exact iff_false_intro (fun ha=>D.decode_far_not_adj h hy w ha.symm)
  · rcases a with ⟨i,c⟩|v <;> rcases b with ⟨j,d⟩|w
    · exact D.adj_points_iff h i j c d
    · change Γ.Adj (D.point i c) ((D.labelEquiv h hy).symm w).val↔w.val i=c
      rw [Γ.adj_comm,D.adj_point_iff_label h,D.labelEquiv_symm_apply h hy]
    · change Γ.Adj ((D.labelEquiv h hy).symm v).val (D.point j d)↔v.val j=d
      rw [D.adj_point_iff_label h,D.labelEquiv_symm_apply h hy]
    · change Γ.Adj ((D.labelEquiv h hy).symm v).val ((D.labelEquiv h hy).symm w).val↔
        ∃i,w.val=flip i v.val
      rw [D.adj_far_iff h hy,D.labelEquiv_symm_apply h hy,D.labelEquiv_symm_apply h hy]

noncomputable def coordinateIso : canonical≃gΓ where
  toEquiv:=Equiv.ofBijective (D.decode h hy) ⟨D.decode_injective h hy,D.decode_surjective h hy⟩
  map_rel_iff':=D.decode_adj h hy _ _
end Frame
end Theory.Combinatorics.QuadrangleTwentySeven

namespace Theory.Combinatorics.QuadrangleTwentySeven

/-- Every SRG with parameters `(27,10,1,5)` admits the displayed coordinates. -/
theorem exists_coordinateIso {W : Type*} [Fintype W] (Δ : SimpleGraph W)
    [DecidableRel Δ.Adj] (hΔ : Δ.IsSRGWith 27 10 1 5) :
    Nonempty (canonical ≃g Δ) := by
  classical
  have hpos : 0 < Fintype.card W := by rw [hΔ.card]; decide
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
  have hfar : 0 < Fintype.card (Far Δ x) := by rw [far_card hΔ]; decide
  obtain ⟨y, hy⟩ := Fintype.card_pos_iff.mp hfar
  exact ⟨(frame hΔ hy).coordinateIso hΔ hy⟩

/-- Any two SRGs with parameters `(27,10,1,5)` are graph-isomorphic. -/
theorem exists_iso_of_srg {W Z : Type*} [Fintype W] [Fintype Z]
    (Δ : SimpleGraph W) (Ξ : SimpleGraph Z) [DecidableRel Δ.Adj] [DecidableRel Ξ.Adj]
    (hΔ : Δ.IsSRGWith 27 10 1 5) (hΞ : Ξ.IsSRGWith 27 10 1 5) :
    Nonempty (Δ ≃g Ξ) := by
  obtain ⟨eΔ⟩ := exists_coordinateIso Δ hΔ
  obtain ⟨eΞ⟩ := exists_coordinateIso Ξ hΞ
  exact ⟨eΔ.symm.trans eΞ⟩

end Theory.Combinatorics.QuadrangleTwentySeven
