module
public import Theory.GroupAction.CubicTree.TrackFixer

/-!
# Recentring and conjugating the actual track

Changing the integer origin or reversing the line preserves its literal
pointwise fixer. Moving the line by the group action conjugates both the
translation and the fixer. These identities normalize arbitrary tracks onto
one chosen base edge in Goldschmidt (1980), (5.3), before applying the
centralizer conclusion to the new tracks in (6.11).
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph Subgroup SimpleGraph.PathTransitivePolygon
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
namespace Track

/-- Recenter the same oriented track at an integer vertex. -/
def shift (t : Track Γ G) (j : ℤ) : Track Γ G where
  vertex i := t.vertex (i+j)
  injective := t.injective.comp (fun _ _ he => by omega)
  adjacent i := by simpa only [add_right_comm i 1 j] using t.adjacent (i+j)
  translation := t.translation
  translate i := by simpa only [add_right_comm i 2 j] using t.translate (i+j)

@[simp] theorem shift_fixer (t : Track Γ G) (j : ℤ) : (t.shift j).fixer = t.fixer := by
  ext g
  simp only [mem_fixer]
  constructor
  · intro h i
    simpa [shift] using h (i-j)
  · intro h i
    exact h (i+j)

/-- Move a track by the actual group action and conjugate its translation. -/
def conjugate (t : Track Γ G) (hact : GraphAction Γ G) (g : G) : Track Γ G where
  vertex i := g • t.vertex i
  injective := (MulAction.toPerm g).injective.comp t.injective
  adjacent i := hact.map_adj g (t.adjacent i)
  translation := g*t.translation*g⁻¹
  translate i := by simp only [mul_smul,inv_smul_smul,t.translate]

/-- Conjugation carries the literal pointwise track fixer to the fixer of
the translated track. -/
theorem conjugate_fixer (t : Track Γ G) (hact : GraphAction Γ G) (g : G) :
    (t.conjugate hact g).fixer = t.fixer.map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨(MulAut.conj g).symm x,?_,(MulAut.conj g).apply_symm_apply x⟩
    apply t.mem_fixer.mpr
    intro i
    have hh := (t.conjugate hact g).mem_fixer.mp hx i
    change x • (g • t.vertex i) = g • t.vertex i at hh
    simpa [mul_smul] using congrArg (g⁻¹ • ·) hh
  · rintro ⟨y,hy,rfl⟩
    apply (t.conjugate hact g).mem_fixer.mpr
    intro i
    change (g*y*g⁻¹) • (g • t.vertex i) = g • t.vertex i
    simp only [mul_smul,inv_smul_smul,t.mem_fixer.mp hy]

/-- The two orientations of the line have exactly the same pointwise fixer. -/
@[simp] theorem reverse_fixer (t : Track Γ G) : t.reverse.fixer = t.fixer := by
  ext g
  simp only [mem_fixer]
  constructor
  · intro h i
    simpa [Track.reverse] using h (-i)
  · intro h i
    exact h (-i)

end Track
end Theory.GroupAction.CubicTree
