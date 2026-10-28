module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry
public import Theory.AlgebraicGroup.BNPair.MaximalParabolic

/-!
# Maximal parabolics of a marked octagonal Tits system

For two vertex types, each singleton of distinguished reflections is the
complement of the other. Thus both marked parabolics are maximal proper
subgroups. This uses the abstract standard-parabolic classification and
keeps concrete matrix and quotient instances outside the proof.

Source: GLS3 2.6.5; Aschbacher–Smith J.5.3, printed p.445.
-/

public section
namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry.OctagonalDatum
variable {G I:Type*} [Group G] {T:TitsSystem (X:=G)} {F:I→Subgroup G}

/-- Both parabolics are maximal when the two indicated types exhaust the marking. -/
theorem parabolic_isCoatom_of_two (D:OctagonalDatum T F) {i j:I} (hne:i≠j)
    (hcover:∀k:I,k=i ∨ k=j) : IsCoatom (F i) := by
  have hn:D.simple i≠D.simple j:=fun h=>hne (D.simple_injective h)
  have he:T.S \ {D.simple j}={D.simple i}:=by
    rw [← D.simple_range]
    ext x
    simp only [Set.mem_sdiff,Set.mem_range,Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨k,rfl⟩,hk⟩
      rcases hcover k with rfl | rfl
      · rfl
      · exact (hk rfl).elim
    · rintro rfl
      exact ⟨⟨i,rfl⟩,hn⟩
  have h:=T.standardParabolic_isCoatom (D.simple_mem j)
  rw [he,← D.parabolic_eq] at h
  exact h

end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry.OctagonalDatum
