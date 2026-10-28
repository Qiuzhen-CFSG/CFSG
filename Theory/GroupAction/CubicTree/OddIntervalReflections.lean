module
public import Theory.GroupAction.CubicTree.CentralTranslation
public import Theory.GroupAction.CubicTree.Reflections

/-!
# Odd fixed intervals produce adjacent involution movers

An even translation moves the left endpoint of an odd-length fixed interval
to the vertex just beyond its original right endpoint. The two conjugate
involutions then fix adjacent vertices and move each other's fixed vertex.
On the preferred source track this supplies reflections.

Source: Goldschmidt (6.5), printed p.397.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
namespace Track

theorem CentralInterval.adjacentInvolutionMovers_of_odd
    {t : Track Γ G} {z : G} (d : t.CentralInterval z) (hz : t.CentralInvolution z)
    (hodd : Odd (d.fixedRight - d.fixedLeft)) : AdjacentInvolutionMovers Γ G := by
  obtain ⟨m, hm⟩ := hodd
  let k : ℤ := m + 1
  let z' := (MulAut.conj (t.translation ^ k)) z
  let e := d.shift k
  have he : e.fixedLeft = d.fixedRight + 1 := by
    dsimp only [e, CentralInterval.shift, k]
    omega
  have hz' := hz.shift k
  have hr := d.centralRight_mem
  have hr' := e.centralRight_mem
  refine ⟨t.vertex d.fixedRight, t.vertex (d.fixedRight + 1), z, z',
    t.adjacent _, (d.fixed_iff _).2 ⟨le_trans hr.1 hr.2, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := (e.fixed_iff e.fixedLeft).2 ⟨le_rfl, le_trans hr'.1 hr'.2⟩
    simpa only [he] using hh
  · intro hh
    have hn := (d.fixed_iff _).1 hh
    omega
  · intro hh
    have hn := (e.fixed_iff _).1 hh
    omega
  · rw [← hz.1]
    exact pow_orderOf_eq_one z
  · rw [← hz'.1]
    exact pow_orderOf_eq_one z'

theorem hasReflections_of_odd_centralInterval {t : Track Γ G}
    (hpreferred : AdjacentInvolutionMovers Γ G → t.HasReflections)
    {z : G} (d : t.CentralInterval z) (hz : t.CentralInvolution z)
    (hodd : Odd (d.fixedRight - d.fixedLeft)) : t.HasReflections :=
  hpreferred (d.adjacentInvolutionMovers_of_odd hz hodd)

end Track
end Theory.GroupAction.CubicTree
