module



public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PolarPointResidues.AtPoint

/-!
# Point-residue consequences in original coordinates

The binary polar relation is converted back to original line and plane
incidence. It yields the eight noncoplanar lines, point-stabilizer transport,
and the projection through a plane used in I.5.9.
Source: Aschbacher–Smith, I.5.9, pp.421–422.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Theory.SpecificGroups.SymmetricSix
namespace PolarPointResidues
variable {G : Type*} [Group G] {S : DSystem .C3 G}
namespace Mark
variable {x : S.Point} {dual : Bool} (m : Mark S x dual)

theorem coplanar_iff (p q : PolarOrientation.Point dual) :
    (∃ π : S.Plane, S.Inc (m.lines p).val π ∧ S.Inc (m.lines q).val π) ↔
      p=q ∨ PolarOrientation.Collinear dual p q := by
  rw [←PolarOrientation.common_line_iff]
  constructor
  · rintro ⟨π,hp,hq⟩
    let π' : {π : S.Plane // S.Inc x π} := ⟨π,S.point_line_plane (m.lines p).property hp⟩
    refine ⟨m.planes.symm π',?_,?_⟩
    · apply (m.incident _ _).mp
      simpa only [Equiv.apply_symm_apply] using hp
    · apply (m.incident _ _).mp
      simpa only [Equiv.apply_symm_apply] using hq
  · rintro ⟨l,hp,hq⟩
    exact ⟨(m.planes l).val,(m.incident _ _).mpr hp,(m.incident _ _).mpr hq⟩

theorem noncoplanar_iff (p q : PolarOrientation.Point dual) :
    (¬∃ π : S.Plane, S.Inc (m.lines p).val π ∧ S.Inc (m.lines q).val π) ↔
      q≠p ∧ ¬PolarOrientation.Collinear dual p q := by
  rw [m.coplanar_iff,not_or]
  exact and_congr ne_comm Iff.rfl

def noncoplanarEquiv (p : PolarOrientation.Point dual) :
    {q : PolarOrientation.Point dual // q≠p ∧ ¬PolarOrientation.Collinear dual p q} ≃
      {l : S.Line // S.Inc x l ∧ ¬∃π:S.Plane,S.Inc (m.lines p).val π ∧ S.Inc l π} where
  toFun q := ⟨(m.lines q.val).val,(m.lines q.val).property,(m.noncoplanar_iff p q).mpr q.property⟩
  invFun l := ⟨m.lines.symm ⟨l.val,l.property.1⟩,by
    apply (m.noncoplanar_iff p _).mp
    simpa only [Equiv.apply_symm_apply] using l.property.2⟩
  left_inv q := by simp only [Equiv.symm_apply_apply,Subtype.coe_eta]
  right_inv l := by apply Subtype.ext; simp only [Equiv.apply_symm_apply]

theorem noncoplanar_eight (p : PolarOrientation.Point dual) :
    Nat.card {l : S.Line // S.Inc x l ∧ ¬∃π:S.Plane,S.Inc (m.lines p).val π ∧ S.Inc l π}=8 := by
  rw [←Nat.card_congr (m.noncoplanarEquiv p)]
  exact PolarOrientation.noncollinear_eight dual p

theorem lift_alternating (a : A6) : ∃ g : MulAction.stabilizer G x, m.actor g=a.val := by
  apply MonoidHom.mem_range.mp
  rcases m.actor_range with h|h
  · rw [h]; exact a.property
  · rw [h]; trivial

theorem noncoplanar_transporter (p q r : PolarOrientation.Point dual)
    (hq : ¬∃π:S.Plane,S.Inc (m.lines p).val π ∧ S.Inc (m.lines q).val π)
    (hr : ¬∃π:S.Plane,S.Inc (m.lines p).val π ∧ S.Inc (m.lines r).val π) :
    ∃ g : G, g • x=x ∧ g • (m.lines p).val=(m.lines p).val ∧
      g • (m.lines q).val=(m.lines r).val := by
  obtain ⟨a,ha,hq'⟩ := PolarOrientation.a6_noncollinear_transporter dual p q r
    ((m.noncoplanar_iff p q).mp hq) ((m.noncoplanar_iff p r).mp hr)
  obtain ⟨g,hg⟩ := m.lift_alternating a
  refine ⟨g.val,g.property,?_,?_⟩
  · rw [←m.lines_smul,hg]
    exact congrArg (fun p=>(m.lines p).val) ha
  · rw [←m.lines_smul,hg]
    exact congrArg (fun p=>(m.lines p).val) hq'

theorem projection (p : PolarOrientation.Point dual) (l : PolarOrientation.Line dual) :
    ∃ n : S.Line, S.Inc x n ∧ S.Inc n (m.planes l).val ∧
      ∃σ:S.Plane,S.Inc (m.lines p).val σ ∧ S.Inc n σ := by
  obtain ⟨q,hq,hpq⟩ := PolarOrientation.projection dual p l
  exact ⟨(m.lines q).val,(m.lines q).property,(m.incident q l).mpr hq,
    (m.coplanar_iff p q).mpr hpq⟩
end Mark

variable (S)
/-- I.5.9: exactly eight lines through a point are not coplanar with a fixed line. -/
theorem noncoplanar_eight (x : S.Point) (l : S.Line) (hl : S.Inc x l) :
    Nat.card {k : S.Line // S.Inc x k ∧ ¬∃π:S.Plane,S.Inc l π ∧ S.Inc k π}=8 := by
  obtain ⟨dual,⟨m⟩⟩ := exists_mark S x
  simpa only [Equiv.apply_symm_apply] using m.noncoplanar_eight (m.lines.symm ⟨l,hl⟩)

/-- I.5.9: the actual point-line stabilizer is transitive on the eight
noncoplanar lines through the point. -/
theorem noncoplanar_transporter (x : S.Point) (l k n : S.Line)
    (hl : S.Inc x l) (hk : S.Inc x k) (hn : S.Inc x n)
    (hlk : ¬∃π:S.Plane,S.Inc l π ∧ S.Inc k π)
    (hln : ¬∃π:S.Plane,S.Inc l π ∧ S.Inc n π) :
    ∃ g : G, g • x=x ∧ g • l=l ∧ g • k=n := by
  obtain ⟨dual,⟨m⟩⟩ := exists_mark S x
  have h := m.noncoplanar_transporter (m.lines.symm ⟨l,hl⟩) (m.lines.symm ⟨k,hk⟩)
    (m.lines.symm ⟨n,hn⟩)
  simp only [Equiv.apply_symm_apply] at h
  exact h hlk hln

/-- The quadrangle projection used in I.5.9(3ii), stated in the original
point, line and plane incidence. -/
theorem projection (x : S.Point) (k : S.Line) (π : S.Plane)
    (hk : S.Inc x k) (hπ : S.Inc x π) :
    ∃n:S.Line,S.Inc x n ∧ S.Inc n π ∧ ∃σ:S.Plane,S.Inc k σ ∧ S.Inc n σ := by
  obtain ⟨dual,⟨m⟩⟩ := exists_mark S x
  simpa only [Equiv.apply_symm_apply] using m.projection (m.lines.symm ⟨k,hk⟩) (m.planes.symm ⟨π,hπ⟩)

end PolarPointResidues
end Quasithin.I5.DSystem
