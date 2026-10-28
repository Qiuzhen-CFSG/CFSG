module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlanePencil
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ThreeGeometry
/-!
# The marked outside-line pencil and its two common δ₂ lines

Transport the native shared-octad pencil through the original Todd chart.
Coplanarity and the δ₁ label are both equivalent to incidence with its
specified duad. A line of the plane outside this pencil is δ₂ from exactly
two of its three members; these two lines are mutually δ₁. This supplies
the actual configurations used at each common neighbor in AS91 (7.4).

Source: Aschbacher–Segev (1991), (3.10), (7.4), pp.596,603–604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- The literal lines of a point-plane flag coplanar with an outside line
form a singular pencil, and each has the original δ₁ label. -/
theorem outside_plane_pencil {u : Point d.P} {π : Plane z} {b k : Line d.L}
    (huπ : OnPlane d.P u π) (hbk : LineType d.residue 1 u b k)
    (hkπ : LineOnPlane d.L k π) (hbπ : ¬ LineOnPlane d.L b π) :
    ∃ a : Duad, ∀ l : {l : Line d.L // OnLine d.L u l ∧ LineOnPlane d.L l π},
      (Coplanar d.L b l.val ↔ incident a (d.residue.flagLines u π huπ l)) ∧
      (LineType d.residue 1 u b l.val ↔ incident a (d.residue.flagLines u π huπ l)) := by
  obtain ⟨hub,huk⟩ := lineType_incident hbk
  let σ := d.residue.planesAt u ⟨π,huπ⟩
  let B := d.residue.linesAt u ⟨b,hub⟩
  have hB : ¬ Native.Incident B σ := fun hi => hbπ
    ((d.residue.incidenceAt u ⟨b,hub⟩ ⟨π,huπ⟩).mpr hi)
  have hn : Native.Delta 1 B (d.residue.linesAt u ⟨k,huk⟩) :=
    (d.residue.lineType_one_at u ⟨b,hub⟩ ⟨k,huk⟩).mp hbk
  obtain ⟨_,A,hA⟩ := hn
  obtain ⟨hAB,hAK⟩ := Finset.mem_inter.mp hA
  have hAσ : Native.PlaneOctad σ A :=
    ((d.residue.incidenceAt u ⟨k,huk⟩ ⟨π,huπ⟩).mp hkπ) A hAK
  obtain ⟨A,hAB,hAσ,hit⟩ := Native.outside_pencil σ B hB ⟨A,hAB,hAσ⟩
  obtain ⟨a,ha⟩ := Native.planeOctad_duad σ (ResidueChart.tetradLabel σ) hAσ
  refine ⟨a,?_⟩
  intro l
  have hlσ := (d.residue.incidenceAt u ⟨l.val,l.property.1⟩ ⟨π,huπ⟩).mp l.property.2
  have he : incident a (d.residue.flagLines u π huπ l) ↔
      A ∈ (d.residue.linesAt u ⟨l.val,l.property.1⟩).parts := by
    change incident a (Native.residueEquiv σ _ (d.residue.flagLinesNative u π huπ l)) ↔ _
    rw [Native.residueEquiv_incidence,ha]
    rfl
  have hne : B.parts ≠ (d.residue.linesAt u ⟨l.val,l.property.1⟩).parts := fun hh =>
    hB ((Native.line_parts_injective hh).symm ▸ hlσ)
  have hc : Coplanar d.L b l.val → incident a (d.residue.flagLines u π huπ l) := by
    intro hc
    exact he.mpr (hit _ hlσ ((d.coplanar_iff_native ⟨b,hub⟩ ⟨l.val,l.property.1⟩).mp hc))
  have ht : incident a (d.residue.flagLines u π huπ l) →
      LineType d.residue 1 u b l.val := by
    intro ht
    exact (d.residue.lineType_one_at u ⟨b,hub⟩ ⟨l.val,l.property.1⟩).mpr
      ⟨hne,A,Finset.mem_inter.mpr ⟨hAB,he.mp ht⟩⟩
  have tc : LineType d.residue 1 u b l.val → Coplanar d.L b l.val := fun ht =>
    (d.delta_coplanar u b l.val hub l.property.1).mpr ⟨1,by decide,ht⟩
  exact ⟨⟨hc,fun hh => tc (ht hh)⟩,⟨fun hh => hc (tc hh),ht⟩⟩

private theorem pencil_noncollinear_card (a : Duad) (s : Syntheme) (hs : ¬ incident a s) :
    ((Native.Polar.pencil a).filter (fun t => ¬ synthemeCollinear s t)).card = 2 := by
  revert a s; decide +kernel

/-- The two common δ₂ directions of (3.10), in the same literal plane.
Both are δ₁ from the outside line and from each other. -/
theorem outside_plane_two_lines {u : Point d.P} {π : Plane z} {a b k : Line d.L}
    (huπ : OnPlane d.P u π) (hua : OnLine d.L u a) (haπ : LineOnPlane d.L a π)
    (hbk : LineType d.residue 1 u b k) (hkπ : LineOnPlane d.L k π)
    (hbπ : ¬ LineOnPlane d.L b π) (hab : ¬ Coplanar d.L a b) :
    ∃ m n : {l : Line d.L // OnLine d.L u l ∧ LineOnPlane d.L l π},
      m ≠ n ∧ LineType d.residue 2 u a m.val ∧ LineType d.residue 2 u a n.val ∧
      LineType d.residue 1 u b m.val ∧ LineType d.residue 1 u b n.val ∧
      LineType d.residue 1 u m.val n.val := by
  classical
  obtain ⟨p,hp⟩ := d.outside_plane_pencil huπ hbk hkπ hbπ
  let e := d.residue.flagLines u π huπ
  let A : {l : Line d.L // OnLine d.L u l ∧ LineOnPlane d.L l π} := ⟨a,hua,haπ⟩
  have hA : ¬ incident p (e A) := fun hi => hab
    (by obtain ⟨σ,hb,ha⟩ := (hp A).1.mpr hi; exact ⟨σ,ha,hb⟩)
  obtain ⟨s,t,hst,he⟩ := Finset.card_eq_two.mp (pencil_noncollinear_card p (e A) hA)
  have hs : incident p s ∧ ¬ synthemeCollinear (e A) s := by
    have : s ∈ (Native.Polar.pencil p).filter (fun t => ¬ synthemeCollinear (e A) t) := by simp [he]
    simpa [Native.Polar.pencil] using this
  have ht : incident p t ∧ ¬ synthemeCollinear (e A) t := by
    have : t ∈ (Native.Polar.pencil p).filter (fun t => ¬ synthemeCollinear (e A) t) := by simp [he]
    simpa [Native.Polar.pencil] using this
  have two (s : Syntheme) (hs : incident p s) (hn : ¬ synthemeCollinear (e A) s) :
      LineType d.residue 2 u a (e.symm s).val := by
    have hne : a ≠ (e.symm s).val := by
      intro hh
      have ee : A = e.symm s := Subtype.ext hh
      exact hA (by simpa only [ee,Equiv.apply_symm_apply] using hs)
    have hnot : ¬ LineType d.residue 1 u a (e.symm s).val := by
      intro hh
      have ht := (d.residue.flagLines_collinear_iff u π huπ A (e.symm s)).mpr hh
      exact hn (by simpa only [e,Equiv.apply_symm_apply] using ht)
    obtain ⟨i,hi,hit⟩ := (d.delta_coplanar u a (e.symm s).val hua (e.symm s).property.1).mp
      ⟨π,haπ,(e.symm s).property.2⟩
    fin_cases i
    · exact (hne ((d.delta_zero _ _ _).mp hit).2.symm).elim
    · exact (hnot hit).elim
    · exact hit
    · norm_num at hi
    · norm_num at hi
  refine ⟨e.symm s,e.symm t,e.symm.injective.ne hst,two s hs.1 hs.2,two t ht.1 ht.2,?_,?_,?_⟩
  · exact (hp _).2.mpr (by simpa only [e,Equiv.apply_symm_apply] using hs.1)
  · exact (hp _).2.mpr (by simpa only [e,Equiv.apply_symm_apply] using ht.1)
  · apply (d.residue.flagLines_collinear_iff u π huπ _ _).mp
    change synthemeCollinear (e (e.symm s)) (e (e.symm t))
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    exact (syntheme_collinear_iff_common_duad s t).mpr ⟨hst,p,hs.1,ht.1⟩
end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
