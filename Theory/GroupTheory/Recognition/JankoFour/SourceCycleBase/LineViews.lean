module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Orbitals
/-!
# The visible-line clique and oval calculations

`lineView` is the source's actual L(x,l). For a point off the line, joining
lines identify it bijectively with the neighboring points on l. The plane
incidence and δ₁/δ₂ counts determine the orbital at each neighbor; source
(5.6) transports that same native label to x. Thus three neighbors produce
a three-line δ₁ clique, while five produce a five-line δ₂ coclique.
These are the incidence and counting steps of (7.3); interpreting the triple
as a singular line and using oval/disc hitting still requires the native
sections 2–3 finite geometry.

Source: AS91 (7.3), with (5.4) and (5.6), p.603.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- The literal L(x,l) in §7: the joining lines from x to its neighbors on l. -/
def lineView (x : Point d.P) (l : Line d.L) : Set (Line d.L) :=
  {m | ∃ u, OnLine d.L u l ∧ Adj d.L x u ∧ OnLine d.L x m ∧ OnLine d.L u m}

theorem lineView_card {x : Point d.P} {l : Line d.L} (hxl : ¬ OnLine d.L x l) :
    (d.lineView x l).ncard = {u | OnLine d.L u l ∧ Adj d.L x u}.ncard := by
  classical
  let f : {u : Point d.P // OnLine d.L u l ∧ Adj d.L x u} → d.lineView x l :=
    fun u => ⟨d.joiningLine u.property.2, u.val, u.property.1, u.property.2,
      d.joiningLine_incident u.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v he
      apply Subtype.ext
      by_contra huv
      have hj : d.joiningLine u.property.2 = d.joiningLine v.property.2 := congrArg Subtype.val he
      have hvm : OnLine d.L v.val (d.joiningLine u.property.2) := hj ▸
        (d.joiningLine_incident v.property.2).2
      have heq := d.line_eq_of_incident huv u.property.1 v.property.1
        (d.joiningLine_incident u.property.2).2 hvm
      exact hxl (heq ▸ (d.joiningLine_incident u.property.2).1)
    · intro m
      obtain ⟨u, hul, hxu, hxm, hum⟩ := m.property
      refine ⟨⟨u, hul, hxu⟩, Subtype.ext ?_⟩
      exact d.line_eq_of_incident hxu.1 (d.joiningLine_incident hxu).1
        (d.joiningLine_incident hxu).2 hxm hum
  exact (Nat.card_eq_of_bijective f hf).symm

theorem lineView_in_plane {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π)
    {m : Line d.L} (hm : m ∈ d.lineView x l) :
    OnLine d.L x m ∧ LineOnPlane d.L m π := by
  obtain ⟨u, hul, hxu, hxm, hum⟩ := hm
  exact ⟨hxm, d.plane_closed x u m π hxu.1 hxm hum hxπ (d.string u l π hul hlπ)⟩

/-- In a plane a nonincident line has either three or five neighbors.
The corresponding orbital at a neighbor is respectively δ₁ or δ₂. -/
theorem lineType_of_line_neighbor_card {x u : Point d.P} {l m : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π)
    (hxl : ¬ OnLine d.L x l) (hul : OnLine d.L u l)
    (hxu : Adj d.L x u) (hxm : OnLine d.L x m) (hum : OnLine d.L u m)
    (i : Fin 5) (hi : i = 1 ∨ i = 2)
    (hc : {v | OnLine d.L v l ∧ Adj d.L x v}.ncard = if i = 1 then 3 else 5) :
    LineType d.residue i u m l := by
  have hmπ := d.plane_closed x u m π hxu.1 hxm hum hxπ (d.string u l π hul hlπ)
  obtain ⟨j, hj, ht⟩ := (d.delta_coplanar u m l hum hul).mp ⟨π, hmπ, hlπ⟩
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp_all
  rcases hj' with rfl | rfl | rfl
  · have he := ((d.delta_zero u m l).mp ht).2
    exact (hxl (he.symm ▸ hxm)).elim
  · rcases hi with rfl | rfl
    · exact ht
    · have hc' := d.delta_one_neighbors u x m l hum hxm hxu.1 ht
      have hbad : (3 : ℕ) = 5 := hc'.symm.trans (by simpa only [show (2 : Fin 5) ≠ 1 from by decide, if_false] using hc)
      exact (by omega : False).elim
  · rcases hi with rfl | rfl
    · have hall := d.delta_two_neighbors u x m l hum hxm hxu.1 ht
      have hs : {v | OnLine d.L v l ∧ Adj d.L x v} = {v | OnLine d.L v l} :=
        Set.ext fun v => ⟨fun hv => hv.1, fun hv => ⟨hv, hall v hv⟩⟩
      rw [hs, d.line_card] at hc
      norm_num at hc
    · exact ht

/-- The clique/coclique calculation in (7.3), with all labels transported
from the actual native trios. The ambient label at u is carried to x by
source (5.6), not by an unmarked residue isomorphism. -/
theorem lineView_pair_type {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π)
    (hxl : ¬ OnLine d.L x l) (i : Fin 5) (hi : i = 1 ∨ i = 2)
    (hc : {v | OnLine d.L v l ∧ Adj d.L x v}.ncard = if i = 1 then 3 else 5)
    {m n : Line d.L} (hm : m ∈ d.lineView x l) (hn : n ∈ d.lineView x l) (hmn : m ≠ n) :
    LineType d.residue i x m n := by
  obtain ⟨u, hul, hxu, hxm, hum⟩ := hm
  obtain ⟨v, hvl, hxv, hxn, hvn⟩ := hn
  have huv : u ≠ v := by
    rintro rfl
    exact hmn (d.line_eq_of_incident hxu.1 hxm hum hxn hvn)
  have huv' : Adj d.L u v := ⟨huv, l, hul, hvl⟩
  have ht := d.lineType_of_line_neighbor_card hxπ hlπ hxl hul hxu hxm hum i hi hc
  exact (d.triangle_labels u x v m l n i (adj_symm hxu) hxv (adj_symm huv')
    hum hxm hul hvl hxn hvn).mp ht

/-- The three visible joining lines form a native δ₁ clique in the point-plane residue. -/
theorem lineView_three_clique {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π) (hxl : ¬ OnLine d.L x l)
    (hc : {v | OnLine d.L v l ∧ Adj d.L x v}.ncard = 3) :
    (d.lineView x l).ncard = 3 ∧
      (∀ m ∈ d.lineView x l, OnLine d.L x m ∧ LineOnPlane d.L m π) ∧
      ∀ m ∈ d.lineView x l, ∀ n ∈ d.lineView x l, m ≠ n → LineType d.residue 1 x m n := by
  exact ⟨(d.lineView_card hxl).trans hc,
    fun _ hm => d.lineView_in_plane hxπ hlπ hm,
    fun _ hm _ hn hmn => d.lineView_pair_type hxπ hlπ hxl 1 (Or.inl rfl)
      (by simpa using hc) hm hn hmn⟩

/-- The five visible joining lines form a native δ₂ coclique, the oval in (7.3.2). -/
theorem lineView_five_coclique {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π)
    (hall : ∀ v, OnLine d.L v l → Adj d.L x v) :
    (d.lineView x l).ncard = 5 ∧
      (∀ m ∈ d.lineView x l, OnLine d.L x m ∧ LineOnPlane d.L m π) ∧
      ∀ m ∈ d.lineView x l, ∀ n ∈ d.lineView x l, m ≠ n → LineType d.residue 2 x m n := by
  have hxl : ¬ OnLine d.L x l := fun hx => (hall x hx).1 rfl
  have hc : {v | OnLine d.L v l ∧ Adj d.L x v}.ncard = 5 := by
    have hs : {v | OnLine d.L v l ∧ Adj d.L x v} = {v | OnLine d.L v l} :=
      Set.ext fun v => ⟨fun hv => hv.1, fun hv => ⟨hv, hall v hv⟩⟩
    rw [hs, d.line_card]
  exact ⟨(d.lineView_card hxl).trans hc,
    fun _ hm => d.lineView_in_plane hxπ hlπ hm,
    fun _ hm _ hn hmn => d.lineView_pair_type hxπ hlπ hxl 2 (Or.inr rfl)
      (by simpa using hc) hm hn hmn⟩

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
