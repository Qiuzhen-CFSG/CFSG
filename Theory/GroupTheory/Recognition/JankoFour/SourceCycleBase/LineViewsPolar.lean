module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ResidueCharts
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.LineViews
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Polar
/-!
# The visible lines in the actual symplectic residue

The point-plane chart identifies the lines visible from an ambient line with
literal incident trios of its sextet residue. Their labels preserve the
original Todd orbital. Consequently the three-neighbor clique in (7.3) is an
actual singular pencil, and the five-neighbor coclique is an oval meeting
each singular pencil exactly once.

Source: Aschbacher–Segev (1991), (2.1.3) and (7.3), pp.592,603.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

noncomputable def lineViewEmbedding {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π) : d.lineView x l ↪ Syntheme where
  toFun m := d.residue.flagLines x π hxπ
    ⟨m.val, d.lineView_in_plane hxπ hlπ m.property⟩
  inj' := by
    intro m n he
    apply Subtype.ext
    exact congrArg (fun q : {k : Line d.L // OnLine d.L x k ∧ LineOnPlane d.L k π} => q.val)
      ((d.residue.flagLines x π hxπ).injective he)

noncomputable def visibleSynthemes {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π) : Finset Syntheme := by
  classical
  let : Fintype (d.lineView x l) := Fintype.ofFinite _
  exact Finset.univ.map (d.lineViewEmbedding hxπ hlπ)

theorem visibleSynthemes_card {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π) :
    (d.visibleSynthemes hxπ hlπ).card = (d.lineView x l).ncard := by
  classical
  let : Fintype (d.lineView x l) := Fintype.ofFinite _
  simp only [visibleSynthemes, Finset.card_map, Finset.card_univ]
  exact Set.fintypeCard_eq_ncard (d.lineView x l)

theorem mem_visibleSynthemes {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π) (s : Syntheme) :
    s ∈ d.visibleSynthemes hxπ hlπ ↔ ∃ m : d.lineView x l, d.lineViewEmbedding hxπ hlπ m = s := by
  classical
  simp [visibleSynthemes]

theorem lineViewEmbedding_collinear_iff {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π) (m n : d.lineView x l) :
    synthemeCollinear (d.lineViewEmbedding hxπ hlπ m) (d.lineViewEmbedding hxπ hlπ n) ↔
      LineType d.residue 1 x m.val n.val := by
  exact d.residue.flagLines_collinear_iff x π hxπ _ _

/-- AS91 (7.3.1): the actual three visible lines form a singular pencil in
 the dual binary symplectic residue, under the original Todd marking. -/
theorem lineView_three_singular {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π) (hxl : ¬ OnLine d.L x l)
    (hc : {v | OnLine d.L v l ∧ Adj d.L x v}.ncard = 3) :
    ∃ a : Duad, d.visibleSynthemes hxπ hlπ = Native.Polar.pencil a := by
  obtain ⟨hcard,_,hpairs⟩ := d.lineView_three_clique hxπ hlπ hxl hc
  apply Native.Polar.clique_three_is_pencil _ ((d.visibleSynthemes_card hxπ hlπ).trans hcard)
  intro s hs t ht hst
  obtain ⟨m,rfl⟩ := (d.mem_visibleSynthemes hxπ hlπ s).mp hs
  obtain ⟨n,rfl⟩ := (d.mem_visibleSynthemes hxπ hlπ t).mp ht
  apply (d.lineViewEmbedding_collinear_iff hxπ hlπ m n).mpr
  exact hpairs m.val m.property n.val n.property
    (fun he => hst (congrArg (d.lineViewEmbedding hxπ hlπ) (Subtype.ext he)))

/-- AS91 (7.3.2): all five neighbors give an oval in that same actual residue. -/
theorem lineView_five_oval {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π)
    (hall : ∀ v, OnLine d.L v l → Adj d.L x v) :
    Native.Polar.Oval (d.visibleSynthemes hxπ hlπ) := by
  obtain ⟨hcard,hinc,hpairs⟩ := d.lineView_five_coclique hxπ hlπ hall
  apply Native.Polar.oval_of_five_coclique _ ((d.visibleSynthemes_card hxπ hlπ).trans hcard)
  intro s hs t ht hst hcol
  obtain ⟨m,rfl⟩ := (d.mem_visibleSynthemes hxπ hlπ s).mp hs
  obtain ⟨n,rfl⟩ := (d.mem_visibleSynthemes hxπ hlπ t).mp ht
  have hne : m.val ≠ n.val := fun he => hst (congrArg (d.lineViewEmbedding hxπ hlπ) (Subtype.ext he))
  have htwo := hpairs m.val m.property n.val n.property hne
  have hone := (d.lineViewEmbedding_collinear_iff hxπ hlπ m n).mp hcol
  obtain ⟨i,_,hi⟩ := d.orbital_partition x m.val n.val (hinc m.val m.property).1 (hinc n.val n.property).1
  have hbad : (1 : Fin 5) = 2 := (hi 1 hone).trans (hi 2 htwo).symm
  exact (by decide : (1 : Fin 5) ≠ 2) hbad

/-- The oval arising from the ambient five-point line meets every singular
pencil, supplying the literal hitting statement used in (7.4) and (7.7). -/
theorem lineView_five_hits_pencil {x : Point d.P} {l : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hlπ : LineOnPlane d.L l π)
    (hall : ∀ v, OnLine d.L v l → Adj d.L x v) (a : Duad) :
    ∃! s, s ∈ d.visibleSynthemes hxπ hlπ ∧ incident a s :=
  Native.Polar.oval_hits_pencil _ (d.lineView_five_oval hxπ hlπ hall) a

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
