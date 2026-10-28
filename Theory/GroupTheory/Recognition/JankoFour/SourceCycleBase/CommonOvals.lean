module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.CommonPencils
/-!
# The six-point common-neighbor disc

At each point of the common-neighbor clique, the two source lines give two
distinct visible ovals. A common-neighbor direction belongs to either oval
exactly when its point lies on the supporting line; the triangle-label
identity excludes every other point. Each oval therefore meets the direction
set in three. There are exactly two ovals through a direction, so the finite
disc-or-nine theorem applies. The proved bound of seven excludes nine.

The result retains the literal six plane points, the original Todd marking,
and membership in the originally chosen common-neighbor component.

Source: Aschbacher–Segev (1991), (2.1)–(2.2), (3.10), (7.4.1), pp.592,596,603–604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

private theorem lineType_one_ne {u : Point d.P} {m n : Line d.L}
    (ht : LineType d.residue 1 u m n) : m ≠ n := by
  intro he
  obtain ⟨hum,hun⟩ := lineType_incident ht
  have hz := (d.delta_zero u m n).mpr ⟨hum,he.symm⟩
  obtain ⟨i,_,hi⟩ := d.orbital_partition u m n hum hun
  have hh : (0 : Fin 5) = 1 := (hi _ hz).trans (hi _ ht).symm
  exact (by decide : (0 : Fin 5) ≠ 1) hh

/-- In a plane, a δ₁ neighbor of a line visible in all five points cannot
have its second point on one of the same five directions from x. -/
theorem lineView_avoids_delta_one {x v w : Point d.P} {π : Plane z} {m n : Line d.L}
    (hxπ : OnPlane d.P x π) (hmπ : LineOnPlane d.L m π)
    (hall : ∀ t, OnLine d.L t m → Adj d.L x t)
    (hvm : OnLine d.L v m) (hvn : OnLine d.L v n) (hwn : OnLine d.L w n)
    (hvw : v ≠ w) (hxw : Adj d.L x w) (ht : LineType d.residue 1 v m n) :
    d.joiningLine hxw ∉ d.lineView x m := by
  have hwm : ¬ OnLine d.L w m := fun hh => (d.lineType_one_ne ht)
    (d.line_eq_of_incident hvw hvm hh hvn hwn)
  rintro ⟨t,htm,hxt,hxq,htq⟩
  have hwq := (d.joiningLine_incident hxw).2
  have hxl : ¬ OnLine d.L x m := fun hh => (hall x hh).1 rfl
  have hcard : {t | OnLine d.L t m ∧ Adj d.L x t}.ncard = 5 := by
    have he : {t | OnLine d.L t m ∧ Adj d.L x t} = {t | OnLine d.L t m} :=
      Set.ext fun t => ⟨fun hh => hh.1, fun hh => ⟨hh,hall t hh⟩⟩
    rw [he,d.line_card]
  have htwo := d.lineType_of_line_neighbor_card hxπ hmπ hxl htm hxt hxq htq 2
    (Or.inr rfl) (by simpa using hcard)
  have hone : LineType d.residue 1 t m (d.joiningLine hxw) := by
    by_cases he : t = v
    · subst t
      have hen := d.line_eq_of_incident hvw hvn hwn htq hwq
      exact hen ▸ ht
    · have hvt : Adj d.L v t := ⟨Ne.symm he,m,hvm,htm⟩
      have htw : Adj d.L t w := ⟨fun hh => hwm (hh ▸ htm),d.joiningLine hxw,htq,hwq⟩
      exact (d.triangle_labels v t w m n (d.joiningLine hxw) 1 hvt htw
        ⟨Ne.symm hvw,n,hwn,hvn⟩ hvm htm hvn hwn htq hwq).mp ht
  have hone := d.lineType_symm hone
  obtain ⟨i,_,hi⟩ := d.orbital_partition t (d.joiningLine hxw) m htq htm
  have hh : (1 : Fin 5) = 2 := (hi _ hone).trans (hi _ htwo).symm
  exact (by decide : (1 : Fin 5) ≠ 2) hh

/-- The two lines in the same singular pencil give distinct ovals at x. -/
theorem visible_ovals_distinct {x v : Point d.P} {π : Plane z} {m n : Line d.L}
    (hxπ : OnPlane d.P x π) (hmπ : LineOnPlane d.L m π) (hnπ : LineOnPlane d.L n π)
    (hallm : ∀ t, OnLine d.L t m → Adj d.L x t)
    (halln : ∀ t, OnLine d.L t n → Adj d.L x t)
    (hvm : OnLine d.L v m) (hvn : OnLine d.L v n)
    (ht : LineType d.residue 1 v m n) :
    d.visibleSynthemes hxπ hmπ ≠ d.visibleSynthemes hxπ hnπ := by
  classical
  have hw : ∃ w, OnLine d.L w n ∧ w ≠ v := by
    by_contra! hn
    have hs : {w | OnLine d.L w n} ⊆ {v} := fun w hw => hn w hw
    have hh := Set.ncard_le_ncard hs
    rw [d.line_card,Set.ncard_singleton] at hh
    omega
  obtain ⟨w,hwn,hwv⟩ := hw
  let W : d.lineView x n := ⟨d.joiningLine (halln w hwn),w,hwn,halln w hwn,
    d.joiningLine_incident (halln w hwn)⟩
  have hmem := (d.mem_visibleSynthemes hxπ hnπ _).mpr ⟨W,rfl⟩
  intro he
  rw [←he] at hmem
  obtain ⟨Q,hQ⟩ := (d.mem_visibleSynthemes hxπ hmπ _).mp hmem
  have hqe : Q.val = d.joiningLine (halln w hwn) :=
    congrArg Subtype.val ((d.residue.flagLines x π hxπ).injective hQ)
  exact d.lineView_avoids_delta_one hxπ hmπ hallm hvm hvn hwn hwv.symm
    (halln w hwn) ht (hqe ▸ Q.property)

/-- A common-neighbor direction visible from one of the two source lines
comes from a point on that line itself. -/
theorem planeCommon_visible_on_line {x u y v : Point d.P} {π : Plane z} {m : Line d.L}
    (hxπ : OnPlane d.P x π) (hyπ : ¬ OnPlane d.P y π)
    (hu : u ∈ d.planeCommon x y π) (hv : v ∈ d.planeCommon x y π)
    (hum : OnLine d.L u m) (hmπ : LineOnPlane d.L m π)
    (hall : ∀ t, OnLine d.L t m → Adj d.L x t)
    (hbm : LineType d.residue 1 u (d.joiningLine hu.2.2) m)
    (hvis : d.joiningLine hv.2.1 ∈ d.lineView x m) : OnLine d.L v m := by
  by_contra hvm
  have huv : u ≠ v := fun he => hvm (he ▸ hum)
  have hadj := d.common_neighbors_off_plane_clique hyπ hu.1 hv.1
    hu.2.1 hu.2.2 hv.2.1 hv.2.2 huv
  let n := d.joiningLine hadj
  let b := d.joiningLine hu.2.2
  have hun := (d.joiningLine_incident hadj).1
  have hvn := (d.joiningLine_incident hadj).2
  have hyb := (d.joiningLine_incident hu.2.2).1
  have hub := (d.joiningLine_incident hu.2.2).2
  have hnπ := d.plane_closed u v n π huv hun hvn hu.1 hv.1
  have hbπ : ¬ LineOnPlane d.L b π := fun hh => hyπ (d.string y b π hyb hh)
  obtain ⟨a,ha⟩ := d.outside_plane_pencil hu.1 hbm hmπ hbπ
  let M : {l : Line d.L // OnLine d.L u l ∧ LineOnPlane d.L l π} := ⟨m,hum,hmπ⟩
  let N : {l : Line d.L // OnLine d.L u l ∧ LineOnPlane d.L l π} := ⟨n,hun,hnπ⟩
  obtain ⟨σ,hyσ,huσ,hvσ⟩ := d.triangles_in_plane y u v hu.2.2 hadj (adj_symm hv.2.2)
  have hbσ := d.plane_closed y u b σ hu.2.2.1 hyb hub hyσ huσ
  have hnσ := d.plane_closed u v n σ huv hun hvn huσ hvσ
  have hM := (ha M).2.mp hbm
  have hN := (ha N).1.mp ⟨σ,hbσ,hnσ⟩
  have hmn : M ≠ N := by
    intro he
    have hh : m = n := congrArg Subtype.val he
    exact hvm (hh.symm ▸ hvn)
  have ht : LineType d.residue 1 u m n :=
    (d.residue.flagLines_collinear_iff u π hu.1 M N).mp
      ((syntheme_collinear_iff_common_duad _ _).mpr
        ⟨(d.residue.flagLines u π hu.1).injective.ne hmn,a,hM,hN⟩)
  exact d.lineView_avoids_delta_one hxπ hmπ hall hum hun hvn huv hv.2.1 ht hvis

noncomputable def commonLabel {x y : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π) (v : d.planeCommon x y π) : Syntheme :=
  d.residue.flagLines x π hxπ ⟨d.joiningLine v.property.2.1,
    (d.joiningLine_incident v.property.2.1).1,
    d.plane_closed x v.val _ π v.property.2.1.1
      (d.joiningLine_incident v.property.2.1).1
      (d.joiningLine_incident v.property.2.1).2 hxπ v.property.1⟩

noncomputable def commonSynthemes {x y : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π) : Finset Syntheme := by
  classical
  let := Fintype.ofFinite (d.planeCommon x y π)
  exact Finset.univ.image (d.commonLabel (y := y) hxπ)

theorem mem_commonSynthemes {x y : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π) (s : Syntheme) :
    s ∈ d.commonSynthemes (y := y) hxπ ↔ ∃ v : d.planeCommon x y π, d.commonLabel hxπ v = s := by
  classical
  simp [commonSynthemes]

theorem commonLabel_injective {x y : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π)
    (hnone : ¬ ∃ σ, OnPlane d.P x σ ∧ OnPlane d.P y σ) :
    Function.Injective (d.commonLabel (y := y) hxπ) := by
  intro v w he
  apply Subtype.ext
  by_contra hvw
  have hline : d.joiningLine v.property.2.1 = d.joiningLine w.property.2.1 :=
    congrArg Subtype.val ((d.residue.flagLines x π hxπ).injective he)
  have hvq := (d.joiningLine_incident v.property.2.1).2
  have hwq : OnLine d.L w.val (d.joiningLine v.property.2.1) :=
    hline.symm ▸ (d.joiningLine_incident w.property.2.1).2
  have hadj : Adj d.L v.val w.val := ⟨hvw,_,hvq,hwq⟩
  obtain ⟨σ,hyσ,hvσ,hwσ⟩ := d.triangles_in_plane y v.val w.val v.property.2.2
    hadj (adj_symm w.property.2.2)
  have hqσ := d.plane_closed v.val w.val _ σ hvw hvq hwq hvσ hwσ
  exact hnone ⟨σ,d.string x _ σ (d.joiningLine_incident v.property.2.1).1 hqσ,hyσ⟩

theorem commonSynthemes_card {x y : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π)
    (hnone : ¬ ∃ σ, OnPlane d.P x σ ∧ OnPlane d.P y σ) :
    (d.commonSynthemes (y := y) hxπ).card = (d.planeCommon x y π).ncard := by
  classical
  let := Fintype.ofFinite (d.planeCommon x y π)
  rw [commonSynthemes,Finset.card_image_of_injective _ (d.commonLabel_injective hxπ hnone),
    Finset.card_univ]
  exact Set.fintypeCard_eq_ncard _

/-- Each of the source ovals meets the common-neighbor directions in
exactly the three neighbors of y on its supporting line. -/
theorem commonSynthemes_inter_visible {x u y : Point d.P} {π : Plane z} {m : Line d.L}
    (hxπ : OnPlane d.P x π) (hyπ : ¬ OnPlane d.P y π)
    (hu : u ∈ d.planeCommon x y π)
    (hnone : ¬ ∃ σ, OnPlane d.P x σ ∧ OnPlane d.P y σ)
    (hum : OnLine d.L u m) (hmπ : LineOnPlane d.L m π)
    (hall : ∀ t, OnLine d.L t m → Adj d.L x t)
    (hbm : LineType d.residue 1 u (d.joiningLine hu.2.2) m) :
    (d.visibleSynthemes hxπ hmπ ∩ d.commonSynthemes (y := y) hxπ).card = 3 := by
  classical
  let T := {w | OnLine d.L w m ∧ Adj d.L y w}
  let := Fintype.ofFinite T
  let f : T → d.planeCommon x y π := fun w =>
    ⟨w.val,d.string w.val m π w.property.1 hmπ,hall w.val w.property.1,w.property.2⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun q : d.planeCommon x y π => q.val) he)
  have he : d.visibleSynthemes hxπ hmπ ∩ d.commonSynthemes (y := y) hxπ =
      Finset.univ.image (fun w : T => d.commonLabel hxπ (f w)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨hs,hc⟩ := Finset.mem_inter.mp hs
      obtain ⟨v,hv⟩ := (d.mem_commonSynthemes hxπ s).mp hc
      obtain ⟨Q,hQ⟩ := (d.mem_visibleSynthemes hxπ hmπ s).mp hs
      have hqe : d.joiningLine v.property.2.1 = Q.val :=
        congrArg Subtype.val ((d.residue.flagLines x π hxπ).injective (hv.trans hQ.symm))
      have hvm := d.planeCommon_visible_on_line hxπ hyπ hu v.property hum hmπ hall hbm
        (hqe.symm ▸ Q.property)
      refine Finset.mem_image.mpr ⟨⟨v.val,hvm,v.property.2.2⟩,Finset.mem_univ _,?_⟩
      exact hv
    · intro hs
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hs
      refine Finset.mem_inter.mpr ⟨?_,(d.mem_commonSynthemes hxπ _).mpr ⟨f w,rfl⟩⟩
      refine (d.mem_visibleSynthemes hxπ hmπ _).mpr ⟨⟨d.joiningLine (hall w.val w.property.1),
        w.val,w.property.1,hall w.val w.property.1,
        d.joiningLine_incident (hall w.val w.property.1)⟩,rfl⟩
  rw [he]
  have hfi : Function.Injective (fun w : T => d.commonLabel hxπ (f w)) :=
    (d.commonLabel_injective hxπ hnone).comp hf
  rw [Finset.card_image_of_injective _ hfi,Finset.card_univ,Set.fintypeCard_eq_ncard]
  exact d.delta_one_neighbors u y (d.joiningLine hu.2.2) m
    (d.joiningLine_incident hu.2.2).2 (d.joiningLine_incident hu.2.2).1 hu.2.2.1 hbm

private theorem oval_eq_of_two {O M N : Finset Syntheme} {s : Syntheme}
    (hO : Native.Polar.Oval O) (hM : Native.Polar.Oval M) (hN : Native.Polar.Oval N)
    (hMN : M ≠ N) (hsO : s ∈ O) (hsM : s ∈ M) (hsN : s ∈ N) : O = M ∨ O = N := by
  have hsub : {M,N} ⊆ Native.Polar.allOvals.filter (fun Q => s ∈ Q) := by
    intro Q hQ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hQ
    rcases hQ with rfl|rfl
    · exact Finset.mem_filter.mpr ⟨(Native.Polar.mem_allOvals _).mpr hM,hsM⟩
    · exact Finset.mem_filter.mpr ⟨(Native.Polar.mem_allOvals _).mpr hN,hsN⟩
  have he : {M,N} = Native.Polar.allOvals.filter (fun Q => s ∈ Q) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Native.Polar.ovals_through_card,
      Finset.card_pair hMN])
  have hmem : O ∈ ({M,N} : Finset (Finset Syntheme)) :=
    he.symm ▸ Finset.mem_filter.mpr ⟨(Native.Polar.mem_allOvals _).mpr hO,hsO⟩
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hmem

theorem commonLabel_mem_visible {x y : Point d.P} {π : Plane z} {m : Line d.L}
    (hxπ : OnPlane d.P x π) (hmπ : LineOnPlane d.L m π)
    (v : d.planeCommon x y π) (hvm : OnLine d.L v.val m) :
    d.commonLabel hxπ v ∈ d.visibleSynthemes hxπ hmπ := by
  exact (d.mem_visibleSynthemes hxπ hmπ _).mpr
    ⟨⟨d.joiningLine v.property.2.1,v.val,hvm,v.property.2.1,
      d.joiningLine_incident v.property.2.1⟩,rfl⟩

/-- Every touched oval is one of the two source ovals at a common neighbor,
so its intersection with the same-plane directions has exactly three members. -/
theorem commonSynthemes_oval_intersections {x y : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hyπ : ¬ OnPlane d.P y π)
    (hnone : ¬ ∃ σ, OnPlane d.P x σ ∧ OnPlane d.P y σ)
    (hrechoice : ∀ v (hv : v ∈ d.planeCommon x y π), ∃ k,
      OnLine d.L v k ∧ LineOnPlane d.L k π ∧
      LineType d.residue 1 v (d.joiningLine hv.2.2) k) :
    ∀ O, Native.Polar.Oval O → (O ∩ d.commonSynthemes (y := y) hxπ).Nonempty →
      (O ∩ d.commonSynthemes (y := y) hxπ).card = 3 := by
  intro O hO hmeet
  obtain ⟨s,hs⟩ := hmeet
  obtain ⟨hsO,hsS⟩ := Finset.mem_inter.mp hs
  obtain ⟨v,hvs⟩ := (d.mem_commonSynthemes hxπ s).mp hsS
  obtain ⟨k,hvk,hkπ,hbk⟩ := hrechoice v.val v.property
  obtain ⟨m,n,hmn,hmn',hbm,hbn,hallm,halln,_,_⟩ :=
    d.planeCommon_two_lines hxπ v.property hnone hkπ hbk
  have hM := d.lineView_five_oval hxπ m.property.2 hallm
  have hN := d.lineView_five_oval hxπ n.property.2 halln
  have hMN := d.visible_ovals_distinct hxπ m.property.2 n.property.2 hallm halln
    m.property.1 n.property.1 hmn'
  have hsM : s ∈ d.visibleSynthemes hxπ m.property.2 :=
    hvs ▸ d.commonLabel_mem_visible hxπ m.property.2 v m.property.1
  have hsN : s ∈ d.visibleSynthemes hxπ n.property.2 :=
    hvs ▸ d.commonLabel_mem_visible hxπ n.property.2 v n.property.1
  rcases oval_eq_of_two hO hM hN hMN hsO hsM hsN with rfl|rfl
  · exact d.commonSynthemes_inter_visible hxπ hyπ v.property hnone m.property.1
      m.property.2 hallm hbm
  · exact d.commonSynthemes_inter_visible hxπ hyπ v.property hnone n.property.1
      n.property.2 halln hbn

/-- AS91 (7.4.1), retaining the actual six common neighbors, their marked
disc, and membership in the originally specified component. -/
theorem delta_three_common_disc {x u y : Point d.P}
    (ht : d.ternary 2 x u y) (hn : ¬ d.ternary 1 x u y) :
    ∃ (π : Plane z) (hxπ : OnPlane d.P x π) (s : Syntheme),
      (d.planeCommon x y π).ncard = 6 ∧
      d.commonSynthemes (y := y) hxπ = Native.Polar.disc s ∧
      (∀ v ∈ d.planeCommon x y π, v ∈ commonComponent (graph d.L) x u y) ∧
      ∀ v ∈ d.planeCommon x y π, ∀ w ∈ d.planeCommon x y π, v ≠ w → Adj d.L v w := by
  obtain ⟨π,hxπ,hu,hyπ,hnone,hcomp,hrechoice⟩ := d.delta_three_plane_configuration ht hn
  have hne : (d.commonSynthemes (y := y) hxπ).Nonempty :=
    ⟨d.commonLabel hxπ ⟨u,hu⟩,(d.mem_commonSynthemes hxπ _).mpr ⟨⟨u,hu⟩,rfl⟩⟩
  obtain ⟨k,_,hkπ,hbk⟩ := hrechoice u hu
  have hbound := d.planeCommon_card_le_seven hyπ hu hkπ hbk
  have hcard := d.commonSynthemes_card hxπ hnone
  rcases Native.Polar.disc_or_nine_of_oval_intersections _ hne
      (d.commonSynthemes_oval_intersections hxπ hyπ hnone hrechoice) with ⟨s,hs⟩ | h9
  · refine ⟨π,hxπ,s,?_,hs,hcomp,?_⟩
    · rw [←hcard,hs,Native.Polar.disc_card]
    · intro v hv w hw hvw
      exact d.common_neighbors_off_plane_clique hyπ hv.1 hw.1 hv.2.1 hv.2.2 hw.2.1 hw.2.2 hvw
  · omega
end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
