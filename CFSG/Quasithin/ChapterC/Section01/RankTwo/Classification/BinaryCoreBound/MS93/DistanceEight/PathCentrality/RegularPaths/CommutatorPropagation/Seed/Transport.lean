module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Six

/-!
# The fixed core and first backward transport of the terminal commutator

Let W be the transported prescribed P-orbit span and assume W ≤ Q_(a'-2).
Its radius-two origin puts W in Q_(a'-4). A regular turn places Z_a' in
localZSpan (a'-4) (a'-2), so (4.4.1)(i) puts [W,Z_a'] in D_(a'-2).
A turn in the local residual fixes that commutator pointwise; uniqueness
of the intervening vertex in the tree transports the terminal edge to
the edge at a'-4 toward a'-3.

The last theorem applies both deductions to the literal failedSpanCommutator.
The initial assertions R₀ ≰ Z_a and R₀ = U_(a'-1)^(a') remain explicit
premises here. They are the outstanding initial P-orbit calculation, not
consequences of the fixed-core argument.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.4), printed p.894, the first displayed assertions.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private theorem path_distance {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.walk.length) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop i))
    ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := Nat.sub_le_sub_right hj i
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

/-- The relative P-orbit stays within the radius-two subgroup at its origin. -/
theorem prescribedSpan_le_radius {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hb : 2 ≤ geometry.b R) : prescribedSpan p ≤ V R a := by
  have hl := p.length_eq_b
  apply iSup_le
  intro g
  have hd : (cosetGraph R).dist
      (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2)) a ≤ 2 := by
    have hg : Stellmacher.PushingUp.AmalgamGraph.act R g a = a := g.property.1
    have hh := dist_act R (g : FreeAmalgam R) (p.walk.getVert 2) a
    rw [hg, SimpleGraph.dist_comm (u := p.walk.getVert 2), p.dist_start (by omega)] at hh
    exact hh.le
  exact le_iSup_of_le _ (le_iSup_of_le hd le_rfl)

/-- A conjugator fixing the origin preserves the same radius-two bound. -/
theorem transportedSpan_le_radius {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hb : 2 ≤ geometry.b R) {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤ V R a := by
  have hmap : (V R a).map (MulAut.conj g⁻¹).toMonoidHom = V R a :=
    mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized R a ((stabilizer R a).inv_mem hg))
  exact (map_mono (prescribedSpan_le_radius p hb)).trans hmap.le

/-- Failed escape places the literal commutator inside the terminal edge displacement. -/
theorem failedSpanCommutator_le_terminal_edge [Finite M] {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 2 < geometry.b R) (g : FreeAmalgam R)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    failedSpanCommutator p g ≤
      edgeCommutator R a' (p.walk.getVert (p.walk.length - 1)) := by
  have hl := p.length_eq_b
  have ht : color R (p.walk.getVert (p.walk.length - 1)) = true := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    have hne : ¬ color R (p.walk.getVert (p.walk.length - 1)) = false := by
      rw [p.vertex_color (Nat.sub_le _ _), Nat.even_iff]
      rw [Nat.even_iff] at he
      omega
    cases h : color R (p.walk.getVert (p.walk.length - 1)) <;> simp_all
  have hadj : Adjacent R (p.walk.getVert (p.walk.length - 2))
      (p.walk.getVert (p.walk.length - 1)) := by
    apply (cosetGraph_adj R _ _).mp
    convert p.walk.adj_getVert_succ (i := p.walk.length - 2) (by omega) using 1
    congr 1
    omega
  change ⁅_, Z R a'⁆ ≤ ⁅Z R a', _⁆
  rw [commutator_comm]
  exact commutator_mono le_rfl (hfail.trans (Q_le_adjacent_h R ht hadj))

/-- MS93 (4.4.1)(i), applied using the last regular turn, gives the first fixed-core bound. -/
theorem failedSpanCommutator_le_penultimate_fixed {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (hp : HasTurnConjugators R p)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    failedSpanCommutator p g ≤ fixedCore R (p.walk.getVert (p.walk.length - 2)) := by
  have hl := p.length_eq_b
  have he : Even p.walk.length := by
    rw [hl]
    exact geometry.even (alpha R) rfl
  have hc : color R (p.walk.getVert (p.walk.length - 2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hd : color R (p.walk.getVert (p.walk.length - 4)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hdc : (cosetGraph R).dist (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 2)) = 2 := by
    rw [path_distance p (by omega) (Nat.sub_le _ _)]
    omega
  obtain ⟨u, hu, hturn⟩ := hp (p.walk.length - 2)
    ((p.vertex_color (Nat.sub_le _ _)).mp hc) (by omega) (by omega)
  have hturn' : Stellmacher.PushingUp.AmalgamGraph.act R u a' =
      p.walk.getVert (p.walk.length - 4) := by
    simpa only [show p.walk.length - 2 + 2 = p.walk.length by omega,
      show p.walk.length - 2 - 2 = p.walk.length - 4 by omega,
      SimpleGraph.Walk.getVert_length] using hturn
  have hinv : Stellmacher.PushingUp.AmalgamGraph.act R u⁻¹
      (p.walk.getVert (p.walk.length - 4)) = a' := by
    rw [← hturn', ← act_mul, mul_inv_cancel, act_one]
  have hspan : Z R a' ≤ localZSpan R (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 2)) := by
    have hh := le_iSup (fun k : stabilizer R (p.walk.getVert (p.walk.length - 2)) =>
      Z R (Stellmacher.PushingUp.AmalgamGraph.act R k
        (p.walk.getVert (p.walk.length - 4))))
      ⟨u⁻¹, (stabilizer R _).inv_mem hu⟩
    simpa only [hinv, localZSpan] using hh
  have hW : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 4)) := by
    apply (transportedSpan_le_radius p (by omega) hg).trans
    apply V_le_Q_of_dist_add_two_lt R p.start_color
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  change ⁅_, Z R a'⁆ ≤ _
  rw [commutator_comm]
  exact (commutator_mono hspan (le_inf hW hfail)).trans
    (span_kernel_intersection_le_fixed (by omega) hlocal hd hc hdc)

private theorem midpoint_unique (geometry : Geometry R) {a c t u : Vertex R}
    (hd : (cosetGraph R).dist a c = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hau : Adjacent R a u) (hcu : Adjacent R c u) : t = u := by
  let w : (cosetGraph R).Walk a c := .cons ((cosetGraph_adj R _ _).mpr hat)
    (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct)) .nil)
  let v : (cosetGraph R).Walk a c := .cons ((cosetGraph_adj R _ _).mpr hau)
    (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R hcu)) .nil)
  have hw : w.length = (cosetGraph R).dist a c := hd.symm
  have hv : v.length = (cosetGraph R).dist a c := hd.symm
  have hh := (geometry.tree.isAcyclic.subsingleton_path a c).elim
    ⟨w, w.isPath_of_length_eq_dist hw⟩ ⟨v, v.isPath_of_length_eq_dist hv⟩
  exact congrArg (fun q : (cosetGraph R).Path a c => q.val.getVert 1) hh

/-- A residual turn fixes K pointwise and transports both vertices of its terminal edge. -/
theorem preceding_edge_of_terminal_and_fixed [Finite M] (source : LocalSource L R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hb : 6 < geometry.b R) (hp : HasTurnConjugators R p)
    {K : Subgroup (FreeAmalgam R)}
    (hK : K ≤ fixedCore R (p.walk.getVert (p.walk.length - 2)))
    (hE : K = edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))) :
    K = edgeCommutator R (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 3)) := by
  have hl := p.length_eq_b
  have he : Even p.walk.length := by
    rw [hl]
    exact geometry.even (alpha R) rfl
  have hc : color R (p.walk.getVert (p.walk.length - 2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hdc : (cosetGraph R).dist (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 2)) = 2 := by
    rw [path_distance p (by omega) (Nat.sub_le _ _)]
    omega
  obtain ⟨u, hu, hturn⟩ := hp (p.walk.length - 2)
    ((p.vertex_color (Nat.sub_le _ _)).mp hc) (by omega) (by omega)
  have hturn' : Stellmacher.PushingUp.AmalgamGraph.act R u a' =
      p.walk.getVert (p.walk.length - 4) := by
    simpa only [show p.walk.length - 2 + 2 = p.walk.length by omega,
      show p.walk.length - 2 - 2 = p.walk.length - 4 by omega,
      SimpleGraph.Walk.getVert_length] using hturn
  obtain ⟨l, hlL, hld⟩ := exists_residual_turn source hc
    (by rw [SimpleGraph.dist_comm]; exact hdc) hu hturn'
  have hlc : Stellmacher.PushingUp.AmalgamGraph.act R l
      (p.walk.getVert (p.walk.length - 2)) = p.walk.getVert (p.walk.length - 2) :=
    Ltilde_le_stabilizer _ hlL
  have hadj (i j : ℕ) (hj : j = i + 1) (hbound : i < p.walk.length) :
      Adjacent R (p.walk.getVert i) (p.walk.getVert j) := by
    rw [hj]
    exact (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ hbound)
  have hlast : Adjacent R a' (p.walk.getVert (p.walk.length - 1)) := by
    have hh := adjacent_symm R (hadj (p.walk.length - 1) p.walk.length (by omega) (by omega))
    simpa only [SimpleGraph.Walk.getVert_length] using hh
  have hmiddle : Stellmacher.PushingUp.AmalgamGraph.act R l
      (p.walk.getVert (p.walk.length - 1)) = p.walk.getVert (p.walk.length - 3) := by
    apply midpoint_unique (geometry := geometry) hdc
    · simpa only [hld] using (adjacent_act_iff R l _ _).mpr hlast
    · simpa only [hlc] using (adjacent_act_iff R l _ _).mpr
        (hadj (p.walk.length - 2) (p.walk.length - 1) (by omega) (by omega))
    · exact hadj _ _ (by omega) (by omega)
    · exact adjacent_symm R (hadj (p.walk.length - 3) (p.walk.length - 2) (by omega) (by omega))
  have hfix (x : FreeAmalgam R) (hx : x ∈ K) : (MulAut.conj l⁻¹) x = x := by
    have hh := (hK hx).2 l⁻¹ ((Ltilde R _).inv_mem hlL)
    change l⁻¹ * x * (l⁻¹)⁻¹ = x
    rw [hh, mul_inv_cancel_right]
  have hmap : K.map (MulAut.conj l⁻¹).toMonoidHom = K := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hfix x hx).symm ▸ hx
    · intro x hx
      exact ⟨x, hx, hfix x hx⟩
  calc
    K = K.map (MulAut.conj l⁻¹).toMonoidHom := hmap.symm
    _ = (edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))).map
        (MulAut.conj l⁻¹).toMonoidHom := congrArg _ hE
    _ = edgeCommutator R (p.walk.getVert (p.walk.length - 4))
        (p.walk.getVert (p.walk.length - 3)) := by
      rw [← edgeCommutator_act, hld, hmiddle]

/-- Assemble the terminal seed once the two initial P-orbit assertions have been proved. The fixed-core and preceding-edge fields are constructed here. -/
theorem seed_of_initial_calculation [Finite M] (source : LocalSource L R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (hp : HasTurnConjugators R p)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hnot : ¬ failedSpanCommutator p g ≤ Z R a)
    (hE : failedSpanCommutator p g =
      edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))) :
    TerminalPropagationSeed p (failedSpanCommutator p g) := by
  have hD := failedSpanCommutator_le_penultimate_fixed p hb hlocal hp hg hfail
  exact ⟨hnot, hE, hD, preceding_edge_of_terminal_and_fixed source p hb hp hD hE⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
