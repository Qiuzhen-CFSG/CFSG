module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic

/-!
# The critical exclusion in the joint-normality argument of MS93 (4.4.2)

If the critical commutator lay in the natural subgroup at the second
predecessor e, it would have nontrivial image modulo the fixed core at e.
Source (4.4.1)(ii), applied to the pair (a′,e), then covers Z_e by a
displacement subgroup and the fixed core. The displacement lies in Z_a,
so it centralizes the abelian radius subgroup V_a. Normalization of the
fixed core and its disjointness from U_e show that Z_e centralizes V_a.
The actual natural action then puts V_a in Q_e, contradicting (4.3).

This proves the third input of jointSpan_normalized_of_source_steps.
For its other two local inputs we reduce from the P-orbit span to a single
conjugate of the reverse span. Conjugation by P preserves both the orbit
span and the edge. The seed commutator bounds therefore extend to the
whole orbit using the subgroup commutator preimage inside Q_a.

The two seed bounds still require the local module calculation. The final
assembly below is conditional on precisely these unproved seed bounds;
it does not assert joint normality from the source inputs alone.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, the chain R ≤ H₁H₂ ≤ U_(a′−2).
The fixed core is the source D, and V_a is the full radius-two subgroup.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {a a' : Vertex R}

/-- The final application of (4.4.1) excludes the printed containment
R ≤ U_(a′−2), using the full radius subgroup in (4.3). -/
theorem critical_not_le_terminal_natural [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (p : CriticalPath R geometry a a') :
    ¬ ⁅Z R a, Z R a'⁆ ≤ U R (p.walk.getVert (p.walk.length - 2)) := by
  let e := p.walk.getVert (p.walk.length - 2)
  have hl := p.length_eq_b
  have heven : Even p.walk.length := by
    rw [p.shortest, p.critical.1]
    exact geometry.even a p.start_color
  have he : color R e = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hea' : (cosetGraph R).dist e a' = 2 := by
    dsimp [e]
    rw [p.dist_end]
    omega
  have hae : (cosetGraph R).dist a e = geometry.b R - 2 := by
    dsimp [e]
    rw [p.dist_start (by omega), hl]
  have hZaQe : Z R a ≤ Q R e := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a p.start_color)
    rw [geometry.distance_constant a p.start_color, hae]
    change geometry.b R - 2 < geometry.b R
    omega
  have hVaGe : V R a ≤ stabilizer R e := by
    apply (V_le_iff R p.start_color _).mpr
    intro d hd hda
    apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d e ≤ geometry.b R
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := e)
    rw [hae] at ht
    omega
  have hVeGa : V R e ≤ stabilizer R a := by
    apply (V_le_iff R he _).mpr
    intro d hd hde
    apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d a ≤ geometry.b R
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := e) (w := a)
    rw [SimpleGraph.dist_comm (u := e), hae] at ht
    omega
  intro hR
  have hnotD : ¬ ⁅Z R a', Z R a⁆ ≤ fixedCore R e := by
    intro hD
    apply common.critical_noncommutation a p.start_color a' p.critical
    apply le_bot_iff.mp
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) e he]
    exact le_inf hR ((commutator_comm (Z R a) (Z R a') ▸ hD).trans inf_le_right)
  have hinit : ¬ ⁅Z R a', Q R e⁆ ≤ fixedCore R e :=
    fun h => hnotD ((commutator_mono le_rfl hZaQe).trans h)
  have hex : ∃ x ∈ Z R a, ¬ ⁅localZSpan R a' e, zpowers x⁆ ≤ fixedCore R e := by
    by_contra! h
    apply hnotD
    apply commutator_le.mpr
    intro z hz x hx
    exact h x hx (commutator_mem_commutator (Z_le_localZSpan R a' e hz) (mem_zpowers x))
  obtain ⟨x, hx, hmove⟩ := hex
  have hcover := (hlocal a' e p.end_color he (by rw [SimpleGraph.dist_comm, hea']) hinit).2
    x (hZaQe hx) hmove
  let W := localZSpan R a' e
  have hWGa : W ≤ stabilizer R a :=
    (localZSpan_le_V R (by rw [SimpleGraph.dist_comm, hea'])).trans hVeGa
  have hKZa : ⁅zpowers x, W⁆ ≤ Z R a :=
    (commutator_mono (zpowers_le.mpr hx) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hWGa.trans (Z_normalized R a)))
  let := V_abelian_of_four_lt R p.start_color hb
  have hVV : V R a ≤ centralizer (V R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hKzero : ⁅⁅zpowers x, W⁆, V R a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hKZa.trans ((Z_le_VBall R a 2).trans hVV))
  have hDnorm : Q R e ≤ normalizer (fixedCore R e : Set (FreeAmalgam R)) :=
    (show Q R e ≤ stabilizer R e from fun _ hx => hx.1).trans (fixedCore_normalized R e)
  have hDVa : ⁅fixedCore R e, V R a⁆ ≤ fixedCore R e :=
    le_normalizer_iff_commutator_le_left.mp (hVaGe.trans (fixedCore_normalized R e))
  have hpre : Z R e ≤ commutatorPreimage (Q R e) (V R a) (fixedCore R e) :=
    hcover.trans (sup_le
      (le_commutatorPreimage (hKZa.trans hZaQe) (hKzero.le.trans bot_le))
      (le_commutatorPreimage inf_le_left hDVa))
  have hcommD : ⁅Z R e, V R a⁆ ≤ fixedCore R e :=
    (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hDnorm)
  have hcommU : ⁅Z R e, V R a⁆ ≤ U R e :=
    (commutator_mono le_rfl hVaGe).trans_eq
      (Escape.Initial.Z_commutator_stabilizer source e he)
  have hzero : ⁅Z R e, V R a⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) e he]
    exact le_inf hcommU (hcommD.trans inf_le_right)
  apply common.escape a p.start_color a' p.critical e hea'
    (by rw [hae, p.critical.1, geometry.distance_constant a p.start_color]; change _ + 2 = geometry.b R; omega)
  rw [← common.natural.centralizer e he]
  exact le_inf hVaGe
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (centralizer_le (MS93.U_le_Z e)))


open NormalizerTransfer

/-- The contained calculation for one seed. The containment premise is on
the full orbit span, exactly as in the source; no weaker premise is imposed. -/
@[expose] def ContainedSeedBound (p : CriticalPath R geometry a a') : Prop :=
  ∀ g ∈ stabilizer R a,
    rightConjugate (relativeP p) g ⊔ Z R a' = stabilizer R a →
    rightConjugate (reversePSpan p) g ≤ Q R (p.walk.getVert (p.walk.length - 2)) →
    ⁅rightConjugate (localZSpan R a (p.walk.getVert 2)) g, Z R a'⁆ ≤
      localZSpan R (p.walk.getVert 2) a

/-- The edge calculation for one seed, prior to closing under P-conjugation. -/
@[expose] def EdgeSeedBound (p : CriticalPath R geometry a a') : Prop :=
  ∀ g ∈ stabilizer R a,
    rightConjugate (relativeP p) g ⊔ Z R a' = stabilizer R a →
    ⁅rightConjugate (localZSpan R a (p.walk.getVert 2)) g,
      Z R (p.walk.getVert (p.walk.length - 2))⁆ ≤
      rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g

private theorem conjugate_mul {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    rightConjugate (rightConjugate A g) h = rightConjugate A (g * h) := by
  rw [rightConjugate, rightConjugate, Subgroup.map_map, rightConjugate]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_eq_self {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) : rightConjugate A g = A :=
  mem_normalizer_iff_map_conj_eq.mp ((normalizer (A : Set G)).inv_mem hg)

private theorem conjugate_seed_le_kernel (p : CriticalPath R geometry a a')
    (hb : 4 < geometry.b R) {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    rightConjugate (localZSpan R a (p.walk.getVert 2)) g ≤ Q R a := by
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hQ : localZSpan R a (p.walk.getVert 2) ≤ Q R a :=
    (LocalCommutator.span_le_kernel_intersection hc (p.dist_start (by omega)) hb).trans
      inf_le_left
  exact (map_mono hQ).trans (conjugate_eq_self (Q_normalized R a hg)).le

private theorem relativeP_conjugate_mul (p : CriticalPath R geometry a a')
    {h : FreeAmalgam R} (hh : h ∈ relativeP p) (g : FreeAmalgam R) :
    rightConjugate (relativeP p) (h * g) = rightConjugate (relativeP p) g := by
  rw [← conjugate_mul, conjugate_eq_self ((relativeP p).le_normalizer hh)]

private theorem reversePSpan_conjugate_mul (p : CriticalPath R geometry a a')
    {h : FreeAmalgam R} (hh : h ∈ relativeP p) (g : FreeAmalgam R) :
    rightConjugate (reversePSpan p) (h * g) = rightConjugate (reversePSpan p) g := by
  rw [← conjugate_mul, conjugate_eq_self (reversePSpan_normalized p hh)]

private theorem edge_conjugate_mul (p : CriticalPath R geometry a a')
    {h : FreeAmalgam R} (hh : h ∈ relativeP p) (g : FreeAmalgam R) :
    rightConjugate (edgeCommutator R a (p.walk.getVert 1)) (h * g) =
      rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g := by
  rw [← conjugate_mul, conjugate_eq_self hh.2]

private theorem orbit_commutator_le (p : CriticalPath R geometry a a')
    (hb : 4 < geometry.b R) {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (A D : Subgroup (FreeAmalgam R))
    (hD : Q R a ≤ normalizer D)
    (hseed : ∀ h : relativeP p,
      ⁅rightConjugate (localZSpan R a (p.walk.getVert 2)) ((h : FreeAmalgam R) * g), A⁆ ≤ D) :
    ⁅rightConjugate (reversePSpan p) g, A⁆ ≤ D := by
  have hpre : rightConjugate (reversePSpan p) g ≤ commutatorPreimage (Q R a) A D := by
    rw [reversePSpan, rightConjugate, conjugatesIn, Subgroup.map_iSup]
    apply iSup_le
    intro h
    change rightConjugate (rightConjugate (localZSpan R a (p.walk.getVert 2)) h) g ≤ _
    rw [conjugate_mul]
    exact le_commutatorPreimage
      (conjugate_seed_le_kernel p hb ((stabilizer R a).mul_mem h.property.1 hg))
      (hseed h)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hD)

/-- Lift the contained calculation for a single reverse span to its whole
P-orbit span. The seed premise is the remaining local module calculation. -/
theorem containedDisplacementBound_of_seed
    (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hseed : ContainedSeedBound p) :
    ContainedDisplacementBound p := by
  intro g hg hgen hcontained
  apply orbit_commutator_le p hb hg _ _
    ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
      (localZSpan_normalized R _ a))
  intro h
  have hhg : (h : FreeAmalgam R) * g ∈ stabilizer R a :=
    (stabilizer R a).mul_mem h.property.1 hg
  apply hseed _ hhg (by rw [relativeP_conjugate_mul p h.property]; exact hgen)
  rwa [reversePSpan_conjugate_mul p h.property]

/-- Edge localization for each conjugated seed passes to its P-orbit span.
Q_a centralizes the conjugated edge, so the commutator preimage is a subgroup.
The nontriviality premise of EdgeDisplacementBound is unnecessary for this lift. -/
theorem edgeDisplacementBound_of_seed [Finite M]
    (source : LocalSource L R)
    (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hseed : EdgeSeedBound p) :
    EdgeDisplacementBound p := by
  intro g hg hgen _
  have hl := p.length_eq_b
  have hadj : Adjacent R a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hE : edgeCommutator R a (p.walk.getVert 1) ≤ Z R a :=
    (Escape.Initial.edge_le_natural source a _ p.start_color hadj).trans (MS93.U_le_Z a)
  have hEg : rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g ≤ Z R a :=
    (map_mono hE).trans (conjugate_eq_self (Z_normalized R a hg)).le
  have hQcentral : Q R a ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes a p.start_color))
  apply orbit_commutator_le p hb hg _ _
    ((hQcentral.trans (centralizer_le hEg)).trans (Subgroup.centralizer_le_normalizer _))
  intro h
  have hhg : (h : FreeAmalgam R) * g ∈ stabilizer R a :=
    (stabilizer R a).mul_mem h.property.1 hg
  have hh := hseed _ hhg (by rw [relativeP_conjugate_mul p h.property]; exact hgen)
  rwa [edge_conjugate_mul p h.property] at hh


/-- Supply all three local inputs of the joint-normality assembly after
the two single-seed calculations have been established. The critical exclusion
has no seed, failed-escape, or selection premise. -/
theorem local_bounds_of_seed [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (p : CriticalPath R geometry a a')
    (hcontained : ContainedSeedBound p) (hedge : EdgeSeedBound p) :
    ContainedDisplacementBound p ∧ EdgeDisplacementBound p ∧
      ¬ ⁅Z R a, Z R a'⁆ ≤ U R (p.walk.getVert (p.walk.length - 2)) :=
  ⟨containedDisplacementBound_of_seed p hb hcontained,
    edgeDisplacementBound_of_seed source p hb hedge,
    critical_not_le_terminal_natural common hb hlocal p⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds
