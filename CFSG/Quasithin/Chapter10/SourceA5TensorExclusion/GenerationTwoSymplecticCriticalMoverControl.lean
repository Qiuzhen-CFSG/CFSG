module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRepeatedMovers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalQuadraticFixed
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Original small critical images force equal movers

A large backward critical image contains the entire fixed subgroup of the
opposite action in its actual critical commutator. A nontrivial vector of
the backward seed fixed by the common edge therefore centralizes both
selected residual generators. It lies in the vanishing original fixed core,
a contradiction. This excludes the large-image alternative on generated
overlaps; the small-image alternative was already excluded.

Apply this to the literal unequal-mover selector. Every small original
critical image now forces the first two movers to agree. The positioned
backward path and the repeated-path construction consequently discharge
their equal-mover premises. All conjugators, full seeds, kernels and radius
indices remain those of the original geometry.

The large-image starting branch and both terminal distance exclusions are
still required for the full marked plane recognition.
Source: MS93 (5.5), (5.10)--(5.11), printed pp.915--917,922--924;
Aschbacher--Smith 9.3.10, printed pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterC.Sp4Four.DistanceReduction.StrictIndex
open ChapterC.Sp4Four.DistanceReduction.LargeDistance
open scoped commutatorElement
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- A large original critical image contains the entire fixed subgroup
of its opposite action inside the actual critical commutator. -/
theorem original_large_critical_fixed_le_root
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      4 < (Q R a).relIndex (Z R z) →
      Z R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) ≤ ⁅Z R a,Z R z⁆ := by
  intro R geometry a z path hlarge
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have hb : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a path.start_color
        (by rwa [geometry.distance_constant a path.start_color])) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a path.start_color] at hcore
  have hZQ : Z R z ≤ Q R z :=
    (geometry.omega_bound z path.end_color
      (by rw [geometry.distance_constant z path.end_color]; exact hb)).trans (omegaCenter_le _)
  have hZZ : Z R z ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    hZQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))
  have hquad : ⁅Z R z,U R a⁆ ≤ centralizer (Z R z : Set (FreeAmalgam R)) := by
    rw [←c.original_Z_eq_U a path.start_color,commutator_comm]
    exact (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨a,z,path⟩).trans hZZ
  rw [c.original_Z_eq_U a path.start_color,commutator_comm]
  exact original_large_quadratic_fixed_le_commutator R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path.start_color hfixed (Z R z) (path.endpoint_Z_le_start_stabilizer hb) hlarge hquad

/-- Full residual generation excludes a large backward critical image:
a nontrivial edge-fixed vector lies in its commutator and hence is fixed
by both generating subgroups of the neighboring original residual. -/
theorem original_generated_backward_large_root_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1 = t →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) → False := by
  intro R geometry hb a z d t path back hat hdt hbt hgen hlarge
  let w := path.walk.getVert (path.walk.length-2)
  let H := Z R d ⊓ centralizer (Q R t : Set (FreeAmalgam R))
  have hpos : 0 < geometry.b R := by omega
  have rev := c.original_critical_reverse eK geometry hpos back
  have hlarge' : 4 < (Q R d).relIndex (Z R w) := by
    by_contra! hsmall
    have hdata := c.original_small_critical_data eK geometry rev (lt_of_le_of_lt hsmall (by decide : 4 < 16))
    rw [hdata.2.1] at hlarge
    omega
  have hwQt : Z R w ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    change geometry.b R - 1 < geometry.b R
    omega
  have hHroot : H ≤ ⁅Z R d,Z R w⁆ :=
    (inf_le_inf_left _ (centralizer_le hwQt)).trans
      (c.original_large_critical_fixed_le_root eK geometry back hlarge')
  have hwQz : Z R w ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R - (geometry.b R - 2) < geometry.b R
    omega
  have hHZ : H ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    (hHroot.trans (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨d,w,back⟩)).trans (hwQz.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))
  have hHJ : H ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le (LocalPackage.J_le_radical R d t))
  have hHL : H ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hgen.trans
      (sup_le (le_centralizer_iff.mp hHJ) (le_centralizer_iff.mp hHZ)))
  have hHQ : H ≤ Q R a := inf_le_left.trans
    ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q (by omega) a path.start_color))
  have hHbot : H = ⊥ := by
    apply le_bot_iff.mp
    rw [←c.original_fixedCore_eq_bot a path.start_color]
    exact le_inf hHQ hHL
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    back.start_color hdt
  have hpT : IsPGroup 2 (Q R t) := hiT ▸ hodd.isPGroup.map i
  have ht : color R t = true := by
    have h := adjacent_color_ne R hdt
    rw [back.start_color] at h
    cases he : color R t <;> simp_all
  have hZdT : Z R d ≤ Q R t :=
    ((geometry.omega_bound d back.start_color
      (by rw [geometry.distance_constant d back.start_color]; exact hpos)).trans (omegaCenter_le _)).trans
        (Q_le_adjacent_h R ht hdt)
  have hn : Q R t ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
      (Z_normalized R d)
  have hne : Z R d ≠ ⊥ := by
    intro heq
    have hc := c.original_Z_card eK d back.start_color
    rw [heq,card_bot] at hc
    omega
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  let N := (Z R d).subgroupOf (Q R t)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial (Z R d) := (nontrivial_iff_ne_bot _).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hZdT).toEquiv.nontrivial
  let : Fact (IsPGroup 2 (Q R t)) := ⟨hpT⟩
  obtain ⟨x,hxne,hxc⟩ := exists_nontrivial_center_mem_normal N (p := 2)
  have hxH : ((x : Q R t) : FreeAmalgam R) ∈ H := by
    refine ⟨x.property,?_⟩
    intro y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hxc) ⟨y,hy⟩)
  rw [hHbot] at hxH
  exact hxne (Subtype.ext (Subtype.ext (mem_bot.mp hxH)))

/-- A small original critical image forces equality of the first two
full movers. Both possible backward critical-image sizes are excluded
under the actual unequal-mover residual generation. -/
theorem original_small_critical_first_movers_eq
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) := by
  intro R geometry hb a z path hsmall
  by_contra hne
  obtain ⟨ha4,hz4,_⟩ := c.original_small_critical_data eK geometry path hsmall
  obtain ⟨g,hg,back,hbt,hover,hgen,_,hlarge,_⟩ :=
    c.original_unequal_root_backward_large_image eK geometry hb path hne hz4 ha4
  have hlen : 4 < path.walk.length := by rw [path.length_eq_b]; exact hb
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (back.walk.getVert 1) := by
    rw [hbt]
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hat
  have hdtg : Adjacent R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) := by
    rw [hbt]
    exact (adjacent_act_iff R g _ _).mpr hdt
  exact c.original_generated_backward_large_root_impossible eK geometry hb path back
    hatg hdtg rfl hgen hlarge


/-- The actual small-image selector has a large backward critical image
and its root escapes the forward seed, with no equal-mover premise. -/
theorem original_small_critical_positioned_backward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) =
          LocalPackage.J R a (back.walk.getVert 1) ∧
        16 ≤ (Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) ∧
        ¬ ⁅Z R (act R g (path.walk.getVert 2)),Z R (path.walk.getVert (path.walk.length-2))⁆ ≤
          Z R (path.walk.getVert 2) := by
  intro R geometry hb a z path hsmall
  exact c.original_equal_mover_small_critical_backward_large_image eK geometry hb path hsmall
    (c.original_small_critical_first_movers_eq eK geometry hb path hsmall)

open ChapterC.Sp4Four.DistanceReduction.LargeDistance

/-- A small shifted critical root supplies the initial equal-mover branch
itself. Its obstruction to two-mover generation therefore has no independent
mover-equality premise. -/
theorem original_shifted_small_root_not_generated_of_small
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ (s : ℕ → CriticalSegment geometry),
      (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) → ∀ n,
      (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) < 16 →
      ¬ Ltilde R (s n).first ≤
        LocalPackage.J R (s (n+1)).first ((s (n+1)).path.walk.getVert 1) ⊔
          LocalPackage.J R (s n).first ((s n).path.walk.getVert 1) := by
  intro R geometry hb s hs n hsmall
  have heq : MoverAgreement (s (n+1)) 0 := by
    simpa only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      c.original_small_critical_first_movers_eq eK geometry hb (s (n+1)).path hsmall
  exact c.original_shifted_small_root_not_generated eK geometry hb s hs
    ((sequence_first_mover_agreement_iff (by omega) s hs (n+1)).mp heq) n hsmall

/-- Apply the image-improving choices to the original small-image path.
Every repeated mover comparison is now equal, and all shifted small roots
have the full-residual generation obstruction, without extra geometry. -/
theorem original_small_critical_repeated_mover_control
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R → ∀ p : CriticalSegment geometry,
      (Q R p.last).relIndex (Z R p.first) < 16 →
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) ∧
        (∀ n k, 2*k+2 ≤ geometry.b R → MoverAgreement (s (n+k)) k) ∧
        (∀ n, (Q R (s n).last).relIndex (Z R (s n).first) < 16 →
          16 ≤ (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first)) ∧
        (∀ n, (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) < 16 →
          ¬ Ltilde R (s n).first ≤
            LocalPackage.J R (s (n+1)).first ((s (n+1)).path.walk.getVert 1) ⊔
              LocalPackage.J R (s n).first ((s n).path.walk.getVert 1)) ∧
        ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
          ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ ∧
        (4 < (Q R (s 1).first).relIndex (V R (s 2).last) ∨
          4 < (Q R (s 2).first).relIndex (V R (s 2).last ⊓ Q R (s 1).first)) := by
  intro R geometry hb p hsmall
  have heq : MoverAgreement p 0 := by
    simpa only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      c.original_small_critical_first_movers_eq eK geometry hb p.path hsmall
  obtain ⟨s,hs0,hs,_,hagree,hlarge,_,hnot,hcent,hsplit⟩ :=
    c.original_image_improving_mover_sequence eK geometry hb p
  exact ⟨s,hs0,hs,fun n k hk => (hagree n k hk).mpr heq,hlarge,hnot heq,hcent,hsplit⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
