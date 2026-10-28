module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion

/-!
# Geometry of the bad binary module alternatives

The source module estimates discharge all premises of MS93 (2.3), forcing
critical distance four and normality of the critical X commutator at its
midpoint. That commutator lies in X at the initial vertex and thus centralizes
its kernel. The initial kernel escapes the midpoint kernel: containment
would give equality by equal orders and contradict criticality. Simplicity of
the actual midpoint quotient therefore makes the entire two-residual
centralize the commutator.

These are the geometric steps of the binary (3.8) exclusion. They do not
exclude the bad alternatives by themselves or assume the natural structure.
Source: Meierfrankenfeld--Stellmacher (1993), (2.3) and (3.8), pp.857--859,
877--878. Quotients and normality are relative to the actual local stabilizers.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open ModuleAlternatives NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- A normal subgroup of a local stabilizer escaping its kernel contains
its two-residual, by the actual simple quotient. -/
theorem residual_le_of_normal_not_le (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false)
    (N : Subgroup (FreeAmalgam R)) (hN : N ≤ stabilizer R a)
    (hn : (N.subgroupOf (stabilizer R a)).Normal) (hout : ¬ N ≤ Q R a) :
    Ltilde R a ≤ N := by
  let S := stabilizer R a
  let N₀ := N.subgroupOf S
  let Q₀ := (Q R a).subgroupOf S
  let : N₀.Normal := hn
  obtain ⟨frame⟩ := SourceCalculation.exists_frame a ha
  let π := frame.projection source
  have hπ := frame.projection_surjective source
  have hker : π.ker = Q₀ := frame.projection_kernel source
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hnπ : (N₀.map π).Normal := hn.map π hπ
  have htop : N₀.map π = ⊤ := by
    rcases hnπ.eq_bot_or_eq_top with hz | ht
    · have hh := (Subgroup.map_eq_bot_iff N₀).mp hz
      rw [hker] at hh
      exact (hout (fun x hx => hh (show (⟨x, hN hx⟩ : S) ∈ N₀ from hx))).elim
    · exact ht
  have hgen : N₀ ⊔ Q₀ = ⊤ := by
    have hh := congrArg (Subgroup.comap π) htop
    simpa only [comap_map_eq, hker, comap_top] using hh
  have hres : pResidual 2 S ≤ N₀ :=
    sInf_le ⟨hn, isPGroup_quotient_of_sup_eq_top N₀ Q₀
      (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype hgen⟩
  have hh := map_mono (f := S.subtype) hres
  rwa [map_subgroupOf_eq_of_le hN] at hh

/-- Source (2.3)(b), at all oriented edges, from the specified quotient. -/
theorem generation (source : LocalSource L R) : CriticalCriterion.Generation R := by
  intro a t ha hat x hx hout
  let S := stabilizer R a
  let N := conjugatesIn (zpowers x) S
  have hT : Q R t ≤ S := fun _ hy => hy.2 a (adjacent_symm R hat)
  have hN : N ≤ S := conjugatesIn_le _ _ ((zpowers_le.mpr hx).trans hT)
  have hxN : x ∈ N := by
    apply le_iSup (fun g : S => rightConjugate (zpowers x) g) (1 : S)
    exact ⟨x, mem_zpowers x, by simp⟩
  have hLN := residual_le_of_normal_not_le source a ha N hN
    (normal_subgroupOf_of_le_normalizer (conjugatesIn_normalized _ _))
    (fun hh => hout (hh hxN))
  have hQt : Q R a ≤ Q R t := by
    have ht : color R t = true := by
      have hh := adjacent_color_ne R hat
      cases hc : color R t <;> simp_all
    exact Q_le_adjacent_h R ht hat
  apply le_antisymm (sup_le hN hT)
  change stabilizer R a ≤ _
  rw [← source.local_generation a ha]
  exact sup_le (hLN.trans le_sup_left) (hQt.trans le_sup_right)

/-- The endpoint and Frattini clauses of source (2.3)(c) are discharged
by the proved bad-case estimates. -/
theorem commutatorControl (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source) :
    CriticalCriterion.CommutatorControl R geometry := by
  have estimates := badCaseEstimates_of_badCase source geometry hb hbad
  intro a ha a' hc
  obtain ⟨hle, hout⟩ := critical_endpoint_choice source geometry (by omega) a ha a' hc
  exact ⟨Z R a', hle, hout, fun t ht Y hY hPhi =>
    estimates.commutator_bound a ha a' hc t ht.1 ht.2 Y hY hPhi⟩

/-- The auxiliary subgroup in (2.3)(d) is the actual critical X commutator. -/
theorem edgeWitness (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a') :
    CriticalCriterion.EdgeWitness R geometry a t ⁅X R a, X R a'⁆ := by
  have estimates := badCaseEstimates_of_badCase source geometry hb hbad
  refine ⟨(critical_commutator_le_intersection source geometry (by omega) a ha a' hc).trans
    inf_le_left, estimates.auxiliary_normal a ha a' hc t hat ht,
    estimates.auxiliary_not_normal a ha a' hc, ?_⟩
  intro ha₁ d hd htd
  apply estimates.auxiliary_common a ha a' hc t hat ht d hd
  rwa [hd.1, geometry.distance_constant a ha₁]

/-- The first reduction in source (3.8): every bad binary branch has b = 4. -/
theorem distance_eq_four (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source) : geometry.b R = 4 := by
  obtain ⟨a', hc⟩ := criticalPair_exists R (alpha R) (geometry.exists_critical (alpha R) rfl)
  obtain ⟨t, hat, ht⟩ := exists_adjacent_dist_sub_one R (alpha R) a' (by
    rw [hc.1, geometry.distance_constant (alpha R) rfl]
    change 0 < geometry.b R
    omega)
  exact CriticalCriterion.distance_eq_four R source geometry hb (generation source)
    (commutatorControl source geometry hb hbad) (alpha R) rfl a' hc t hat ht _
    (edgeWitness source geometry hb hbad (alpha R) rfl a' hc t hat ht)

/-- The source auxiliary subgroup is normal in the midpoint stabilizer. -/
theorem critical_commutator_normal_midpoint (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hac : (cosetGraph R).dist a c = 2)
    (hca' : (cosetGraph R).dist c a' = 2) :
    ⁅X R a, X R a'⁆ ≤ stabilizer R c ∧
      ((⁅X R a, X R a'⁆).subgroupOf (stabilizer R c)).Normal := by
  have hfour := distance_eq_four source geometry hb hbad
  have hd : (cosetGraph R).dist a a' = 4 :=
    (hc.1.trans (geometry.distance_constant a ha)).trans hfour
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hac
  have ht : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct))
    have h₁ := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected R).dist_triangle (u := t) (v := c) (w := a')
    omega
  exact CriticalCriterion.normal_at_second R source geometry hb (generation source)
    (commutatorControl source geometry hb hbad) a ha a' hc t c hat hct hac (by omega) _
    (edgeWitness source geometry hb hbad a ha a' hc t hat ht)

/-- Along a critical path of length four, the starting kernel escapes the
midpoint kernel. Equal kernel orders rule out containment. -/
theorem critical_kernel_not_le_midpoint (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hcColor : color R c = false)
    (hca' : (cosetGraph R).dist c a' = 2) : ¬ Q R a ≤ Q R c := by
  intro hle
  let := finite_stabilizer R c
  let : Finite (Q R c) := Finite.of_injective
    (inclusion (show Q R c ≤ stabilizer R c from fun _ hx => hx.1)) (inclusion_injective _)
  have heq : Q R a = Q R c := eq_of_le_of_card_ge hle (by
    rw [source.Q_card a ha, source.Q_card c hcColor])
  have hZX : Z R a ≤ X R a := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]; change 0 < geometry.b R; omega)
  have hX : X R a = X R c := congrArg omegaCenter heq
  have hcQ := MS93.X_le_Q_of_dist_lt R geometry (source.edgeCentralizerCondition geometry)
    c hcColor a' (by rw [geometry.distance_constant c hcColor]; change _ < geometry.b R; omega)
  exact hc.2 (hZX.trans (hX.le.trans hcQ))

/-- Source (3.8)'s binary auxiliary subgroup is fixed by the midpoint residual.
Normality in G_c makes its centralizer normal there; that centralizer contains
Q_a, which escapes Q_c, so simplicity forces it to contain Ltilde_c. -/
theorem critical_commutator_le_fixed_midpoint (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hcColor : color R c = false)
    (hac : (cosetGraph R).dist a c = 2) (hca' : (cosetGraph R).dist c a' = 2) :
    ⁅X R a, X R a'⁆ ≤ fixedCore R c := by
  let A := ⁅X R a, X R a'⁆
  let S := stabilizer R c
  obtain ⟨hAS, hAn⟩ := critical_commutator_normal_midpoint source geometry hb hbad a ha a' hc c hac hca'
  have hAX : A ≤ X R a :=
    (critical_commutator_le_intersection source geometry (by omega) a ha a' hc).trans inf_le_left
  have hAQ : A ≤ Q R c := hAX.trans
    (MS93.X_le_Q_of_dist_lt R geometry (source.edgeCentralizerCondition geometry) a ha c (by
      rw [geometry.distance_constant a ha]; change _ < geometry.b R; omega))
  let C := S ⊓ centralizer (A : Set (FreeAmalgam R))
  have hCn : (C.subgroupOf S).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hg),
      mem_normalizer_iff_map_conj_eq.mp
        ((((normal_subgroupOf_iff_le_normalizer hAS).mp hAn).trans
          (normalizer_le_normalizer_centralizer A)) hg)]
  have hQC : Q R a ≤ C := le_inf
    (Q_le_stabilizer_of_dist_le_two a c ha hcColor hac.le)
    ((Q_le_centralizer_X R a).trans (centralizer_le hAX))
  have hLC := residual_le_of_normal_not_le source c hcColor C inf_le_left hCn
    (fun hle => critical_kernel_not_le_midpoint source geometry hb a ha a' hc c hcColor hca'
      (hQC.trans hle))
  exact le_inf hAQ (le_centralizer_iff.mp (hLC.trans inf_le_right))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
