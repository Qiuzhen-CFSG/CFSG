module

public import Stellmacher.SectionEight.EightFourSourceNineShiftedCommutation
public import Stellmacher.SectionEight.EightFourStarCentralizerTwoSubgroupCore

/-!
# The shifted-center action after R2 in Stellmacher (8.4)

The shifted terminal center lies in the core of the second path vertex and
therefore in the first-step stabilizer. Source (9) excludes containment in
the first-step core. The actual star-centralizer theorem consequently makes
its action on the initial fixed-subgroup closure nontrivial.

Two local kernels supply the geometric and centralizer steps: a vertex center
lies in any stabilizer within critical distance, and a two-subgroup centralizing
the center at a vertex with a central neighbor lies in that vertex core.
The latter transports the full terminal Sylow-centralizer equality from (7.4),
excluding the reversed edge orientation using endpoint noncommutation.
Neither local kernel assumes Hypothesis Two on a generated subgroup.

A separate conditional reduction shows that commutation of the star's
intersection with the shifted stabilizer forces the first alternative in
source (6). The intersection is then precisely the star's index-two
centralizer. This reduction explicitly retains the restricted-commutation
hypothesis; it does not claim the still-needed R1 argument or final normality.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4), printed p.40,
the paragraphs following (9) in `refs/files/stellmacher-n-group.pdf`.

Both action and conditional index-two conclusions hold for the exact local
source-nine data. The original canonical statements remain fieldwise-data
wrappers, preserving the supplied quotient action and all chosen subgroups.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- A two-subgroup centralizing the center at a vertex with a central neighbor
lies in that vertex's two-core. -/
public theorem eight_four_center_centralizer_two_subgroup_core_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (hcentral : ZAt ctx.Γ neighbor ≤ CenterAmbient (GAt ctx.Γ neighbor))
    (D : Subgroup H) (hDP : D ≤ GAt ctx.Γ vertex)
    (hDtwo : IsPGroup 2 D) (hcomm : ⁅D, ZAt ctx.Γ vertex⁆ = ⊥) :
    D ≤ QAt ctx.Γ vertex := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  have hpos := cp.length_pos
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  have hprevious : Γ.adjacent cp.a' previous := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hindex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  obtain ⟨actor, horient | horient⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1 hprevious hadj
  · let pulled := D.conjBy actor
    have hvertex : Γ.act actor⁻¹ vertex = cp.a' := by
      rw [← horient.1, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
    have hP : pulled ≤ GAt Γ cp.a' := by
      have hmap := Subgroup.map_mono hDP (f := (MulAut.conj actor).toMonoidHom)
      have hstab := stabilizer_act Γ actor⁻¹ vertex
      rw [hvertex, inv_inv] at hstab
      exact hmap.trans_eq hstab.symm
    have htwo : IsPGroup 2 pulled := hDtwo.map (MulAut.conj actor).toMonoidHom
    have hcomm' : ⁅pulled, ZAt Γ cp.a'⁆ = ⊥ := by
      have hmap := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom) hcomm
      rw [Subgroup.map_commutator, Subgroup.map_bot] at hmap
      have hcenter := z_act Γ actor⁻¹ vertex
      rw [hvertex, inv_inv] at hcenter
      change ⁅pulled, (z Γ vertex).map (MulAut.conj actor).toMonoidHom⁆ = ⊥ at hmap
      rwa [← hcenter] at hmap
    obtain ⟨T, hT⟩ := (htwo.comap_subtype (K := GAt Γ cp.a')).exists_le_sylow
    have hTbound : pulled ≤ sylowTwoAmbient (GAt Γ cp.a') T := by
      intro element helement
      exact ⟨⟨element, hP helement⟩, hT helement, rfl⟩
    have hcore : pulled ≤ QAt Γ cp.a' := by
      change pulled ≤ q Γ cp.a'
      rw [← ((lemma_seven_four h Γ cp).commutator_case ctx.commutator_ne).1 T]
      exact le_inf hTbound (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm')
    have hQ := SevenSix.q_act Γ actor⁻¹ vertex
    rw [hvertex, inv_inv] at hQ
    change pulled ≤ q Γ cp.a' at hcore
    rw [hQ] at hcore
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor).injective).mp hcore
  · have hinitial : z Γ (Γ.act actor cp.a) ≤ stabilizer Γ neighbor := by
      rw [← horient.1, stabilizer_act, z_act]
      exact Subgroup.map_mono ((lemma_seven_four h Γ cp).first_containment.1.trans
        (lemma_seven_four h Γ cp).first_containment.2)
    have hzero : ⁅z Γ neighbor, z Γ (Γ.act actor cp.a)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le hinitial)))
    rw [← horient.1, z_act, z_act, ← Subgroup.map_commutator] at hzero
    have hzero' := Subgroup.map_injective (MulAut.conj actor⁻¹).injective
      (hzero.trans (Subgroup.map_bot _).symm)
    exact (ctx.commutator_ne (by rwa [Subgroup.commutator_comm] at hzero')).elim

/-- Centers stabilize every vertex at most the critical distance away. -/
public theorem eight_four_center_le_stabilizer_of_distance_le_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (left right neighbor : ctx.Γ.Vertex) (hneigh : ctx.Γ.adjacent left neighbor)
    (hdist : ctx.Γ.distance left right ≤ ctx.criticalPath.length) :
    ZAt ctx.Γ left ≤ GAt ctx.Γ right := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let distance := Γ.distance left right
  by_cases hzero : distance = 0
  · have heq : left = right := (Γ.distance_zero_iff _ _).mp hzero
    rw [← heq]
    exact ((lemma_seven_three h Γ).center_core left neighbor
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hneigh)).trans
        ((Subgroup.map_subtype_le _).trans (by
          rw [q, Γ.twoCoreAt_def]
          exact Subgroup.map_subtype_le _))
  have hpos : 0 < distance := Nat.pos_of_ne_zero hzero
  obtain ⟨path, hstart, hend, hadj⟩ := Γ.distance_path left right
  let penult := path ⟨distance - 1, by omega⟩
  have hpenult : Γ.distance left penult ≤ distance - 1 := by
    let initialPath : Fin (distance - 1 + 1) → Γ.Vertex :=
      fun index => path ⟨index, by omega⟩
    have hbound := Γ.distance_le_of_path (distance - 1) initialPath
      (fun index => by
        convert hadj ⟨index, by omega⟩ using 1 <;> rfl)
    simpa [initialPath, hstart, penult] using hbound
  have hcore : z Γ left ≤ q Γ penult :=
    SevenSix.critical_minimality Γ cp (by change distance ≤ cp.length at hdist; omega)
  have hlast : Γ.adjacent penult right := by
    have hedge := hadj ⟨distance - 1, by omega⟩
    have hsucc : (⟨distance - 1, by omega⟩ : Fin distance).succ =
        ⟨distance, Nat.lt_succ_self _⟩ := Fin.ext (by simp; omega)
    rw [hsucc, hend] at hedge
    exact hedge
  exact hcore.trans ((lemma_seven_three h Γ).sylow_and_core _ _
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlast) default).2.2

private theorem distance_le_neighbor_distance_add_one
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext H S P1 P2) (left middle right : Γ.Vertex)
    (hadj : Γ.adjacent left middle) :
    Γ.distance left right ≤ Γ.distance middle right + 1 := by
  obtain ⟨path, hstart, hend, hpath⟩ := Γ.distance_path middle right
  let extended : Fin (Γ.distance middle right + 1 + 1) → Γ.Vertex :=
    Fin.cases left path
  have hextended : ∀ index : Fin (Γ.distance middle right + 1),
      Γ.adjacent (extended index.castSucc) (extended index.succ) := by
    intro index
    refine Fin.cases ?_ (fun offset => ?_) index
    · change Γ.adjacent left (path 0)
      rwa [hstart]
    · simpa [extended] using hpath offset
  simpa [extended, hend] using
    Γ.distance_le_of_path (Γ.distance middle right + 1) extended hextended

/-- After R2: the shifted center lies in the second core, escapes the first
core, and acts nontrivially on the actual initial star. -/
public theorem eight_four_source_nine_shifted_center_action_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ZAt ctx.Γ next ≤ QAt ctx.Γ second ∧
      ZAt ctx.Γ next ≤ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      ¬ ZAt ctx.Γ next ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅C, ZAt ctx.Γ next⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  have hlength : 2 < cp.length := hlen
  let second := cp.path ⟨2, by omega⟩
  let next := Γ.act configuration.y⁻¹ cp.a'
  let C := ⨆ vertex, F vertex cp.firstStep
  change ZAt Γ next ≤ QAt Γ second ∧ ZAt Γ next ≤ GAt Γ cp.firstStep ∧
    ¬ ZAt Γ next ≤ QAt Γ cp.firstStep ∧ ⁅C, ZAt Γ next⁆ ≠ ⊥
  have hpos := cp.length_pos
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  have hprevious : Γ.adjacent cp.a' previous := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hindex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfix : Γ.act configuration.x⁻¹ cp.a' = cp.a' := by
    have hmem := (GAt Γ cp.a').inv_mem (configuration.hL0 configuration.hx)
    change configuration.x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hmem
    rw [Γ.stabilizer_def] at hmem
    exact hmem
  have hmiddle : Γ.adjacent cp.a' configuration.d := by
    have hedge := adjacent_act Γ configuration.x⁻¹ hprevious
    rwa [hfix, ← configuration.hd] at hedge
  have hend : Γ.distance cp.a' second ≤ cp.length - 2 := by
    have hbound := SevenSix.path_distance_le Γ cp 2 cp.length (by omega) le_rfl
    rw [cp.path_end, Γ.distance_symm] at hbound
    exact hbound
  have hmiddleDist := distance_le_neighbor_distance_add_one Γ configuration.d cp.a'
    second (Γ.adjacent_symm hmiddle)
  have hnextDist := distance_le_neighbor_distance_add_one Γ next configuration.d second
    (Γ.adjacent_symm configuration.hadj)
  have hdist : Γ.distance next second ≤ cp.length := by omega
  have hsecondAdj : Γ.adjacent cp.firstStep second := by
    have hedge := cp.path_adj ⟨1, by omega⟩
    change Γ.adjacent (cp.path ⟨1, by omega⟩) second at hedge
    rwa [cp.path_first] at hedge
  have hnextP := eight_four_center_le_stabilizer_of_distance_le_local ctx
    next second configuration.d (Γ.adjacent_symm configuration.hadj) hdist
  have htwo : IsPGroup 2 (ZAt Γ next) := by
    let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm configuration.hadj))
    exact IsElementaryAbelian.isPGroup 2 (ZAt Γ next)
  have hcomm : ⁅ZAt Γ next, ZAt Γ second⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact eight_four_source_nine_shifted_centers_commute_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen
  have hcore := eight_four_center_centralizer_two_subgroup_core_local ctx
    second cp.firstStep (Γ.adjacent_symm hsecondAdj) hcenter (ZAt Γ next) hnextP htwo hcomm
  have hfirst : ZAt Γ next ≤ GAt Γ cp.firstStep := hcore.trans
    ((lemma_seven_three h Γ).sylow_and_core second cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hsecondAdj)) default).2.2
  have hnot : ¬ ZAt Γ next ≤ QAt Γ cp.firstStep := by
    intro hle
    apply (eight_four_source_nine_intersection_local ctx hcenter w hbranch
      F hbase hcov hsub configuration).2
    exact hle.trans ((lemma_seven_three h Γ).sylow_and_core cp.firstStep cp.a
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) default).2.2
  refine ⟨hcore, hfirst, hnot, ?_⟩
  intro hzero
  apply hnot
  have hCbase := (eight_four_edge_star_closure_local ctx w F hbase hcov hsub hformula).1
  dsimp only at hCbase
  apply eight_four_star_centralizer_two_subgroup_core_local ctx hcenter w hbranch
    (ZAt Γ next) hfirst htwo
  rw [Subgroup.commutator_comm, ← hCbase]
  exact hzero

private theorem centralizer_eq_index_two_subgroup
    {H : Type u} [Group H] [Finite H]
    (C D P : Subgroup H)
    (hcard : Nat.card C = 2 * Nat.card ↥(C ⊓ P))
    (hcomm : ⁅C ⊓ P, D⁆ = ⊥) (hnoncomm : ⁅C, D⁆ ≠ ⊥) :
    C ⊓ Subgroup.centralizer (D : Set H) = C ⊓ P := by
  let A := C ⊓ P
  let B := C ⊓ Subgroup.centralizer (D : Set H)
  have hAC : A ≤ C := inf_le_left
  have hBC : B ≤ C := inf_le_left
  have hAB : A ≤ B := le_inf inf_le_left
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hAproduct := (A.subgroupOf C).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv] at hAproduct
  change Nat.card A * A.relIndex C = Nat.card C at hAproduct
  have hApositive : 0 < Nat.card A := Nat.card_pos
  have hAindex : A.relIndex C = 2 := by
    change Nat.card C = 2 * Nat.card A at hcard
    nlinarith
  have hBdvd : B.relIndex C ∣ 2 := hAindex ▸ Subgroup.relIndex_dvd_of_le_left C hAB
  have hBindex : B.relIndex C = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hBdvd with hone | htwo
    · have hCB := Subgroup.relIndex_eq_one.mp hone
      exact (hnoncomm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hCB.trans inf_le_right))).elim
    · exact htwo
  have hBproduct := (B.subgroupOf C).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv] at hBproduct
  change Nat.card B * B.relIndex C = Nat.card C at hBproduct
  have hcards : Nat.card B ≤ Nat.card A := by
    rw [hAindex] at hAproduct
    rw [hBindex] at hBproduct
    omega
  exact (Subgroup.eq_of_le_of_card_ge hAB hcards).symm

/-- Restricted commutation forces the exact index-two centralizer and the
first source-(6) alternative; restricted commutation is an explicit input. -/
public theorem eight_four_source_nine_index_two_of_restricted_commutation_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length)
    (hrestricted : ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep) ⊓
      GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')⁆ = ⊥) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ¬ C ≤ GAt ctx.Γ next ∧
      configuration.Ltilde = C ⊔ QAt ctx.Γ next ∧
      C ⊓ Subgroup.centralizer (ZAt ctx.Γ next : Set H) = C ⊓ GAt ctx.Γ next ∧
      Nat.card C = 2 * Nat.card ↥(C ⊓ Subgroup.centralizer (ZAt ctx.Γ next : Set H)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let C := ⨆ vertex, F vertex cp.firstStep
  have haction := (eight_four_source_nine_shifted_center_action_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen).2.2.2
  have hnot : ¬ C ≤ GAt Γ next := by
    intro hle
    apply haction
    have hzero : ⁅C ⊓ GAt Γ next, ZAt Γ next⁆ = ⊥ := hrestricted
    rwa [inf_eq_left.mpr hle] at hzero
  change ¬ C ≤ GAt Γ next ∧ configuration.Ltilde = C ⊔ QAt Γ next ∧ _
  rcases configuration.hcase with hfirst | hsecond
  · have heq := centralizer_eq_index_two_subgroup C (ZAt Γ next) (GAt Γ next)
      hfirst.2 hrestricted haction
    exact ⟨hnot, hfirst.1, heq, by rw [heq]; exact hfirst.2⟩
  · exact (hnot hsecond.2).elim


/-- Canonical specializations retaining the actual source-nine configuration. -/
public theorem eight_four_source_nine_shifted_center_action
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ZAt ctx.Γ next ≤ QAt ctx.Γ second ∧
      ZAt ctx.Γ next ≤ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      ¬ ZAt ctx.Γ next ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅C, ZAt ctx.Γ next⁆ ≠ ⊥ := by
  exact eight_four_source_nine_shifted_center_action_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_index_two_of_restricted_commutation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length)
    (hrestricted : ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep) ⊓
      GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')⁆ = ⊥) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ¬ C ≤ GAt ctx.Γ next ∧
      configuration.Ltilde = C ⊔ QAt ctx.Γ next ∧
      C ⊓ Subgroup.centralizer (ZAt ctx.Γ next : Set H) = C ⊓ GAt ctx.Γ next ∧
      Nat.card C = 2 * Nat.card ↥(C ⊓ Subgroup.centralizer (ZAt ctx.Γ next : Set H)) := by
  exact eight_four_source_nine_index_two_of_restricted_commutation_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen hrestricted

end Stellmacher.SectionEight
