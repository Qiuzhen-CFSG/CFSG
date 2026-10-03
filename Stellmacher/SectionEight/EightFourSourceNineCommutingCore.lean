module

public import Stellmacher.SectionEight.EightFourSourceNineRestrictedCommutation

/-!
# The commuting-core case of Stellmacher (8.4)

Let C be the actual first-step star, next the selected shifted endpoint, and
D the intersection of its center with the first-step core. If C centralizes
D, the first alternative in source (6), now supplied by the proved restricted
commutation theorem, shows that Ltilde centralizes D. Since its retained actor
y conjugates the terminal center to the shifted center, D is precisely the
intersection of those two centers. The intermediate core therefore normalizes
D as well as the shifted center.

An index-two subgroup and its overgroup have trivial quotient action under
their common normalizer. Assuming the shifted-center/core-intersection index
is two, this puts the shifted-center commutator with the intermediate core
inside D. Transport of the initial fixed-commutator identity puts the actual
edge-fixed subgroup in that commutator. Source (9) and edge-fixed strictness
give the contradiction.

The actor-index hypothesis of the final theorem is explicit and is not proved
in this module. Neither the final noncommuting-core case nor (8.4) normality is
asserted. All supplied graph, module and extraction witnesses are retained.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4), printed p.40,
the first of the two last cases in `refs/files/stellmacher-n-group.pdf`.

The local versions retain all graph, witness and source-nine data, with the
same explicit conditional inputs. Original canonical statements are exact
wrappers through the local context and fieldwise configuration conversion.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The common normalizer acts trivially on an index-two quotient. -/
public theorem commutator_le_of_normalizing_index_two
    {H : Type u} [Group H] (Z D Q : Subgroup H)
    (hindex : D.relIndex Z = 2)
    (hQZ : Q ≤ Subgroup.normalizer (Z : Set H))
    (hQD : Q ≤ Subgroup.normalizer (D : Set H)) :
    ⁅Z, Q⁆ ≤ D := by
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro actor hactor point hpoint
  have hconj : actor * point * actor⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hQZ hactor) point).mp hpoint
  have hmem : actor * point * actor⁻¹ ∈ D ↔ point⁻¹ ∈ D :=
    ((Subgroup.mem_normalizer_iff.mp (hQD hactor) point).symm).trans D.inv_mem_iff.symm
  have hproduct := (D.subgroupOf Z).mul_mem_iff_of_index_two hindex
    (a := ⟨actor * point * actor⁻¹, hconj⟩) (b := ⟨point⁻¹, Z.inv_mem hpoint⟩)
  exact hproduct.mpr hmem

/-- The actual edge-fixed subgroup lies in the commutator of the first
center with the second vertex core. -/
public theorem eight_four_edge_fixed_le_core_commutator_local
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
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (hcentral : ZAt ctx.Γ neighbor ≤ CenterAmbient (GAt ctx.Γ neighbor)) :
    F vertex neighbor ≤ ⁅ZAt ctx.Γ vertex, QAt ctx.Γ neighbor⁆ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  obtain ⟨actor, horient | horient⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · have hF := hcov actor cp.a cp.firstStep
    rw [horient.1, horient.2, hbase] at hF
    have hbound : w.oneJFixedPoints S ≤ ⁅ZAt Γ cp.a, QAt Γ cp.firstStep⁆ := by
      rw [← eight_four_initial_fixed_commutator_local ctx hcenter w hbranch]
      exact Subgroup.commutator_mono le_rfl (opposite_closure_le_next_core_local ctx)
    have hmap := Subgroup.map_mono hbound (f := (MulAut.conj actor⁻¹).toMonoidHom)
    rw [Subgroup.map_commutator] at hmap
    have hZ := z_act Γ actor cp.a
    have hQ := SevenSix.q_act Γ actor cp.firstStep
    rw [horient.1] at hZ
    rw [horient.2] at hQ
    change (w.oneJFixedPoints S).conjBy actor⁻¹ ≤
      ⁅(z Γ cp.a).map (MulAut.conj actor⁻¹).toMonoidHom,
        (q Γ cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom⁆ at hmap
    rw [← hF, ← hZ, ← hQ] at hmap
    exact hmap
  · have hZendP : z Γ (Γ.act actor cp.a') ≤ stabilizer Γ neighbor := by
      rw [← horient.1, stabilizer_act, z_act]
      exact Subgroup.map_mono (lemma_seven_four h Γ cp).reverse_containment.1
    have hcomm : ⁅z Γ neighbor, z Γ (Γ.act actor cp.a')⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le hZendP)))
    rw [← horient.1, z_act, z_act, ← Subgroup.map_commutator] at hcomm
    exact (ctx.commutator_ne (Subgroup.map_injective (MulAut.conj actor⁻¹).injective
      (hcomm.trans (Subgroup.map_bot _).symm))).elim

/-- In the commuting-core case, the shifted center meets the first core in
exactly its intersection with the original terminal center. -/
public theorem eight_four_source_nine_core_intersection_of_commuting_local
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
    (hcomm : ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
        QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ⊥) :
    ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep =
        ZAt ctx.Γ ctx.criticalPath.a' ⊓
          ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let C := ⨆ vertex, F vertex cp.firstStep
  let D := ZAt Γ next ⊓ QAt Γ cp.firstStep
  let h := ctx.sectionSeven
  have hrestricted := eight_four_source_nine_restricted_commutation_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hL := (eight_four_source_nine_index_two_of_restricted_commutation_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen hrestricted).2.1
  have hQC : QAt Γ next ≤ Subgroup.centralizer (D : Set H) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact inf_le_left.trans
      (((lemma_seven_three h Γ).center_core next configuration.d
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
          (Γ.adjacent_symm configuration.hadj))).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _)))
  have hLC : configuration.Ltilde ≤ Subgroup.centralizer (D : Set H) := by
    rw [hL]
    exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hQC
  have hDC : D ≤ Subgroup.centralizer (configuration.Ltilde : Set H) :=
    Subgroup.le_centralizer_iff.mp hLC
  have htransport : ZAt Γ next = (ZAt Γ cp.a').conjBy configuration.y := by
    change z Γ (Γ.act configuration.y⁻¹ cp.a') = _
    rw [z_act, inv_inv]
    rfl
  have hDend : D ≤ ZAt Γ cp.a' := by
    intro point hpoint
    have hpointNext : point ∈ ZAt Γ next := hpoint.1
    rw [htransport] at hpointNext
    obtain ⟨preimage, hpreimage, heq⟩ := hpointNext
    have hfix := Subgroup.mem_centralizer_iff.mp (hDC hpoint)
      configuration.y configuration.hy
    have hsame : preimage = point := by
      change configuration.y * preimage * configuration.y⁻¹ = point at heq
      have hsolve := congrArg (fun value => configuration.y⁻¹ * value * configuration.y) heq
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at hsolve
      rw [← hfix, inv_mul_cancel_left] at hsolve
      exact hsolve
    exact hsame ▸ hpreimage
  have hEndCore : ZAt Γ cp.a' ≤ QAt Γ cp.firstStep :=
    (opposite_center_le_opposite_closure_local ctx).trans (opposite_closure_le_next_core_local ctx)
  exact le_antisymm (le_inf hDend inf_le_left)
    (le_inf inf_le_right (inf_le_left.trans hEndCore))

/-- The index-two actor conclusion excludes the commuting-core case. -/
public theorem eight_four_source_nine_noncommuting_core_of_actor_index_local
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
    (hindex : (ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep).relIndex
        (ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) = 2) :
    ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
        QAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ := by
  intro hcomm
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let D := ZAt Γ next ⊓ QAt Γ cp.firstStep
  let h := ctx.sectionSeven
  have hpos := cp.length_pos
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  have hprevious : Γ.adjacent cp.a' previous := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hpathindex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hpathindex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfix : Γ.act configuration.x⁻¹ cp.a' = cp.a' := by
    have hmem := (GAt Γ cp.a').inv_mem (configuration.hL0 configuration.hx)
    change configuration.x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hmem
    rwa [Γ.stabilizer_def] at hmem
  have hmiddle : Γ.adjacent cp.a' configuration.d := by
    have hedge := adjacent_act Γ configuration.x⁻¹ hprevious
    rwa [hfix, ← configuration.hd] at hedge
  have hcentral := eight_four_terminal_neighbor_center_le_local ctx
    hcenter configuration.d hmiddle
  have hQend : QAt Γ configuration.d ≤ GAt Γ cp.a' :=
    ((lemma_seven_three h Γ).sylow_and_core configuration.d cp.a'
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hmiddle)) default).2.2
  have hQnext : QAt Γ configuration.d ≤ GAt Γ next :=
    ((lemma_seven_three h Γ).sylow_and_core configuration.d next
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr configuration.hadj) default).2.2
  have hQZ : QAt Γ configuration.d ≤ Subgroup.normalizer (ZAt Γ next : Set H) :=
    hQnext.trans (stabilizer_le_normalizer_z Γ next)
  have hD := eight_four_source_nine_core_intersection_of_commuting_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen hcomm
  have hQD : QAt Γ configuration.d ≤ Subgroup.normalizer (D : Set H) := by
    change QAt Γ configuration.d ≤ Subgroup.normalizer
      ((ZAt Γ next ⊓ QAt Γ cp.firstStep : Subgroup H) : Set H)
    rw [hD]
    exact (le_inf (hQend.trans (stabilizer_le_normalizer_z Γ cp.a')) hQZ).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hbound : F next configuration.d ≤ D :=
    (eight_four_edge_fixed_le_core_commutator_local ctx hcenter w hbranch F hbase hcov
      next configuration.d (Γ.adjacent_symm configuration.hadj) hcentral).trans
        (commutator_le_of_normalizing_index_two (ZAt Γ next) D (QAt Γ configuration.d)
          hindex hQZ hQD)
  have hinitial : F next configuration.d ≤ GAt Γ cp.a :=
    (hbound.trans inf_le_right).trans
      ((lemma_seven_three h Γ).sylow_and_core cp.firstStep cp.a
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
          (Γ.adjacent_symm cp.firstStep_adj)) default).2.2
  exact eight_four_edge_fixed_not_le_central_vertex_local ctx hcenter w hbranch F hbase hcov
    next configuration.d (Γ.adjacent_symm configuration.hadj) hcentral
      ((le_inf le_rfl hinitial).trans configuration.forward)


/-- Canonical specializations retaining the same actual witness and configuration. -/
public theorem eight_four_edge_fixed_le_core_commutator
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
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (hcentral : ZAt ctx.Γ neighbor ≤ CenterAmbient (GAt ctx.Γ neighbor)) :
    F vertex neighbor ≤ ⁅ZAt ctx.Γ vertex, QAt ctx.Γ neighbor⁆ := by
  exact eight_four_edge_fixed_le_core_commutator_local ctx.toLocalContext hcenter w hbranch F hbase hcov vertex neighbor hadj hcentral

public theorem eight_four_source_nine_core_intersection_of_commuting
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
    (hcomm : ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
        QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ⊥) :
    ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep =
        ZAt ctx.Γ ctx.criticalPath.a' ⊓
          ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') := by
  exact eight_four_source_nine_core_intersection_of_commuting_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen hcomm

public theorem eight_four_source_nine_noncommuting_core_of_actor_index
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
    (hindex : (ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep).relIndex
        (ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) = 2) :
    ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
        QAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ := by
  exact eight_four_source_nine_noncommuting_core_of_actor_index_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen hindex

end Stellmacher.SectionEight
