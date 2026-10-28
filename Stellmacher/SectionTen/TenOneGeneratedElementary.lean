module
public import Stellmacher.SectionTen.TenOneGeneratedContainment
public import Theory.Frattini.PGroup

/-!
# The generated elementary subgroup in Stellmacher (10.1)

For the ambient Section Ten context and the offset-two middle vertex, the
actual conjugate closure W of the first-module/terminal-core intersection is
elementary abelian. Consequently its ambient Frattini subgroup is trivial.
The hypotheses are exactly the standing length-three commuting critical-pair
context; no assumption on W or on pairwise commutation is added.

The proved containment W ≤ W₀ puts each generator in every neighboring
core. Distinct neighbor modules have commutators with their own cores equal
to their centers, and those centers intersect trivially by the middle-center
splitting. Thus generators in different neighbor modules commute; generators
in one module commute by (7.5). They have exponent two, which passes to their
closure. The standard finite elementary-abelian Frattini theorem then gives
assertion (2). The final wrappers use the legacy identity-embedding adapter.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.60/PDF p.50 of
`refs/files/stellmacher-n-group.pdf`, proof of (10.1), immediately following
assertion (1).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

private theorem elementary_closure_of_commuting_involutions
    {G : Type u} [Group G] (generators : Set G)
    (hcomm : ∀ x ∈ generators, ∀ y ∈ generators, x * y = y * x)
    (hpow : ∀ x ∈ generators, x ^ 2 = 1) :
    IsElementaryAbelian 2 (Subgroup.closure generators) := by
  let _ : IsMulCommutative (Subgroup.closure generators) :=
    Subgroup.isMulCommutative_closure hcomm
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨element, helement⟩
  apply Subtype.ext
  change element ^ 2 = 1
  induction helement using Subgroup.closure_induction with
  | mem value hvalue => exact hpow value hvalue
  | one => simp
  | mul left right hleft hright ihleft ihright =>
    have hcommute : Commute left right := setLike_mul_comm hleft hright
    rw [hcommute.mul_pow, ihleft, ihright, one_mul]
  | inv value hvalue ih => rw [inv_pow, ih, inv_one]

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem neighbor_seed_commutator_eq_bot
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {left right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent middle left)
    (hright : ctx.Γ.adjacent middle right) (hne : left ≠ right) :
    ⁅VAt ctx.Γ left ⊓ QAt ctx.Γ right, VAt ctx.Γ right ⊓ QAt ctx.Γ left⁆ = ⊥ := by
  obtain ⟨hmiddle, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have horbit (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle vertex) :
      IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
    exact ⟨actor, hactor⟩
  have hfour := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2
  have hcomm (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle vertex) :
      ⁅VAt ctx.Γ vertex, QAt ctx.Γ vertex⁆ = ZAt ctx.Γ vertex :=
    (nine_next_center_and_commutator_of_initial_four
      ctx.toAmbientSectionNineContext.toLocalContext hfour vertex (horbit vertex hadj)).2
  have hdisjoint := (nine_three_center_split ctx.toAmbientSectionNineContext
    hb hmiddle hleft hright hne).2.1
  apply le_antisymm _ bot_le
  apply (le_inf ?_ ?_).trans (le_of_eq hdisjoint.eq_bot)
  · exact (Subgroup.commutator_mono inf_le_left inf_le_right).trans
      (le_of_eq (hcomm left hleft))
  · have hbound := Subgroup.commutator_mono
      (show VAt ctx.Γ left ⊓ QAt ctx.Γ right ≤ QAt ctx.Γ right from inf_le_right)
      (show VAt ctx.Γ right ⊓ QAt ctx.Γ left ≤ VAt ctx.Γ right from inf_le_left)
    rw [Subgroup.commutator_comm (QAt ctx.Γ right) (VAt ctx.Γ right),
      hcomm right hright] at hbound
    exact hbound

private theorem generated_pair_commutes
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor mover : GAt ctx.Γ middle)
    (x y : ↥(VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')) :
    Commute ((actor : G) * (x : G) * (actor : G)⁻¹)
      ((mover : G) * (y : G) * (mover : G)⁻¹) := by
  let left := ctx.Γ.act (actor : G)⁻¹ ctx.criticalPath.firstStep
  let right := ctx.Γ.act (mover : G)⁻¹ ctx.criticalPath.firstStep
  let first := (actor : G) * (x : G) * (actor : G)⁻¹
  let second := (mover : G) * (y : G) * (mover : G)⁻¹
  have hfirst : first ∈ VAt ctx.Γ left := by
    change _ ∈ v ctx.Γ (ctx.Γ.act (actor : G)⁻¹ ctx.criticalPath.firstStep)
    rw [v_act, inv_inv]
    exact Subgroup.mem_map_of_mem _ x.property.1
  have hsecond : second ∈ VAt ctx.Γ right := by
    change _ ∈ v ctx.Γ (ctx.Γ.act (mover : G)⁻¹ ctx.criticalPath.firstStep)
    rw [v_act, inv_inv]
    exact Subgroup.mem_map_of_mem _ y.property.1
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
  by_cases heq : left = right
  · let _ : IsElementaryAbelian 2 (VAt ctx.Γ left) := by
      change IsElementaryAbelian 2 (v ctx.Γ (ctx.Γ.act (actor : G)⁻¹ ctx.criticalPath.firstStep))
      rw [v_act, inv_inv]
      exact IsElementaryAbelian.map (MulAut.conj (actor : G)).toMonoidHom
    have hsecond' : second ∈ VAt ctx.Γ left := heq.symm ▸ hsecond
    exact setLike_mul_comm hfirst hsecond'
  obtain ⟨_, hfirstAdj, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hleftAdj : ctx.Γ.adjacent middle left := by
    have hadj := adjacent_act ctx.Γ (actor : G)⁻¹ hfirstAdj
    have hfix : ctx.Γ.act (actor : G)⁻¹ middle = middle :=
      (Set.ext_iff.mp (ctx.Γ.stabilizer_def _) _).mp
        ((GAt ctx.Γ middle).inv_mem actor.property)
    rwa [hfix] at hadj
  have hrightAdj : ctx.Γ.adjacent middle right := by
    have hadj := adjacent_act ctx.Γ (mover : G)⁻¹ hfirstAdj
    have hfix : ctx.Γ.act (mover : G)⁻¹ middle = middle :=
      (Set.ext_iff.mp (ctx.Γ.stabilizer_def _) _).mp
        ((GAt ctx.Γ middle).inv_mem mover.property)
    rwa [hfix] at hadj
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  have hW : W ≤ NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) :=
    (ten_one_generated_containment ctx middle hpath).trans inf_le_left
  have hfirstW : first ∈ W := Subgroup.subset_closure ⟨actor, x, rfl⟩
  have hsecondW : second ∈ W := Subgroup.subset_closure ⟨mover, y, rfl⟩
  have hfirstCore : first ∈ QAt ctx.Γ right := by
    exact (hW.trans (sInf_le ⟨right,
      (mem_neighborhood_iff_adjacent ctx.Γ).mpr hrightAdj, rfl⟩)) hfirstW
  have hsecondCore : second ∈ QAt ctx.Γ left := by
    exact (hW.trans (sInf_le ⟨left,
      (mem_neighborhood_iff_adjacent ctx.Γ).mpr hleftAdj, rfl⟩)) hsecondW
  have hcomm := Subgroup.commutator_mem_commutator
    (H₁ := VAt ctx.Γ left ⊓ QAt ctx.Γ right)
    (H₂ := VAt ctx.Γ right ⊓ QAt ctx.Γ left)
    ⟨hfirst, hfirstCore⟩ ⟨hsecond, hsecondCore⟩
  rw [neighbor_seed_commutator_eq_bot ctx middle hpath hleftAdj hrightAdj heq,
    Subgroup.mem_bot] at hcomm
  exact commutatorElement_eq_one_iff_commute.mp hcomm

/-- The subgroup W generated in the proof of (10.1) is elementary abelian. -/
public theorem ten_one_generated_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    IsElementaryAbelian 2 (conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)) := by
  rw [conjugateClosure]
  apply elementary_closure_of_commuting_involutions
  · rintro first ⟨actor, x, rfl⟩ second ⟨mover, y, rfl⟩
    exact (generated_pair_commutes ctx middle hpath actor mover x y).eq
  · rintro element ⟨actor, x, rfl⟩
    have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
    let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
      ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
    have hx : (x : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ x.property.1
    have hmapped := congrArg (MulAut.conj (actor : G)) hx
    simpa only [map_pow, map_one, MulAut.conj_apply] using hmapped

/-- The Frattini assertion (2) in the proof of Stellmacher (10.1). -/
public theorem ten_one_generated_frattini
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    frattiniAmbient (conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)) = ⊥ := by
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  let _ : IsElementaryAbelian 2 W := ten_one_generated_elementary ctx middle hpath
  let _ : Fact (IsPGroup 2 W) := ⟨IsElementaryAbelian.isPGroup 2 W⟩
  change frattiniAmbient W = ⊥
  rw [frattiniAmbient, frattini_eq_bot_of_isElementaryAbelian (R := W) (p := 2),
    Subgroup.map_bot]

/-- The original single-carrier context gives the same elementary subgroup. -/
public theorem ten_one_generated_elementary_legacy
    (ctx : SectionTenContext H S0 S P1 P2)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    IsElementaryAbelian 2 (conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)) :=
  ten_one_generated_elementary ctx.toAmbientContext middle hpath

/-- The legacy-context form of the Frattini assertion (2). -/
public theorem ten_one_generated_frattini_legacy
    (ctx : SectionTenContext H S0 S P1 P2)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    frattiniAmbient (conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)) = ⊥ :=
  ten_one_generated_frattini ctx.toAmbientContext middle hpath

end Stellmacher.SectionTen
