module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeOvercomponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour

/-!
# The actual prepared general Ree completion geometry

The model Sylow subgroup lies in both native residual factors. Transport of
the intrinsic solvable residual therefore puts the original source S inside
both original factors, so the source parabolics generate exactly L ∨ O²(H).
Their inverse comparison maps give a faithful completion in that subgroup,
retaining every element of the common Borel. Native local geometry and common
pushout coverings give its valences, nine-path transitivity and girth at least sixteen.

The full normalizer pair normalizes this same join and its ambient centralizer
is trivial, by the established original normalizer conditions. Neither the
factor join nor the normalizer join is asserted to equal G. Compatible extension
to the native model, the source ambient order bound and actual group recognition
remain to be proved before the prepared Ree row gives GlobalExit.

Source: Aschbacher–Smith 5.3.1–4, printed pp.658–659, and F.4.4–6,
printed pp.274–277 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion.GeneralReeFour
variable {G : Type*} [Group G] [Finite G]

private theorem ree_sylow_le_factor
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (i : Fin 2) (s : ReeF4.LargeLocalSeeds.Side)
    (e : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ≃*
      ReeF4.Parabolics.parabolic m s) : sourceS L H ≤ ![L,residual H] i := by
  have hm := d.ree_parameter_positive h hp m i s e
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
  let Q := ReeF4.Parabolics.parabolic m s
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hr := ReeF4.Parabolics.parabolic_solvableResidual_map hm s
  let U := ((sourceS L H).subgroupOf P).map e.toMonoidHom
  have hU : IsPGroup 2 U :=
    (((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.toMonoidHom)
  let S := (ReeFour.sylow m).subtype
    ((ReeFour.sylow_le_localFactor m s).trans (ReeF4.Parabolics.localFactor_le_parabolic m s))
  have hS : (S : Subgroup Q) ≤ solvableResidual Q := by
    intro x hx
    have hxK := ReeFour.sylow_le_localFactor m s hx
    rw [←hr] at hxK
    obtain ⟨y,hy,he⟩ := hxK
    exact (Subtype.ext he : y = x) ▸ hy
  have hn : ¬ 2 ∣ (solvableResidual Q).index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hS))
  have hle : U ≤ solvableResidual Q := IsPGroup.le_normal_of_index_primeTo _ U hU hn
  change ((sourceS L H).subgroupOf P).map e.toMonoidHom ≤ _ at hle
  rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,
    map_le_map_iff_of_injective e.injective] at hle
  have hs := map_mono (f := P.subtype) hle
  rwa [map_subgroupOf_eq_of_le hSP,d.parabolic_residuals h hTH hp i] at hs

/-- In the actual general Ree row the source completion is the perfect factor join. -/
theorem Preparation.ree_parabolics_join
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse) :
    sourceS L H ≤ L ∧ sourceS L H ≤ residual H ∧
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊔
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 = L ⊔ residual H := by
  have hl := ree_sylow_le_factor d h hTH hp m 0 .linear e.left
  have hr := ree_sylow_le_factor d h hTH hp m 1 .suzuki e.right
  refine ⟨hl,hr,?_⟩
  rw [ChapterF.Source.parabolics_generate]
  exact sup_eq_left.mpr (hl.trans le_sup_left)

private def inclusionCompletion {P Q J : Subgroup G} (hgen : P ⊔ Q = J) :
    RankTwoAmalgam.FaithfulCompletion
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right) (G := J) where
  left := inclusion (hgen ▸ le_sup_left)
  right := inclusion (hgen ▸ le_sup_right)
  compatible := rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : J => (z : G)) h
  generated := by
    rw [inclusion_range,inclusion_range,←subgroupOf_sup (hgen ▸ le_sup_left)
      (hgen ▸ le_sup_right),hgen,subgroupOf_self]

/-- The original compatible comparison supplies the literal local completion,
its normalizer action, and both-type nine-path geometry. Ambient generation
and identification with the concrete Ree group are not asserted. -/
theorem Preparation.ree_completion_geometry
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    2*m+1 = n ∧ 0 < m ∧
    (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) ≤
      normalizer ((L ⊔ residual H : Subgroup G) : Set G)) ∧
    centralizer ((L ⊔ residual H : Subgroup G) : Set G) = ⊥ ∧
    ∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ c : Completion m (L ⊔ residual H : Subgroup G),
      (∀ x, (c.left x : G) = (e.left.symm x : G)) ∧
      (∀ x, (c.right x : G) = (e.right.symm x : G)) ∧
      c.middle.range = (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)).subgroupOf
        (L ⊔ residual H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      c.graph.Connected ∧
      (∀ v : c.Vertex, SimpleGraph.PathTransitivePolygon.RootPathTransitive c.graph
        (L ⊔ residual H : Subgroup G) v 9) ∧
      (∀ v : c.Vertex, Nat.card (c.graph.neighborSet v) =
        (if v.type then (2^n)^2 else 2^n) + 1) ∧
      (∀ v : c.Vertex, ∀ p : c.graph.Walk v v, p.IsCycle → 16 ≤ p.length) := by
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  obtain ⟨hn,hm,_⟩ := d.ree_local_structure h hH.1.1.2 hp m e
  have hlocal := d.ree_normalizer_local_conditions h hH hp m (.inr ⟨e⟩)
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hjoin : P ⊔ Q = L ⊔ residual H := (d.ree_parabolics_join h hH.1.1.2 hp m e).2.2
  let c₀ := inclusionCompletion hjoin
  let e' : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.borel m)
        (ReeF4.Parabolics.parabolic m .suzuki)
        (ReeF4.Parabolics.borel_le_parabolic m .linear)
        (ReeF4.Parabolics.borel_le_parabolic m .suzuki))
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right) := e.symm
  let c : Completion m (L ⊔ residual H : Subgroup G) := c₀.comapIso e'
  have hmid : c.middle.range = (P ⊓ Q).subgroupOf (L ⊔ residual H) := by
    rw [RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range]
    have hh : c₀.middle = inclusion (inf_le_left.trans (hjoin ▸ le_sup_left)) := rfl
    rw [hh,inclusion_range]
  have hover : c.left.range ⊓ c.right.range = c.middle.range := by
    rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,hmid]
    change (inclusion (hjoin ▸ le_sup_left)).range ⊓
      (inclusion (hjoin ▸ le_sup_right)).range = _
    rw [inclusion_range,inclusion_range]
    rfl
  refine ⟨hn,hm,normalizer_pair_normalizes hlocal,normalizer_pair_centralizer_eq_bot hlocal,
    e,c,fun _ => rfl,fun _ => rfl,?_,hover,c.connected,c.nine_transitive hm hover,?_,
    c.cycle_length_ge_sixteen hm hover⟩
  · rw [hmid,ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hH.1.1.2)]
  · intro v
    simpa only [hn] using c.card_neighbors hm hover v

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
