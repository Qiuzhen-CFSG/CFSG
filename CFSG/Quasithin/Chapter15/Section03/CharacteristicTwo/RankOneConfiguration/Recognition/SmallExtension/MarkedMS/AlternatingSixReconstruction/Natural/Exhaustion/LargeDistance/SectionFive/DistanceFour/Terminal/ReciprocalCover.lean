module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalFactorization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalExclusionFF
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalExclusionCentral
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalMarking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Structure

/-!
# The reciprocal FF quotient as a central cover of the moved radius

Restrict the literal section coordinates on (Vcirc B)/B to the moved radius
inside its original finite stabilizer. The restriction is onto because the
numerator is Vcirc B; its kernel is central because B centralizes Vcirc.
Full residual movement and fixedness of the moved derived subgroup transport
through the stabilizer inclusion. The original symmetric marking then gives
the FF central-cover bound, with no new coordinates or action assumptions.

On a large critical path the same moved derived subgroup has order greater
than two. Combining this with its FF bound excludes the actual reciprocal
witness and supplies the terminal consumer for the large-path construction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10) and (5.12)(2), printed pp.880,926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem reciprocal_moving_cover_data
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (stabilizer d.radical a) W)
    (sec : BinaryConjugationSection (stabilizer d.radical a)
      (reciprocalMovedNumerator h d a)
      (B d.radical a ((replacementGeometry h d).Z_normal a)) ρ) :
    let P := (Vcirc d.radical a).subgroupOf (stabilizer d.radical a)
    letI : P.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
    ∃ q : P →* Multiplicative W,
      Function.Surjective q ∧ q.ker ≤ center P ∧
      (∀ g x, (q (MulAut.conjNormal g x)).toAdd = ρ g (q x).toAdd) ∧
      ⁅P,pResidual 2 (stabilizer d.radical a)⁆ = P ∧
      ⁅P,P⁆ ≤ centralizer (pResidual 2 (stabilizer d.radical a) : Set _) := by
  let H := stabilizer d.radical a
  let P := (Vcirc d.radical a).subgroupOf H
  let M := reciprocalMovedNumerator h d a
  let B₀ := B d.radical a ((replacementGeometry h d).Z_normal a)
  let : P.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
  have hPV : Vcirc d.radical a ≤ V d.radical a :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hPQ := hPV.trans (V_le_Q d.radical (geometry := replacementGeometry h d) ha hb)
  have hPH : Vcirc d.radical a ≤ H := hPQ.trans (fun _ hx => hx.1)
  have hPM : Vcirc d.radical a ≤ M := le_sup_left
  let i : P →* M := {
    toFun := fun x => ⟨x.val.val,hPM x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let q := sec.coordinates.comp i
  have hq : Function.Surjective q := by
    have hsup : (Vcirc d.radical a).subgroupOf M ⊔ B₀.subgroupOf M = ⊤ := by
      rw [←subgroupOf_sup hPM (show B₀ ≤ M from le_sup_right)]
      exact subgroupOf_self _
    have hB : (B₀.subgroupOf M).map sec.coordinates = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [sec.kernel_eq]
    have hmap := congrArg (Subgroup.map sec.coordinates) hsup
    rw [Subgroup.map_sup,hB,sup_bot_eq,map_top_of_surjective _ sec.onto] at hmap
    intro w
    have hw : w ∈ ((Vcirc d.radical a).subgroupOf M).map sec.coordinates := by
      rw [hmap]; trivial
    obtain ⟨v,hv,hvw⟩ := hw
    exact ⟨⟨⟨v,hPH hv⟩,hv⟩,hvw⟩
  have hker : q.ker ≤ center P := by
    intro x hx
    have hxB : (x.val : FreeAmalgam d.radical) ∈ B₀ :=
      (sec.coordinates_eq_one_iff (i x)).mp hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact reciprocal_B_centralizes_moving hb ha hfixed hxB y.val y.property
  have hact (g : H) (x : P) :
      (q (MulAut.conjNormal g x)).toAdd = ρ g (q x).toAdd :=
    sec.equivariant g (i x)
  have hmapP : P.map H.subtype = Vcirc d.radical a := map_subgroupOf_eq_of_le hPH
  have hfull : ⁅P,pResidual 2 H⁆ = P := by
    apply map_injective H.subtype_injective
    rw [map_commutator,hmapP]
    exact SourceReduction.Radius.moving_full_commutation h d hb a ha
  have hfix : ⁅P,P⁆ ≤ centralizer (pResidual 2 H : Set H) := by
    intro x hx l hl
    have hx' : (x : FreeAmalgam d.radical) ∈ ⁅Vcirc d.radical a,Vcirc d.radical a⁆ := by
      have hh := mem_map_of_mem H.subtype hx
      rwa [map_commutator,hmapP] at hh
    have he := (hfixed (commutator_mono hPV hPQ hx')).2
      (l : FreeAmalgam d.radical) (mem_map_of_mem H.subtype hl)
    exact Subtype.ext he
  exact ⟨q,hq,hker,hact,hfull,hfix⟩

private theorem reciprocal_cover_bound_of_marking
    {J D W : Type*} [Group J] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (P : Subgroup J) [P.Normal]
    (π : J →* Equiv.Perm (Fin 6)) (hπ : Function.Surjective π)
    (hπL : (pResidual 2 J).map π = alternatingGroup (Fin 6))
    (φ : J →* D) (E : D ≃* Equiv.Perm (Fin 6))
    (hE : ∀ g, E (φ g) = π g)
    (ρ : Representation (ZMod 2) D W) (hff : IsFFModule ρ)
    (q : P →* Multiplicative W) (hq : Function.Surjective q)
    (hker : q.ker ≤ center P)
    (hact : ∀ g x, (q (MulAut.conjNormal g x)).toAdd = ρ (φ g) (q x).toAdd)
    (hfull : ⁅P,pResidual 2 J⁆ = P)
    (hfix : ⁅P,P⁆ ≤ centralizer (pResidual 2 J : Set J))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6))) :
    Nat.card (_root_.commutator P) ≤ 2 := by
  let σ := ρ.comp E.symm.toMonoidHom
  have hffσ : IsFFModule σ := by
    apply IsFFModule.map_equivariant ρ σ E.toMonoidHom E.injective
      (LinearEquiv.refl (ZMod 2) _) _ hff
    intro g w
    change ρ g w = ρ (E.symm (E g)) w
    rw [E.symm_apply_apply]
  have hactσ (g : J) (x : P) :
      (q (MulAut.conjNormal g x)).toAdd = σ (π g) (q x).toAdd := by
    exact (hact g x).trans (by
      change ρ (φ g) (q x).toAdd = ρ (E.symm (π g)) (q x).toAdd
      rw [←hE g,E.symm_apply_apply])
  exact reciprocal_ff_central_cover_derived_le_two P π hπ hπL σ
    q hq hker hactσ hfull hfix hsq hffσ

variable (s : FullSymmetricAction h e hz hn d)

include s in
/-- The literal reciprocal FF section bounds the derived moved radius by
two. The original stabilizer quotient supplies its symmetric actor. -/
theorem reciprocal_moving_derived_le_two_of_ff
    (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hff : ReciprocalMovedFF (h := h) hb a ha hfixed) :
    Nat.card (⁅Vcirc d.radical a,Vcirc d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  let H := stabilizer d.radical a
  let P := (Vcirc d.radical a).subgroupOf H
  let M := reciprocalMovedNumerator h d a
  let B₀ := B d.radical a ((replacementGeometry h d).Z_normal a)
  let := Q_normal d.radical a
  let := reciprocal_B_normal_moved (h := h) hb ha
  let := reciprocal_moved_quotient_elementary_of_fixed (h := h) hb ha hfixed
  let := finite_stabilizer d.radical a
  let : Finite M := Finite.of_injective
    (inclusion ((reciprocal_moved_numerator_le_radius (h := h) hb ha).trans
      ((V_le_Q d.radical (geometry := replacementGeometry h d) ha hb).trans (fun _ hx => hx.1))))
    (inclusion_injective _)
  let : P.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
  obtain ⟨ρ,sec,hFF,hcoordinates⟩ := hff
  obtain ⟨π,hπ,hπker,hπL,E,hE,hsq⟩ := reciprocal_vertex_actor_coordinates s hc a ha
  obtain ⟨q,hq,hker,hact,hfull,hfix⟩ := reciprocal_moving_cover_data hb ha hfixed
    (ρ.comp (QuotientGroup.mk' ((Q d.radical a).subgroupOf H))) sec
  have hbound := reciprocal_cover_bound_of_marking P π hπ hπL
    (QuotientGroup.mk' ((Q d.radical a).subgroupOf H)) E hE ρ hFF
    q hq hker hact hfull hfix hsq
  have hPV : Vcirc d.radical a ≤ V d.radical a :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hPH : Vcirc d.radical a ≤ H := hPV.trans
    ((V_le_Q d.radical (geometry := replacementGeometry h d) ha hb).trans (fun _ hx => hx.1))
  have hmapP : P.map H.subtype = Vcirc d.radical a := map_subgroupOf_eq_of_le hPH
  have hcard : Nat.card (_root_.commutator P) =
      Nat.card (⁅Vcirc d.radical a,Vcirc d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
    calc
      Nat.card (_root_.commutator P) = Nat.card (⁅P,P⁆ : Subgroup H) := by
        rw [←map_subtype_commutator]
        exact (card_map_of_injective P.subtype_injective).symm
      _ = Nat.card (⁅Vcirc d.radical a,Vcirc d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
        rw [←hmapP,←map_commutator]
        exact (card_map_of_injective H.subtype_injective).symm
  rwa [hcard] at hbound

include s in
/-- A large critical path cannot carry the actual reciprocal FF section:
its moved derived subgroup has order both greater than two and at most two. -/
theorem large_reciprocal_ff_false_knownSimple
    (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hff : ReciprocalMovedFF (h := h) (by omega) a p.start_color hfixed) : False := by
  have hsmall := reciprocal_moving_derived_le_two_of_ff s hc (by omega) p.start_color hfixed hff
  have hbig := large_moving_derived_gt_two_at_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hlarge hfixed
  exact (not_le_of_gt hbig) hsmall

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
