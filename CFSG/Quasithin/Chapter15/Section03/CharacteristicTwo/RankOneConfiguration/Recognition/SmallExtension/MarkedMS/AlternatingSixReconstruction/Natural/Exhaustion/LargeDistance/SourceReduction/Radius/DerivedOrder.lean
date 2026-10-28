module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.NaturalApplication
public import Theory.Representation.BinaryPermutation.SixCentralDerived

/-!
# Derived order of the actual A₆ moving radius

NaturalApplication identifies the literal central quotient with the binary
natural four-space, allowing either six-letter marking. The two-residual
still maps onto A₆ and fixes the moving derived subgroup. The central-cover
commutator theorem then bounds its order by two. The result is transported
through the original replacement embedding and to every original-group vertex.

Source: MS93 (3.8), printed p.879. No splitting of the central cover is used.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius

private theorem alternating_residual : pResidual 2 (alternatingGroup (Fin 6)) = ⊤ := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let N := pResidual 2 (alternatingGroup (Fin 6))
  by_contra hn
  let : Nontrivial ((alternatingGroup (Fin 6)) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  let : Group.IsPerfect ((alternatingGroup (Fin 6)) ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent ((alternatingGroup (Fin 6)) ⧸ N) :=
    (isPGroup_quotient_pResidual (G := alternatingGroup (Fin 6)) 2).isNilpotent
  exact Group.IsPerfect.not_isSolvable ((alternatingGroup (Fin 6)) ⧸ N) inferInstance

private theorem residual_image {H : Type*} [Group H] [Finite H]
    (π : H →* Equiv.Perm (Fin 6)) (hπ : π.range = alternatingGroup (Fin 6)) :
    (π.comp (pResidual 2 H).subtype).range = alternatingGroup (Fin 6) := by
  let q := π.codRestrict (alternatingGroup (Fin 6)) (fun g => by rw [←hπ]; exact ⟨g,rfl⟩)
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨g,hg⟩ := show (a : Equiv.Perm (Fin 6)) ∈ π.range from (by rw [hπ]; exact a.property)
    exact ⟨g,Subtype.ext hg⟩
  have hm : (pResidual 2 H).map q = ⊤ := by
    rw [map_pResidual_of_surjective 2 q hq, alternating_residual]
  rw [MonoidHom.range_comp,range_subtype]
  change (pResidual 2 H).map ((alternatingGroup (Fin 6)).subtype.comp q) = _
  rw [←map_map,hm,←MonoidHom.range_eq_map,range_subtype]

/-- A natural moving central quotient and fixed derived subgroup bound the
intrinsic derived order, using the actual residual action above A₆. -/
theorem derived_card_le_two_of_natural
    {H : Type*} [Group H] [Finite H] (P : Subgroup H) [P.Normal]
    [IsElementaryAbelian 2 (P ⧸ center P)]
    (α : H →* MulAut (P ⧸ center P))
    (hα : ∀ g (x : P), α g (QuotientGroup.mk' (center P) x) =
      QuotientGroup.mk' (center P) (MulAut.conjNormal g x))
    (π : H →* Equiv.Perm (Fin 6)) (hπ : π.range = alternatingGroup (Fin 6))
    (e : Additive (P ⧸ center P) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ g v, e (Offenders.linearize α g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (π g) (e v))
    (hfixed : ⁅⁅P,P⁆,pResidual 2 H⁆ = ⊥) : Nat.card (_root_.commutator P) ≤ 2 := by
  let em : (P ⧸ center P) ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    e.toAddEquiv.toMultiplicative
  let q := em.toMonoidHom.comp (QuotientGroup.mk' (center P))
  let ρ : pResidual 2 H →* MulAut P :=
    (MulAut.conjNormal : H →* MulAut P).comp (pResidual 2 H).subtype
  apply BinaryPermutation.SixCentralDerived.card_derived_le_two q
    (em.surjective.comp (QuotientGroup.mk'_surjective (center P)))
    (by
      intro x hx
      apply (QuotientGroup.eq_one_iff x).mp
      apply em.injective
      exact hx.trans (map_one em).symm)
    ρ (π.comp (pResidual 2 H).subtype) (residual_image π hπ).ge
  · intro g x
    have hh := he g (Additive.ofMul (QuotientGroup.mk' (center P) x))
    change e (Additive.ofMul (α g (QuotientGroup.mk' (center P) x))) = _ at hh
    rw [hα] at hh
    exact hh
  · intro g _ z hz
    apply Subtype.ext
    have hz' : (z : H) ∈ ⁅P,P⁆ := by
      rw [←map_subtype_commutator]
      exact mem_map_of_mem P.subtype hz
    have hcent := commutator_eq_bot_iff_le_centralizer.mp hfixed hz' g g.property
    change (g : H) * (z : H) * (g : H)⁻¹ = (z : H)
    rw [hcent,mul_inv_cancel_right]

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

/-- The source moving radius has at most two commutators. Both its natural
quotient and residual fixedness are proved on the original replacement. -/
theorem movingPreimage_derived_card_le_two
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) : Nat.card (_root_.commutator (movingPreimage r)) ≤ 2 := by
  let := movingPreimage_quotient_elementary h m hz hn r himage fg
  obtain ⟨π,hπ,e,he⟩ := movingPreimage_natural h m hz hn r himage fg
  apply derived_card_le_two_of_natural (movingPreimage r)
    (preimageQuotientAction r) (preimageQuotientAction_mk r) π hπ e he
  apply (map_injective (embedM_injective r.radical))
  rw [map_commutator,map_commutator,movingPreimage_map h r (by rw [fg.distance]; decide),
    ←Ltilde_alpha r.radical,Subgroup.map_bot]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hPV : Vcirc r.radical (alpha r.radical) ≤ V r.radical (alpha r.radical) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (V_normalized _))
  exact (commutator_mono hPV hPV).trans
    ((radius_derived_le_fixed h m hz hn r himage fg (alpha r.radical) rfl).trans inf_le_right)

/-- The bound on the literal ambient moving commutator, through the unchanged
embedding of the original replacement. -/
theorem moving_derived_card_le_two_alpha
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) :
    Nat.card (⁅Vcirc r.radical (alpha r.radical),Vcirc r.radical (alpha r.radical)⁆ :
      Subgroup (FreeAmalgam r.radical)) ≤ 2 := by
  have hm := movingPreimage_map h r (by rw [fg.distance]; decide)
  rw [←hm,←map_commutator,card_map_of_injective (embedM_injective r.radical),
    ←map_subtype_commutator,card_map_of_injective (movingPreimage r).subtype_injective]
  exact movingPreimage_derived_card_le_two h m hz hn r himage fg

/-- The source commutator bound at every original-group vertex. -/
theorem moving_derived_card_le_two
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    Nat.card (⁅Vcirc r.radical a,Vcirc r.radical a⁆ : Subgroup (FreeAmalgam r.radical)) ≤ 2 := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color r.radical ha
  have hv : Vcirc r.radical (mVertex r.radical g) =
      (Vcirc r.radical (alpha r.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Vcirc_act r.radical g (alpha r.radical)
  rw [hv,←map_commutator,card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact moving_derived_card_le_two_alpha h m hz hn r himage fg

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
