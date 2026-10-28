module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.NaturalQuotient

/-!
# Natural coordinates on the actual moving central quotient

The nonabelian moving radius has a nontrivial irreducible central-quotient
action. Its actual critical endpoint gives fixed index at most eight.
The preceding recognition theorem therefore constructs equivariant natural
four-dimensional coordinates, with the same quotient map and conjugation.
The possible exceptional automorphism is kept in the resulting marking.

Source: MS93 (3.8), printed pp.878--879. DerivedOrder uses these coordinates
to bound the moving derived subgroup without assuming a split cover.
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

private theorem quotient_action_ne_one {H : Type*} [Group H]
    (P J : Subgroup H) [P.Normal] [IsElementaryAbelian 2 (P ⧸ center P)]
    (α : H →* MulAut (P ⧸ center P))
    (hα : ∀ g (x : P), α g (QuotientGroup.mk' (center P) x) =
      QuotientGroup.mk' (center P) (MulAut.conjNormal g x))
    (hfull : ⁅P,J⁆ = P) (hn : ¬ IsMulCommutative P) : Offenders.linearize α ≠ 1 := by
  intro hz
  have hc : ⁅J,P⁆ ≤ centralizer (P : Set H) := by
    apply commutator_le.mpr
    intro g _ x hx
    let v : P := ⟨x,hx⟩
    have hh := LinearMap.congr_fun (congrArg (fun ρ => ρ g) hz)
      (Additive.ofMul (QuotientGroup.mk' (center P) v))
    have hh' : α g (QuotientGroup.mk' (center P) v) = QuotientGroup.mk' (center P) v := hh
    rw [hα] at hh'
    have hz' := QuotientGroup.eq_iff_div_mem.mp hh'
    intro y hy
    have he := congrArg Subtype.val (mem_center_iff.mp hz' (⟨y,hy⟩ : P))
    change y * (g*x*g⁻¹/x) = (g*x*g⁻¹/x)*y at he
    simpa only [commutatorElement_def,div_eq_mul_inv] using he
  rw [commutator_comm, hfull] at hc
  exact hn (le_centralizer_iff_isMulCommutative.mp hc)

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

/-- The actual moving central quotient is a natural four-dimensional A₆ module.
The six-letter marking may be twisted by the exceptional automorphism. -/
theorem movingPreimage_natural
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) :
    letI := movingPreimage_quotient_elementary h m hz hn r himage fg
    ∃ π : r.overgroup →* Equiv.Perm (Fin 6), π.range = alternatingGroup (Fin 6) ∧
      ∃ e : Additive ((movingPreimage r) ⧸ center (movingPreimage r)) ≃ₗ[ZMod 2]
        BinaryPermutation.natural (Fin 6),
        ∀ g v, e (Offenders.linearize (preimageQuotientAction r) g v) =
          BinaryPermutation.naturalRepresentation (Fin 6) (π g) (e v) := by
  let := movingPreimage_quotient_elementary h m hz hn r himage fg
  let : IsIrreducible (Offenders.linearize (preimageQuotientAction r)) :=
    movingPreimage_quotient_irreducible h m hz hn r himage fg
  obtain ⟨b,hcrit⟩ := criticalPair_exists r.radical (alpha r.radical)
    ((replacementGeometry h r).exists_critical (alpha r.radical) rfl)
  let p := CriticalPath.ofPair (geometry := replacementGeometry h r) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans fg.distance
  have hle : 2 ≤ p.walk.length := by omega
  obtain ⟨q,hq,hk,_,hPk,hfull,hfixed,A,a,ha,haA,hi⟩ :=
    moving_budget_data h m hz hn r himage fg b hcrit (p.walk.getVert 2)
      ((p.vertex_color hle).mpr (by decide)) (p.dist_start hle) (by rw [p.dist_end,hl])
  have hnoncomm : ¬ IsMulCommutative (movingPreimage r) := by
    intro hc
    let := hc
    apply moving_not_commutative h m hz hn r himage fg (alpha r.radical) rfl
    rw [←movingPreimage_map h r (by rw [fg.distance]; decide)]
    infer_instance
  apply AlternatingBudget.natural_of_fixedCodim q hq (by rw [hk]; exact pCore_isPGroup)
    (Offenders.linearize (preimageQuotientAction r))
    (quotient_action_ne_one (movingPreimage r) (pResidual 2 r.overgroup)
      (preimageQuotientAction r) (preimageQuotientAction_mk r) hfull hnoncomm)
    A a ha haA
  rw [←AlternatingBudget.central_quotient_fixed_index (movingPreimage r)
    (preimageQuotientAction r) (preimageQuotientAction_mk r) A] at hi
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (show _ ≤ 2 ^ 3 from hi)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
