module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalExclusionFF

/-!
# FF comparison on the original moving central quotient

An actual descended S6 action on the original moving radius modulo its
center, with an FF witness, bounds the original derived subgroup by two.
The central quotient map, residual commutator generation and derived
fixedness are transported through the original vertex stabilizer. The
actor map is supplied with pointwise compatibility; the full quotient by
the two-core is never identified with S6.

Source: Meierfrankenfeld--Stellmacher (1993), (3.10)(i) and (5.12)(2),
printed pp.880,926; Aschbacher--Smith B.4.2 and B.5.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R)
local notation "Rg" => edge L R

/-- The actual initial layer component supplies the alternating SQTK input
when its action kernel is the retained extension kernel. -/
theorem cubic_terminal_alternating_sqtk (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = extensionKernel h) :
    IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)) := by
  obtain ⟨E⟩ := layerComponent_equiv_alternating h e hk
  exact IsSQTK.knownSimple_of_equiv E (layerComponent_sqtk h e hz)

/-- A genuine FF action on the original moving central quotient has derived
order at most two. The S6 projection retains its actual pointwise action. -/
theorem moving_derived_le_two_of_central_ff
    (hb : 2 < sourceDistance h) (a : Vertex Rg) (ha : color Rg a = false)
    (hfixed : ⁅V Rg a,V Rg a⁆ ≤ fixedCore Rg a)
    (π : stabilizer Rg a →* Equiv.Perm (Fin 6)) (hπ : Function.Surjective π)
    (hπL : (pResidual 2 (stabilizer Rg a)).map π = alternatingGroup (Fin 6))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6))) :
    letI := moving_central_quotient_elementary (sourceGeometry h)
      (sourceDistance_pos h) a ha hfixed
    ∀ σ : Representation (ZMod 2) (Equiv.Perm (Fin 6))
      (Additive ((Vcirc Rg a) ⧸ center (Vcirc Rg a))),
      (∀ g v, σ (π g) v = Offenders.linearize (movingQuotientAction a) g v) →
      IsFFModule σ → Nat.card (_root_.commutator (Vcirc Rg a)) ≤ 2 := by
  let := moving_central_quotient_elementary (sourceGeometry h)
    (sourceDistance_pos h) a ha hfixed
  let := finite_moving (sourceGeometry h) hb a ha
  intro σ hσ hff
  let J := stabilizer Rg a
  let P := (Vcirc Rg a).subgroupOf J
  let : P.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
  have hPV : Vcirc Rg a ≤ V Rg a :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hPJ : Vcirc Rg a ≤ J :=
    hPV.trans (((sourceGeometry h).V_le_Q hb a ha).trans (fun _ hx => hx.1))
  let i : P ≃* Vcirc Rg a := subgroupOfEquivOfLe hPJ
  let q₀ := (QuotientGroup.mk' (center (Vcirc Rg a))).comp i.toMonoidHom
  let q : P →* Multiplicative (Additive ((Vcirc Rg a) ⧸ center (Vcirc Rg a))) := {
    toFun := fun x => Multiplicative.ofAdd (Additive.ofMul (q₀ x))
    map_one' := congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) q₀.map_one
    map_mul' := fun x y => congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) (q₀.map_mul x y) }
  have hq : Function.Surjective q := by
    intro w
    obtain ⟨x,hx⟩ := (QuotientGroup.mk'_surjective (center (Vcirc Rg a))).comp i.surjective w.toAdd.toMul
    exact ⟨x,congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) hx⟩
  have hker : q.ker ≤ center P := by
    intro x hx
    have hxi : i x ∈ center (Vcirc Rg a) := (QuotientGroup.eq_one_iff _).mp hx
    apply mem_center_iff.mpr
    intro y
    apply i.injective
    rw [map_mul,map_mul]
    exact mem_center_iff.mp hxi (i y)
  have hact (g : J) (x : P) :
      (q (MulAut.conjNormal g x)).toAdd = σ (π g) (q x).toAdd := by
    rw [hσ]
    change Additive.ofMul (QuotientGroup.mk' (center (Vcirc Rg a)) (i (MulAut.conjNormal g x))) =
      Additive.ofMul (movingQuotientAction a g (QuotientGroup.mk' (center (Vcirc Rg a)) (i x)))
    rw [movingQuotientAction_apply]
    rfl
  have hmapP : P.map J.subtype = Vcirc Rg a := map_subgroupOf_eq_of_le hPJ
  have hfull : ⁅P,pResidual 2 J⁆ = P := by
    apply map_injective J.subtype_injective
    rw [map_commutator,hmapP]
    exact moving_full_commutation_original h (sourceGeometry h) hb a ha
  have hfix : ⁅P,P⁆ ≤ centralizer (pResidual 2 J : Set J) := by
    intro x hx l hl
    have hx' : (x : FreeAmalgam Rg) ∈ ⁅Vcirc Rg a,Vcirc Rg a⁆ := by
      have hh := mem_map_of_mem J.subtype hx
      rwa [map_commutator,hmapP] at hh
    have he := (hfixed (commutator_mono hPV hPV hx')).2
      (l : FreeAmalgam Rg) (mem_map_of_mem J.subtype hl)
    exact Subtype.ext he
  have hbound :=
    AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.reciprocal_ff_central_cover_derived_le_two
      P π hπ hπL σ q hq hker hact hfull hfix hsq hff
  have hcard : Nat.card (_root_.commutator P) = Nat.card (_root_.commutator (Vcirc Rg a)) := by
    have hm : (_root_.commutator P).map i.toMonoidHom = _root_.commutator (Vcirc Rg a) := by
      rw [map_commutator_eq,MonoidHom.range_eq_top.mpr i.surjective,←commutator_def]
    rw [←hm,card_map_of_injective i.injective]
  rwa [hcard] at hbound

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
