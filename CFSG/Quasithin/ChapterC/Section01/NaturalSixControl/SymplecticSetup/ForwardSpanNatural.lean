module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.OddTransvectionNatural
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanEndpoint
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanFaithful
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions
/-!
# Natural recognition of the terminal moving central section

The forward normal span has an elementary central quotient, with a faithful
literal symmetric-six action. An odd element of the opposite critical
Z-layer is an involution and has fixed index at most two. Faithfulness makes
its fixed codimension exactly one. The established B.5.1 odd-transvection
recognition therefore identifies the actual alternating moved section,
modulo its fixed space, with the natural four-dimensional binary module.

The result retains the descended action and its possibly outer marking.
It does not identify the entire central quotient with that moved section.
The characteristic-replacement and original Chapter13 applications supply
all action, faithfulness, fixed-index and SQTK premises internally.

Source: Meierfrankenfeld--Stellmacher (1993), the terminal paragraph of
(5.12), printed p.927, and (3.10), printed pp.879--881; the recognition input
is the proved Aschbacher--Smith B.5.1 source theorem.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93

private theorem linearized_cyclic_codim_eq_one
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    {D : Type*} [Group D] (ρ : D→*MulAut Y) (hf : Function.Injective ρ)
    (a : D) (ha : a≠1) (hi : (ρ a).fixedSubgroup.index≤2) :
    fixedCodim (Offenders.linearize ρ) (zpowers a)=1 := by
  let σ := Offenders.linearize ρ
  change fixedCodim σ (zpowers a)=1
  let e : fixedSpace σ (zpowers a) ≃ (ρ a).fixedSubgroup := {
    toFun := fun v => ⟨v.val.toMul, (MulAut.mem_fixedSubgroup _ _).mpr
      (congrArg Additive.toMul ((mem_fixedSpace_zpowers_iff σ a v.val).mp v.property))⟩
    invFun := fun v => ⟨Additive.ofMul v.val,(mem_fixedSpace_zpowers_iff σ a _).mpr
      (congrArg Additive.ofMul ((MulAut.mem_fixedSubgroup _ _).mp v.property))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card Y≤Nat.card ((ρ a).fixedSubgroup)*2 := by
    rw [←(ρ a).fixedSubgroup.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  rw [←Nat.card_congr e] at hcard
  change Nat.card (Additive Y)≤_ at hcard
  have hV := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive Y)
  have hF := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=fixedSpace σ (zpowers a))
  rw [Nat.card_zmod] at hV hF
  rw [hV,hF] at hcard
  have hd : Module.finrank (ZMod 2) (Additive Y)≤
      Module.finrank (ZMod 2) (fixedSpace σ (zpowers a))+1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [pow_succ] using hcard
  have hne : zpowers a≠⊥ := fun he => ha (mem_bot.mp (he ▸ mem_zpowers a))
  have hp := fixedCodim_pos_of_faithful σ (Offenders.linearize_injective ρ hf) hne
  have hs := fixedCodim_add_finrank σ (zpowers a)
  omega

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem forward_span_moved_section_natural
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (ρ : Model.S →* MulAut ((localZSpan R (p.walk.getVert 2) (alpha R)) ⧸
        center (localZSpan R (p.walk.getVert 2) (alpha R))))
    (hρ : ∀ m : M, ρ (s.projection m)=forwardSpanCentralAction R (p.walk.getVert 2) m)
    (hEA : IsElementaryAbelian 2 ((localZSpan R (p.walk.getVert 2) (alpha R)) ⧸
        center (localZSpan R (p.walk.getVert 2) (alpha R)))) :
    let := hEA
    ∃ sectionData : MovedSection (Offenders.linearize ρ) (alternatingGroup (Fin 6)),
      IsSymmetricNatural sectionData.action 6 := by
  let := hEA
  have hf := s.forward_span_symmetric_central_action_injective h u hfull hb p ρ hρ
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  have hb2 : 2<s.geometry.b R := by omega
  have hPG : P≤stabilizer R (alpha R) :=
    ((s.forward_span_le_hyperplane_kernel hb2 p).trans inf_le_left).trans (by intro x hx; exact hx.1)
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hpnt : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  obtain ⟨a,ha,hodd⟩ := SetLike.not_le_iff_exists.mp
    (s.critical_opposite_image_not_le_alternating h u hpnt p)
  obtain ⟨m,hm,rfl⟩ := ha
  have hn : s.projection m≠1 := fun he => hodd (he ▸ (alternatingGroup (Fin 6)).one_mem)
  have hsquare : (s.projection m)^2=1 := by
    have hm2 : m^2=1 := by
      apply embedM_injective R
      rw [map_pow,map_one]
      let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
      exact elemPow_eq_one_of_isElementaryAbelian (embedM R m) hm
    rw [←map_pow,hm2,map_one]
  have hc : Nat.card (zpowers (s.projection m))=2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime_iff.mpr ⟨hsquare,hn⟩
  let : IsElementaryAbelian 2 (zpowers (s.projection m)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      simpa only [hc] using pow_card_eq_one' (x:=x)) }
  exact SourceCompletion.symmetricSix_moved_section_natural_of_odd_transvection
    (Offenders.linearize ρ) (Offenders.linearize_injective ρ hf) (s.alternating_sqtk hsq)
    (zpowers (s.projection m)) hc
    (linearized_cyclic_codim_eq_one ρ hf _ hn (s.forward_span_endpoint_fixed_index h u hfull hb p ρ hρ m hm))
    (fun he => hodd (he (mem_zpowers _)))

@[expose] def ForwardSpanNaturalData (c : Vertex R) : Prop :=
  let P := localZSpan R c (alpha R)
  ∃ hEA : IsElementaryAbelian 2 (P⧸center P),
    ∃ ρ : Model.S →* MulAut (P⧸center P),
      (∀ m : M, ρ (s.projection m)=forwardSpanCentralAction R c m) ∧
      Function.Injective ρ ∧
      (let := hEA
       ∃ sectionData : MovedSection (Offenders.linearize ρ) (alternatingGroup (Fin 6)),
         IsSymmetricNatural sectionData.action 6)

theorem forward_span_natural_data
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    s.ForwardSpanNaturalData (p.walk.getVert 2) := by
  have hEA := (s.forward_span_central_quotient h u hfull hb p).1
  obtain ⟨ρ,hρ⟩ := s.exists_forward_span_symmetric_central_action h u hfull hb p
  exact ⟨hEA,ρ,hρ,s.forward_span_symmetric_central_action_injective h u hfull hb p ρ hρ,
    s.forward_span_moved_section_natural h u hfull hsq hb p ρ hρ hEA⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

theorem reducedSource_block_or_forward_span_natural
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨ ((originalSource d hm).reduce r).ForwardSpanNaturalData (p.walk.getVert 2) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    have h := reduced_nativeCentralLayer d hm r
    exact s.forward_span_natural_data h _ hf ((d.sqtk.subgroup J).subgroup r.overgroup) hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
