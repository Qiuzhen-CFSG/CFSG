module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualCenter
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreClass
public import Theory.GroupAction.Order512FiveStructure
public import Theory.Frattini.CentralDerived
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The derived boundary for the original large five-residual

The original order-32 span has centralizer in the residual equal to the
marked central line. Consequently its commutator with the residual is
exactly that line, so the residual is nonabelian. The full core bounds its
class by three. In class three Parrott's intrinsic action theorem identifies
the actual derived and Frattini subgroups with the original span. The other
possibility is retained literally: class two and derived subgroup equal to
the marked central line. No model identification or class-three lower bound
is inferred from the residual order.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual large-branch residual has a nonzero marked span commutator;
its exact remaining derived alternatives separate class two from class three. -/
theorem source_quintic_large_five_residual_derived_alternative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let R := ⁅Q,A⁆
    let Z := centralInvolutions T
    ⁅U,R⁆ = Z ∧ Z ≤ ⁅R,R⁆ ∧ ⁅R,R⁆ ≤ U ∧
      ((Group.nilpotencyClass R = 2 ∧ ⁅R,R⁆ = Z) ∨
        (Group.nilpotencyClass R = 3 ∧ ⁅R,R⁆ = U ∧
          (frattini R).map R.subtype = U ∧
          (Subgroup.upperCentralSeries R 2).map R.subtype = U)) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  let B := Q ⊓ centralizer (A : Set G)
  obtain ⟨_, _, _, _, hRcard, hUR, _, _⟩ :=
    source_quintic_large_five_residual hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA
  obtain ⟨_, hcapB, hURfixed, hcenter, _, hAR⟩ :=
    source_quintic_large_five_residual_center hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA
  change U ⊓ centralizer (R : Set G) = Z at hURfixed
  change R ⊓ B = Z at hcapB
  change (center R).map R.subtype = Z at hcenter
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  have hRtwo : IsPGroup 2 R := (isPGroup_pCoreIn 2 H).to_le hRQ
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 H).isNilpotent
  let : Group.IsNilpotent R := hRtwo.isNilpotent
  have hUcard : Nat.card U = 32 := (source_quintic_span_card_and_core_radical
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZne : Z ≠ ⊥ := by
    intro hz
    rw [hz, card_bot] at hZcard
    omega
  have hUQcomm : ⁅U,Q⁆ = Z := (source_quintic_core_commutators
    hG T hempty hM hu hmany hcard e H hH hi).2
  have hURcomm : ⁅U,R⁆ = Z := by
    have hle : ⁅U,R⁆ ≤ Z := (commutator_mono le_rfl hRQ).trans hUQcomm.le
    have hne : ⁅U,R⁆ ≠ ⊥ := by
      intro he
      have hUZ : U ≤ Z := by
        rw [← hURfixed]
        exact le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.mp he)
      have hc := card_le_of_le hUZ
      rw [hUcard, hZcard] at hc
      omega
    exact eq_of_le_of_card_ge hle (by
      rw [hZcard]
      have hp : 0 < Nat.card (⁅U,R⁆ : Subgroup G) := Nat.card_pos
      have hn : Nat.card (⁅U,R⁆ : Subgroup G) ≠ 1 := fun h => hne (card_eq_one.mp h)
      omega)
  have hZD : Z ≤ ⁅R,R⁆ := hURcomm.ge.trans (commutator_mono hUR le_rfl)
  have hDU : ⁅R,R⁆ ≤ U := (commutator_mono hRQ hRQ).trans
    (source_quintic_full_core_layers hG T hempty hM hu hmany hcard e H hH hi).1.le
  have hRclassLe : Group.nilpotencyClass R ≤ 3 := by
    have hQclass := (source_quintic_full_core_class_and_exponent
      hG T hempty hM hu hmany hcard e H hH hi).1
    have hQzero : Q.lowerCentralSeries 3 = ⊥ :=
      lowerCentralSeries_eq_bot_of_nilpotencyClass_le hQclass.le
    have hRzero : (⊤ : Subgroup R).lowerCentralSeries 3 = ⊥ := by
      apply (map_eq_bot_iff_of_injective _ (f := R.subtype) R.subtype_injective).mp
      rw [map_lowerCentralSeries, ← MonoidHom.range_eq_map, range_subtype]
      exact bot_unique ((lowerCentralSeries_mono 3 hRQ).trans hQzero.le)
    exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hRzero
  have hRclassLo : 2 ≤ Group.nilpotencyClass R := by
    by_contra hn
    have hh : Group.nilpotencyClass R ≤ 1 := by omega
    have hz : R.lowerCentralSeries 1 = ⊥ :=
      lowerCentralSeries_eq_bot_of_nilpotencyClass_le hh
    have hDbot : ⁅R,R⁆ = ⊥ := hz
    exact hZne (bot_unique (hZD.trans hDbot.le))
  refine ⟨hURcomm, hZD, hDU, ?_⟩
  by_cases htwo : Group.nilpotencyClass R ≤ 2
  · left
    refine ⟨?_, le_antisymm ?_ hZD⟩
    · change Group.nilpotencyClass R = 2
      omega
    · have hz : R.lowerCentralSeries 2 = ⊥ :=
        lowerCentralSeries_eq_bot_of_nilpotencyClass_le htwo
      have hDZ : ⁅R,R⁆ ≤ centralizer (R : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp hz
      intro d hd
      apply hcenter.le
      refine ⟨⟨d, (commutator_le_self R) hd⟩, ?_, rfl⟩
      exact mem_center_iff.mpr (fun r => Subtype.ext ((hDZ hd) r r.property))
  · right
    let : Normalizes A R := ⟨hAR⟩
    have hfixed : FixedPoints.subgroup A R ≤ center R := by
      have hfixeq : FixedPoints.subgroup A R =
          (R ⊓ centralizer (A : Set G)).subgroupOf R :=
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R A hAR
      rw [hfixeq]
      intro r hr
      have hrZ : (r : G) ∈ Z := hcapB.le ⟨r.property, hRQ r.property, hr.2⟩
      obtain ⟨z, hz, heq⟩ := hcenter.ge hrZ
      exact (Subtype.ext heq : z = r) ▸ hz
    obtain ⟨hclass, _, hPhi, hUpper, _, hDcard⟩ :=
      Theory.GroupAction.parrott_twoGroup_structure hRtwo hRcard (by omega) hA hfixed
    have hDeq : ⁅R,R⁆ = U := eq_of_le_of_card_ge hDU (by
      rw [← map_subtype_commutator, card_map_of_injective R.subtype_injective,
        hDcard, hUcard])
    refine ⟨hclass, hDeq, ?_, ?_⟩
    · rw [← hPhi, map_subtype_commutator]
      exact hDeq
    · rw [← hUpper, map_subtype_commutator]
      exact hDeq


/-- The full Frattini subgroup of the actual residual always equals its
actual derived subgroup. Its unresolved low-class case is extraspecial,
while the class-three case has the original marked span as both layers. -/
theorem source_quintic_large_five_residual_phi_and_extraspecial_alternative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let R := ⁅H.pCoreIn 2,A⁆
    _root_.commutator R = frattini R ∧
      ((IsExtraspecial 2 R ∧ Group.nilpotencyClass R = 2 ∧
          ⁅R,R⁆ = centralInvolutions T ∧
          (frattini R).map R.subtype = centralInvolutions T) ∨
        (Group.nilpotencyClass R = 3 ∧ ⁅R,R⁆ = U ∧
          (frattini R).map R.subtype = U ∧
          (Subgroup.upperCentralSeries R 2).map R.subtype = U)) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  obtain ⟨_, _, _, halt⟩ := source_quintic_large_five_residual_derived_alternative
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  rcases halt with ⟨hclass,hderived⟩ | ⟨hclass,hderived,hPhi,hupper⟩
  · have hcenter := (source_quintic_large_five_residual_center
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2.1
    have hDcenter : _root_.commutator R = center R := by
      apply Subgroup.map_injective R.subtype_injective
      rw [map_subtype_commutator, hderived, hcenter]
    have hZcard : Nat.card (center R) = 2 := by
      rw [← card_map_of_injective R.subtype_injective, hcenter]
      exact plane_centralInvolutions_card T M hM.1.2 hcard e
    have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
    have hRtwo : IsPGroup 2 R := (isPGroup_pCoreIn 2 H).to_le
      (le_normalizer_iff_commutator_le_left.mp hAQ)
    let : Fact (IsPGroup 2 R) := ⟨hRtwo⟩
    have hPhiZ : frattini R ≤ center R :=
      frattini_le_center_of_central_involutory_commutators hRtwo hDcenter.le (by
        intro r hr
        have hh := congrArg (center R).subtype
          (pow_card_eq_one' (x := (⟨r,hDcenter.le hr⟩ : center R)))
        change r ^ Nat.card (center R) = 1 at hh
        rwa [hZcard] at hh)
    have hPhiEq : frattini R = center R := le_antisymm hPhiZ
      (hDcenter.ge.trans (commutator_le_frattini_of_isPGroup (p := 2)))
    have hspecial : IsExtraspecial 2 R := {
      center_order_p := hZcard
      quotient_elementary_abelian := elementary_quotient_of_frattini_le hRtwo _ hPhiZ
      quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (by
        intro hz
        have hRcard := (source_quintic_large_five_residual
          hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2.2.1
        rw [hz, card_top, hRcard] at hZcard
        omega) }
    refine ⟨hDcenter.trans hPhiEq.symm, Or.inl ⟨hspecial,hclass,hderived,?_⟩⟩
    rw [hPhiEq]
    exact hcenter
  · have hDPhi : _root_.commutator R = frattini R := by
      apply Subgroup.map_injective R.subtype_injective
      rw [map_subtype_commutator]
      exact hderived.trans hPhi.symm
    exact ⟨hDPhi, Or.inr ⟨hclass,hderived,hPhi,hupper⟩⟩

end CFSG.Quasithin.Chapter14.Section06
