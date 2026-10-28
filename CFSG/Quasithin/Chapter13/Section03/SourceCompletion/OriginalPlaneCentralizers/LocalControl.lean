module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Cases
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The actual plane centralizer and its local action

The original chosen module supplies characteristic two for C_G(A): move a
nonidentity element of A to a Sylow-fixed vector and apply centralizer
inheritance. Restrict the characteristic-normalizer control for Q = O₂(LT)
to C_G(A). Together with separately established radicality and normal-closure
Sylow geometry, these facts construct the literal C.2.3 input.

The action of C_M(A) on V maps into the pointwise plane stabilizer S₃. Its
kernel is exactly C_M(V), so its faithful quotient has order dividing six.
The quotient is formed from the actual conjugation action, with no assumed
model isomorphism or ambient normality of the prospective component.

Source: Aschbacher--Smith 13.3.12, printed p.889, and 1.1.3--4.
This supplies local preparation; component extraction and inspection remain
separate source arguments.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

omit [Finite G] in
theorem MarkedPlane.card (d : MarkedPlane V) : Nat.card d.A = 4 := by
  have hc := card_pointCoordinateSubspace d.coordinates d.A d.le_module
  rw [d.plane_space, Module.natCard_eq_pow_finrank (K := K), Nat.card_zmod,
    plane_geometry.1] at hc
  exact hc.symm

omit [Finite G] in
theorem MarkedPlane.ne_bot (d : MarkedPlane V) : d.A ≠ ⊥ := by
  intro h
  have hc := d.card
  rw [h, Subgroup.card_bot] at hc
  norm_num at hc

theorem Context.plane_local_control (s : Context T L V) (d : MarkedPlane V) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (d.A : Set G) ∧
    IsSQTK KnownSimple.IsKnownSimple (centralizer (d.A : Set G)) ∧
    (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (centralizer (d.A : Set G))).characteristicNormalizerClosure ≤
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).subgroupOf
        (centralizer (d.A : Set G)) ∧
    centralizer (d.A : Set G) ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G) := by
  obtain ⟨he, hk, _⟩ := s.earlier_geometry
  have hQH : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (d.A : Set G) := by
    rw [← hk]
    exact inf_le_right.trans (Subgroup.centralizer_le d.le_module)
  have hn : IsSQTK KnownSimple.IsKnownSimple (normalizer (d.A : Set G)) :=
    s.hypothesis.qtke.twoLocal_sqtk
      ⟨d.A, d.ne_bot, IsPGroup.of_card (n := 2) d.card, rfl⟩
  have hsq : IsSQTK KnownSimple.IsKnownSimple (centralizer (d.A : Set G)) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer
      (d.A : Set G)))).mp (hn.subgroup _)
  have hcontrol := he.characteristic_normalizers_le
  change ((T : Subgroup G) ⊓ centralizer (V : Set G)).characteristicNormalizerClosure ≤ _ at hcontrol
  rw [hk] at hcontrol
  have hlocal := characteristicNormalizerClosure_subgroupOf_le hQH hcontrol
  refine ⟨hQH, hsq, ?_, ?_⟩
  · intro x hx
    exact ⟨x.property, hlocal hx⟩
  · simpa only [inf_comm] using he.localCentralizer_le_normalizer d.ne_bot d.le_module

/-- Every nonzero vector is conjugate under the original component to a
Sylow-fixed involution. Thus the centralizer of any nontrivial subgroup of
the chosen module has characteristic two. -/
theorem Context.centralizer_characteristicTwo (s : Context T L V)
    (A : Subgroup G) (hAV : A ≤ V) (hA : A ≠ ⊥) :
    HasCharacteristicTwo (centralizer (A : Set G)) := by
  have he := s.earlier_geometry.1
  have earlier := Section06.source_earlierLocalFacts he
  obtain ⟨z, hz, hz1⟩ := Section06.Components.exists_sylow_fixed he
  have hzchar := he.centralizer_fixedPoint_characteristicTwo earlier hz hz1
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have hxG : x.val ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨n, _, _, hn⟩ := unitary_component_transitive L s.actor s.coordinates
    s.equivariant z x.val hz.1 (hAV x.property) hz1 hxG
  have hxchar : HasCharacteristicTwo (centralizer ({x.val} : Set G)) := by
    rw [← hn]
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj n) z)).mp hzchar
  have hAC : A ≤ centralizer ({x.val} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      ((V.le_centralizer (hAV x.property)) a (hAV ha))
  have hc := earlier.centralizers A (centralizer ({x.val} : Set G)) hxchar hAC
    ((IsElementaryAbelian.isPGroup 2 V).to_le hAV)
  have hCA : centralizer (A : Set G) ≤ centralizer ({x.val} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.property)
  rwa [inf_eq_right.mpr hCA] at hc

/-- In the actual escaping component record, characteristic two is supplied
by the chosen natural module, independently of component inspection. -/
theorem Context.localData_of_input (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G)
    (h : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple (centralizer (d.A : Set G)) ((L ⊔ T).pCoreIn 2)
        (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) J)
    (S : Sylow 2 (centralizer (d.A : Set G)))
    (hS : (S : Subgroup (centralizer (d.A : Set G))).map
      (centralizer (d.A : Set G)).subtype ≤ normalizer (L : Set G)) :
    Nonempty (LocalData T L d J) :=
  ⟨⟨h, s.centralizer_characteristicTwo d.A d.le_module d.ne_bot, S, hS⟩⟩

/-- Construct the literal C.2.3 input after its radicality and local Sylow
geometry have been established. Characteristic-normalizer control and the
SQTK condition are derived from the original source context. -/
theorem Context.pushingUpSetup (s : Context T L V) (d : MarkedPlane V)
    (hrad : IsPRadical 2 (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (centralizer (d.A : Set G))))
    (hsyl : Chapter1.IsSylowIn 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      ((normalClosure (↑(((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
        (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))))).map
          (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).subtype)) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      (centralizer (d.A : Set G)) ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) := by
  obtain ⟨hQH, hsq, hc, _⟩ := s.plane_local_control d
  exact ⟨hsq, hQH, inf_le_left, hrad, hc, hsyl⟩

/-- The literal action of C_M(A) embeds its faithful image into the pointwise
stabilizer S₃ of the standard nondegenerate plane. -/
noncomputable def Context.planeCentralizerAction (s : Context T L V) (d : MarkedPlane V) :
    (centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G) →*
      Representation.BinaryOffender.subspaceKernel rho plane ⊤ :=
  (d.chart.comp (V.normalizerMonoidHom.rangeRestrict.comp
    (inclusion (s.plane_local_control d).2.2.2))).codRestrict _ (by
      intro x
      refine ⟨mem_top _, ?_⟩
      intro w hw
      obtain ⟨v, rfl⟩ := d.coordinates.surjective w
      have hv : v.toMul.val ∈ d.A :=
        (mem_pointCoordinateSubspace d.coordinates d.A v).mp (d.plane_space.symm ▸ hw)
      change rho (d.chart (V.normalizerMonoidHom.rangeRestrict _)) (d.coordinates v) = _
      rw [← d.equivariant]
      apply congrArg d.coordinates
      apply Additive.toMul.injective
      apply Subtype.ext
      change x.val * v.toMul.val * x.val⁻¹ = v.toMul.val
      rw [← mem_centralizer_iff.mp x.property.1 _ hv, mul_inv_cancel_right])

/-- The pointwise stabilizer action retains the original full-automizer chart. -/
theorem Context.planeCentralizerAction_apply (s : Context T L V) (d : MarkedPlane V)
    (x : (centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G)) :
    (s.planeCentralizerAction d x).val =
      d.chart (V.normalizerMonoidHom.rangeRestrict
        (inclusion (s.plane_local_control d).2.2.2 x)) := by rfl

theorem Context.planeCentralizerAction_ker (s : Context T L V) (d : MarkedPlane V) :
    (s.planeCentralizerAction d).ker = (centralizer (V : Set G)).subgroupOf
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) := by
  ext x
  constructor
  · intro hx v hv
    let w : Additive V := Additive.ofMul ⟨v,hv⟩
    have he := d.equivariant (V.normalizerMonoidHom.rangeRestrict
      (inclusion (s.plane_local_control d).2.2.2 x)) w
    have hx' := congrArg Subtype.val (show s.planeCentralizerAction d x = 1 from hx)
    change d.chart (V.normalizerMonoidHom.rangeRestrict
      (inclusion (s.plane_local_control d).2.2.2 x)) = 1 at hx'
    rw [hx', map_one, Module.End.one_apply] at he
    have hc : x.val * v * x.val⁻¹ = v :=
      congrArg (fun z : Additive V => z.toMul.val) (d.coordinates.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro hx
    apply Subtype.ext
    apply rho_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    change rho (d.chart (V.normalizerMonoidHom.rangeRestrict _)) (d.coordinates v) =
      rho 1 (d.coordinates v)
    rw [← d.equivariant, map_one, Module.End.one_apply]
    apply congrArg d.coordinates
    apply Additive.toMul.injective
    apply Subtype.ext
    change x.val * v.toMul.val * x.val⁻¹ = v.toMul.val
    have hxc : x.val ∈ centralizer (V : Set G) := hx
    rw [← mem_centralizer_iff.mp hxc _ v.toMul.property, mul_inv_cancel_right]

theorem Context.planeCentralizerAction_quotient_card_dvd_six
    (s : Context T L V) (d : MarkedPlane V) :
    Nat.card ((centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G) ⧸
      (s.planeCentralizerAction d).ker) ∣ 6 := by
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (s.planeCentralizerAction d)).toEquiv]
  have h := (s.planeCentralizerAction d).range.card_subgroup_dvd_card
  obtain ⟨e⟩ := pointwise_plane_equiv_s3
  rw [Nat.card_congr e.toEquiv] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
    Nat.factorial_succ, Nat.factorial_zero] using h

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
