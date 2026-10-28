module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Faithfulness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Kernel.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Kernel.Geometry

/-!
# The intrinsic moving-coordinate kernel is contained in U

Write C = Vcirc and D = Z[V,Q] inside the finite vertex stabilizer.
The natural-section triple bound and two-residual commutator idempotence
give [D,Ltilde] ≤ U. The supplied H = [C,Q] = U and G = Ltilde Q then
make C intersect D fixed modulo U under the whole stabilizer.

The initial facts give b ≥ 6, so C/U is elementary abelian. Its residual
commutator is the whole quotient. The critical endpoint supplies an actual
nonidentity involution of SL₃(2) with displacement of order at most two;
the checked small-involution splitting theorem makes the fixed subgroup of
C/U trivial. This proves the literal kernel bound C intersect D ≤ U.

The result retains the authorized conditional contract. H = U is used only
at the chosen vertex; the parent first-pairing assembly supplies it. The
existing Coordinates module then restricts the original dual coordinates
and preserves their marking on U.
Source: Meierfrankenfeld--Stellmacher (1993), the denominator convention
on p.881 and |Vcirc/(UH)| = q³ in (4.3.2)(3), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
open Initial Initial.Consequences Initial.Natural Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

private theorem commutator_sup_bound {A : Type*} [Group A]
    {X Y L N : Subgroup A} [N.Normal]
    (hx : ⁅X, L⁆ ≤ N) (hy : ⁅Y, L⁆ ≤ N) : ⁅X ⊔ Y, L⁆ ≤ N := by
  have hh : X ⊔ Y ≤ commutatorPreimage ⊤ L N :=
    sup_le (le_commutatorPreimage le_top hx) (le_commutatorPreimage le_top hy)
  exact (commutator_mono hh le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ L N le_normalizer_of_normal)

private theorem local_bound (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (hi : InitialFacts p) (o : MovingOrientationAt p.a) (hH : H R p.a = U R p.a) :
    (Vcirc R p.a).subgroupOf (stabilizer R p.a) ⊓
      radicalPreimage ((Q R p.a).subgroupOf (stabilizer R p.a))
        ((V R p.a).subgroupOf (stabilizer R p.a)) ((Z R p.a).subgroupOf (stabilizer R p.a)) ≤
      (U R p.a).subgroupOf (stabilizer R p.a) := by
  let S := stabilizer R p.a
  let V₀ := (V R p.a).subgroupOf S
  let Z₀ := (Z R p.a).subgroupOf S
  let Q₀ := (Q R p.a).subgroupOf S
  let L₀ := pResidual 2 S
  let C₀ := (Vcirc R p.a).subgroupOf S
  let U₀ := (U R p.a).subgroupOf S
  let D := radicalPreimage Q₀ V₀ Z₀
  let T := (Z R p.a').subgroupOf S
  let := finite_stabilizer R p.a
  let : V₀.Normal := radius_normal p.a
  let : Z₀.Normal := geometry.Z_normal p.a
  let : Q₀.Normal := Q_normal R p.a
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized p.a)
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (U_normalized p.a)
  let : D.Normal := o.natural_section.radical_normal
  have hVS : V R p.a ≤ S := (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hCS : Vcirc R p.a ≤ S := (Vcirc_le_V p.a).trans hVS
  have hUS : U R p.a ≤ S := (U_le_Z p.a).trans (Z_le_stabilizer R p.a)
  have hTS : Z R p.a' ≤ S :=
    (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).2
  have hC : C₀ = ⁅V₀, L₀⁆ := by
    apply map_injective S.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hCS, map_subgroupOf_eq_of_le hVS]
    rfl
  have hU : U₀ = ⁅Z₀, L₀⁆ := by
    apply map_injective S.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hUS,
      map_subgroupOf_eq_of_le (Z_le_stabilizer R p.a)]
    rfl
  have hCQ : ⁅C₀, Q₀⁆ = U₀ := by
    apply map_injective S.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hCS, map_subgroupOf_eq_of_le hUS,
      map_subgroupOf_eq_of_le (show Q R p.a ≤ S from fun _ hx => hx.1)]
    exact hH
  have hCV : C₀ ≤ V₀ := comap_mono (Vcirc_le_V p.a)
  have hVp : IsPGroup 2 V₀ := (source.V_isPGroup geometry hb p.a p.color_a).comap_subtype
  have hCL : ⁅C₀, L₀⁆ = C₀ := by
    rw [hC]
    exact commutator_isPPerfect_idempotent L₀ V₀ (isPPerfect_pResidual 2) hVp
      le_normalizer_of_normal
  have hfull : ⁅C₀, (⊤ : Subgroup S)⁆ = C₀ :=
    le_antisymm (commutator_le_left _ _) (hCL.symm.le.trans (commutator_mono le_rfl le_top))
  have hgen : L₀ ⊔ Q₀ = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show Q R p.a ≤ S from fun _ hx => hx.1),
      ← MonoidHom.range_eq_map, range_subtype]
    exact source.local_generation p.a p.color_a
  have hDV : D ≤ V₀ := sup_le (comap_mono (Z_le_VBall R p.a 2)) (commutator_le_left _ _)
  have hDLZ : ⁅D, L₀⁆ ≤ Z₀ :=
    commutator_sup_bound (commutator_le_left _ _) o.natural_section.triple_le
  have hDL : ⁅D, L₀⁆ ≤ U₀ := by
    rw [← commutator_isPPerfect_idempotent L₀ D (isPPerfect_pResidual 2)
      (hVp.to_le hDV) le_normalizer_of_normal]
    exact (commutator_mono hDLZ le_rfl).trans hU.symm.le
  have hK : ⁅C₀ ⊓ D, (⊤ : Subgroup S)⁆ ≤ U₀ := by
    rw [← hgen, commutator_comm]
    apply commutator_sup_bound
    · rw [commutator_comm]
      exact (commutator_mono inf_le_right le_rfl).trans hDL
    · rw [commutator_comm]
      exact (commutator_mono inf_le_left le_rfl).trans hCQ.le
  let := Kernel.radius_elementary p.a p.color_a hi.six_le
  let : IsElementaryAbelian 2 V₀ := IsElementaryAbelian.subgroupOf hVS
  let : IsElementaryAbelian 2 C₀ := by
    refine {
      toIsMulCommutative := ⟨⟨?_⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    · intro x y
      apply inclusion_injective hCV
      simp only [map_mul, mul_comm]
    · intro x
      apply inclusion_injective hCV
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V₀) (inclusion hCV x)
  let π := localProjection source p.a p.color_a
  have hπ : Function.Surjective π := localProjection_surjective source p.a p.color_a
  have hker : ⁅C₀, π.ker⁆ ≤ U₀ := by
    rw [localProjection_kernel]
    exact hCQ.le
  have hne : ¬ C₀ ≤ U₀ := by
    intro h
    apply radius_moving_not_le_Z source geometry hb modules p.a p.color_a
    have hh := map_mono (f := S.subtype) h
    rw [map_subgroupOf_eq_of_le hCS, map_subgroupOf_eq_of_le hUS] at hh
    exact hh.trans (U_le_Z p.a)
  let ρ := Kernel.action C₀ U₀ π hπ hker
  have hsmallT : Nat.card (commutatorAction (T.map (ρ.comp π)) (C₀ ⧸ U₀.subgroupOf C₀)) ≤ 2 := by
    rw [Kernel.action_comp, quotientAction_displacement_card]
    apply (relIndex_le_of_le_right (commutator_mono hCV le_rfl) (by
      exact index_ne_zero_of_finite)).trans
    have hh := relIndex_map_map_of_injective U₀ ⁅V₀, T⁆ S.subtype_injective
    rw [map_subgroupOf_eq_of_le hUS, map_commutator,
      map_subgroupOf_eq_of_le hVS, map_subgroupOf_eq_of_le hTS] at hh
    rw [← hh]
    exact Kernel.radius_mod_U_index source hb modules p
  have hsmall : HasSmallInvolution ρ := by
    have hrev := source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical
    obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hrev.2
    let g : S := ⟨z, hTS hz⟩
    have hn : π g ≠ 1 := by
      intro he
      have hk : g ∈ π.ker := he
      rw [localProjection_kernel] at hk
      exact hzQ hk
    have ht : (π g) ^ 2 = 1 := by
      let := geometry.Z_elementary (by omega) p.a' p.end_color
      have he : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz
      rw [← map_pow, show g ^ 2 = 1 from Subtype.ext he, map_one]
    refine ⟨π g, hn, ht, ?_⟩
    have hm : ρ (π g) ∈ T.map (ρ.comp π) := mem_map_of_mem (ρ.comp π) hz
    exact (card_le_of_le (displacement_mono (zpowers_le.mpr hm))).trans hsmallT
  have hbound := Kernel.intersection_bound C₀ U₀ π hπ hker hfull hne hsmall (C₀ ⊓ D) hK
  intro x hx
  exact hbound ⟨hx.1, hx⟩

/-- The literal kernel of the restriction to Vcirc is bounded by U.
The global H=U input is used only at the chosen critical-pair vertex. -/
theorem radical_intersection_bound (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (_transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (orientations : ∀ a, color R a = false → Nonempty (MovingOrientationAt a))
    (p : Counterexample geometry) (_bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hH : ∀ a, color R a = false → H R a = U R a) :
    (Vcirc R p.a).subgroupOf (stabilizer R p.a) ⊓
      radicalPreimage ((Q R p.a).subgroupOf (stabilizer R p.a))
        ((V R p.a).subgroupOf (stabilizer R p.a)) ((Z R p.a).subgroupOf (stabilizer R p.a)) ≤
      (U R p.a).subgroupOf (stabilizer R p.a) := by
  obtain ⟨hi⟩ := initial p
  obtain ⟨o⟩ := orientations p.a p.color_a
  exact local_bound source hb modules p hi o (hH p.a p.color_a)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
