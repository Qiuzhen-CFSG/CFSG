module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoordinates
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearCubic
public import Theory.SpecificGroups.PSL3.LinearThreeRadicalCubic

/-!
# The secondary radical image and the scope of torus movement

The literal projection of K₂ onto the point local of SL₃ carries O₂(K₂)
onto its root plane. Its kernel is K₂ ∩ O₂(K), so the relative index is
2^(2n). Since O₂(K₂) lies in R₂, this proves Q < R₂ and shows that R₂ is
not contained in the original O₂(K).

Consequently no subgroup of O₂,Z(K) can satisfy Q[R₂,X] = R₂. In the
four-element case, every cubic subgroup of K which preserves the root
and centralizes K₂/O₂(K₂) lies in O₂,Z(K): this follows from the explicit
matrix calculation on the actual secondary projection. The source cubic
moves Q but does not move R₂ modulo Q.

The final diagnostic therefore rules out the current SecondaryData record
with the source placement torus ≤ K when n=2. Its universal
radical_mod_core_moved field is stronger than the printed argument, where
movement is invoked only during elimination of cases (1)--(3). The result
is an obstruction to that intermediate interface, not a counterexample to
the ambient source theorem or a proof of the nonblock exclusion. Existing
conditional APIs are preserved. A corrected secondary interface, the
nonbinary MS construction and final assembly remain with
qt-d-1222-rankone-uniqueness-nonblock; the independent full quotient sieve
remains with qt-d-1222-nonblock-endgame-sieve.

Source: Aschbacher--Smith, original 4.3.10--16 and conclusion of 4.3.2,
printed pp.617--619, especially the case-dependent paragraph on p.618.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}

namespace RootCoordinates
variable (m : RootCoordinates d)

theorem secondary_core_image (hn : 1 < n) :
    (pCore 2 (secondary c)).map m.secondaryProjection =
      pCore 2 (pointLocalSL d.field.Carrier) := by
  rw [←m.secondaryProjection.comap_pCore_of_ker_isPGroup
    (m.secondaryProjection_surjective hn) m.secondaryProjection_kernel,
    map_comap_eq_self_of_surjective (m.secondaryProjection_surjective hn)]

omit [Finite G] in
theorem secondary_core_le_radical (D : Chapter12.Section02.ChosenModule T L V) :
    (secondary c).pCoreIn 2 ≤ R₂ c := by
  apply pCoreIn_mono_of_normalizes le_sup_left
  exact sup_le (secondary c).le_normalizer (sylow_normalizes_secondary D)

include m
omit [Finite G] in
theorem secondaryProjection_ker : m.secondaryProjection.ker =
    ((K c).pCoreIn 2).subgroupOf (secondary c) := by
  ext x
  change m.secondaryProjection x = 1 ↔ (x : G) ∈ (pCore 2 (K c)).map (K c).subtype
  change m.secondaryProjection x = 1 ↔
    (K c).subtype (⟨x,secondary_le_original x.property⟩ : K c) ∈ (pCore 2 (K c)).map (K c).subtype
  rw [mem_map_iff_mem (K c).subtype_injective]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff _).mp
    apply d.model.injective
    change linearThreeActor d.model ⟨x,secondary_le_original x.property⟩ = d.model 1
    rw [map_one]
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    change linearThreeActor d.model ⟨x,secondary_le_original x.property⟩ = 1
    change d.model (QuotientGroup.mk' (pCore 2 (K c)) _) = 1
    exact (congrArg d.model ((QuotientGroup.eq_one_iff _).mpr hx)).trans d.model.map_one

theorem secondary_core_relIndex (hn : 1 < n) :
    ((K c).pCoreIn 2).relIndex ((secondary c).pCoreIn 2) = (2 ^ n) ^ 2 := by
  have hh := relIndex_ker (pCore 2 (secondary c)) m.secondaryProjection
  rw [m.secondary_core_image hn,card_pointLocalSL_twoCore,d.field.card_eq,d.degree_eq,
    m.secondaryProjection_ker] at hh
  change (((K c).pCoreIn 2).comap (secondary c).subtype).relIndex
    (pCore 2 (secondary c)) = _ at hh
  rwa [relIndex_comap] at hh

theorem radical_core_relIndex_lower (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (2 ^ n) ^ 2 ≤ ((K c).pCoreIn 2).relIndex (R₂ c) := by
  rw [←m.secondary_core_relIndex hn]
  exact relIndex_le_of_le_right (secondary_core_le_radical D)
    (Subgroup.FiniteIndex.index_ne_zero (H := ((K c).pCoreIn 2).subgroupOf (R₂ c)))

theorem radical_not_le_original_core (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) : ¬ R₂ c ≤ (K c).pCoreIn 2 := by
  intro hR
  have hh := m.radical_core_relIndex_lower hn D
  rw [relIndex_eq_one.mpr hR] at hh
  have hp : 1 < (2 ^ n) ^ 2 :=
    one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by decide)
  omega

theorem core_lt_radical (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) : Q c < R₂ c := by
  refine lt_of_le_of_ne (core_le_radical c) ?_
  intro he
  apply m.radical_not_le_original_core hn D
  rw [←he]
  exact le_normalizer_iff_commutator_le_left.mp
    ((K c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))

theorem coreCenter_not_move_radical (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (X : Subgroup G) (hX : X ≤ (K c).coreCenterIn 2) :
    Q c ⊔ ⁅R₂ c,X⁆ ≠ R₂ c := by
  intro he
  have hRXK : ⁅R₂ c,X⁆ ≤ K c :=
    (commutator_mono le_rfl (hX.trans (coreCenterIn_le 2 _))).trans
      (le_normalizer_iff_commutator_le_right.mp
        (((radical_le_sylow c).trans inf_le_right).trans c.normalizer_component.le))
  have hQcore : Q c ≤ (K c).pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp
      ((K c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))
  have hRK : R₂ c ≤ K c := by
    rw [←he]
    exact sup_le (hQcore.trans (pCoreIn_le 2 _)) hRXK
  have hcomm : ⁅R₂ c,X⁆ ≤ (K c).pCoreIn 2 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx r hr
    exact ((mem_coreCenterIn_iff 2 (K c) x).mp (hX hx)).2 r (hRK hr)
  apply m.radical_not_le_original_core hn D
  rw [←he]
  exact sup_le hQcore hcomm

theorem radical_not_moved_by_coreCenter (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (X : Subgroup G) (hX : X ≤ (K c).coreCenterIn 2) : ⁅R₂ c,X⁆ ≠ R₂ c := by
  intro he
  apply m.coreCenter_not_move_radical hn D X hX
  rw [he,sup_eq_right.mpr (core_le_radical c)]

omit [Finite G] in
theorem actor_mem_pointParabolic (k : K c) (hk : (k : G) ∈ rootNormalizer c) :
    linearThreeActor d.model k ∈ pointParabolicSL d.field.Carrier := by
  let v : Fin 3 → d.field.Carrier := ![1,0,0]
  let u : U c := m.coordinates.symm (Multiplicative.ofAdd v)
  have hu : (u : G) ∈ root c := (m.root_coordinates u).mpr ⟨1,by simp [u,v]⟩
  let u' : U c := ⟨k * (u : G) * (k : G)⁻¹,
    (mem_normalizer_iff.mp (d.natural.2.1 k.property) u).mp u.property⟩
  have hu' : (u' : G) ∈ root c := (mem_normalizer_iff.mp hk u).mp hu
  obtain ⟨a,ha⟩ := (m.root_coordinates u').mp hu'
  have he := m.compatible k u u' rfl
  have hv : (linearThreeActor d.model k).val.mulVec v = a • v := by
    simpa only [u,MulEquiv.apply_symm_apply,toAdd_ofAdd,
      Representation.specialLinearNatural_apply] using he.symm.trans ha
  apply (mem_pointParabolicSL_iff _ _).mpr
  exact ⟨by simpa [v,Matrix.mulVec,dotProduct,Fin.sum_univ_three] using congrFun hv 1,
    by simpa [v,Matrix.mulVec,dotProduct,Fin.sum_univ_three] using congrFun hv 2⟩

theorem cubic_mem_coreCenter (hn : 1 < n) (hF : Nat.card d.field.Carrier = 4)
    (k : K c) (hk : (k : G) ∈ rootNormalizer c) (hk3 : k ^ 3 = 1)
    (hc : ∀ y ∈ secondary c, ⁅(k : G),y⁆ ∈ (secondary c).pCoreIn 2) :
    (k : G) ∈ (K c).coreCenterIn 2 := by
  have hcentral : linearThreeActor d.model k ∈
      center (Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) := by
    apply cubic_pointParabolic_central_of_core_action hF _ (m.actor_mem_pointParabolic k hk)
      (by rw [←map_pow,hk3,map_one])
    intro b hb
    obtain ⟨y,hy⟩ := m.secondaryProjection_surjective hn ⟨b,hb⟩
    obtain ⟨z,hz,hze⟩ := hc y y.property
    have hzi := (m.secondary_core_image hn).le (mem_map_of_mem _ hz)
    rw [pointLocalSL_twoCore_eq] at hzi
    refine ⟨m.secondaryProjection z,hzi,?_⟩
    change linearThreeActor d.model ⟨z,secondary_le_original z.property⟩ =
      ⁅linearThreeActor d.model k,b⁆
    have hzK : (⟨z,secondary_le_original z.property⟩ : K c) =
        ⁅k,⟨y,secondary_le_original y.property⟩⁆ := Subtype.ext hze
    rw [hzK,map_commutatorElement]
    exact congrArg (fun a => ⁅linearThreeActor d.model k,a⁆) (congrArg Subtype.val hy)
  apply (mem_coreCenterIn_iff 2 (K c) _).mpr
  refine ⟨k.property,?_⟩
  intro b hb
  refine ⟨⁅k,⟨b,hb⟩⁆,?_,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  apply d.model.injective
  change linearThreeActor d.model ⁅k,⟨b,hb⟩⁆ = d.model 1
  rw [map_commutatorElement,map_one]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((mem_center_iff.mp hcentral (linearThreeActor d.model ⟨b,hb⟩)).symm)

theorem cubic_subgroup_le_coreCenter (hn : 1 < n) (hF : Nat.card d.field.Carrier = 4)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ K c)
    (hXroot : X ≤ rootNormalizer c)
    (hXsec : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2) :
    X ≤ (K c).coreCenterIn 2 := by
  intro x hx
  let k : K c := ⟨x,hXK hx⟩
  have hk3 : k ^ 3 = 1 := by
    apply Subtype.ext
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : X)))
    simpa only [hX,Subgroup.coe_pow,Subgroup.coe_one] using hh
  apply m.cubic_mem_coreCenter hn hF k (hXroot hx) hk3
  intro y hy
  rw [commutator_comm] at hXsec
  exact hXsec (commutator_mem_commutator hx hy)

end RootCoordinates
/-- Diagnostic for the universal movement clause: when n=2, the source torus
inside K cannot satisfy the current SecondaryData record. -/
theorem MSData.no_secondaryData_with_original_torus (d : MSData c 2)
    (m : RootCoordinates d) (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryData c 2) (hYK : s.torus ≤ K c) : False := by
  have hF : Nat.card d.field.Carrier = 4 := by rw [d.field.card_eq,d.degree_eq]; norm_num
  have hY : Nat.card s.torus = 3 := by simpa using s.torus_card
  have hz := m.cubic_subgroup_le_coreCenter (by decide) hF s.torus hY hYK
    s.torus_le s.torus_secondary
  exact m.coreCenter_not_move_radical (by decide) D s.torus hz s.radical_mod_core_moved

/-- The original constructed cubic moves Q, but cannot move all of R₂,
nor generate R₂ together with Q. All maps and subgroups are the source ones. -/
theorem MSData.exists_source_cubic_with_radical_obstruction (d : MSData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) =
      lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) =
      unipotentSL d.field.Carrier) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ X ⊓ Subgroup.centralizer (root c : Set G) = ⊥ ∧
      ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2 ∧ ⁅Q c,X⁆ = Q c ∧
      Q c < R₂ c ∧ Q c ⊔ ⁅R₂ c,X⁆ ≠ R₂ c ∧ ⁅R₂ c,X⁆ ≠ R₂ c := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨X,hX,hXK,hr,_,hf,_,_,hsec,hQ,_⟩ := d.exists_source_cubic_root D
  exact ⟨X,hX,hXK,hr,hf,hsec,hQ,m.core_lt_radical (by decide) D,
    m.coreCenter_not_move_radical (by decide) D X hXK,
    m.radical_not_moved_by_coreCenter (by decide) D X hXK⟩

/-- The two original parabolic/Sylow markings suffice for the diagnostic;
no secondary radical size or separate root coordinates are assumed. -/
theorem MSData.no_secondaryData_with_original_torus_of_marked_parabolic
    (d : MSData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) =
      lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) =
      unipotentSL d.field.Carrier)
    (s : SecondaryData c 2) (hYK : s.torus ≤ K c) : False := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact d.no_secondaryData_with_original_torus m D s hYK

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
