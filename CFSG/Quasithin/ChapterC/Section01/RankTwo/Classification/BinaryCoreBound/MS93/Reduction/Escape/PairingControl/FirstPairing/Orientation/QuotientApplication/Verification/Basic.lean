module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Source

/-!
# Elementary and fixed-preimage obligations for the selected quotient seed

The parabolic seed and its ambient normal closure stay in the actual image
of V_alpha. Elementary V_alpha/Z_alpha therefore bounds the Frattini
subgroup by the Z-image. The image of B_alpha centralizes the actual
component modulo that image. Extending the selected cyclic commutator
bound through the parabolic normal closure proves fixation modulo exactly
C = fixedPreimage(component, X, Z-image).

We also retain the original cyclic generator in the enlarged seed's
normal closure and transport the moving-neighbor pairing estimates to
G_alpha/D_alpha. Once moving generation is supplied, a trivial seed
pairing would force H_alpha into D_alpha, contradicting the bad branch.
No later escape conclusions enter these deductions.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7) on pp.847--848 and
the first quotient application in (4.3.2)(2), printed p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing
variable {M : Type*} [Group M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}

namespace SelectedSeed
variable (s : SelectedSeed geometry a f)

/-- Adjoining Z and taking the local closure stay inside the radius group. -/
theorem X_le_V : s.X ≤ quotientImage a (V R a) := by
  let := quotientImage_normal a (V R a) (V_normalized a)
  apply sup_le
  · exact map_mono (comap_mono (Z_le_VBall R a 2))
  · apply Incidence.localGenerated_le_of_normalizes _ _ _ le_normalizer_of_normal
    exact zpowers_le.mpr (mem_map_of_mem _ (moving_Z_le_V s.moving s.element_mem))

/-- Normality of V bounds the ambient closure of the selected seed. -/
theorem generated_X_le_V : generated s.X ≤ quotientImage a (V R a) := by
  let := quotientImage_normal a (V R a) (V_normalized a)
  exact normalClosure_le_normal s.X_le_V

variable [Finite M]

/-- The ambient closure is a two-group in the actual local quotient. -/
theorem generated_X_isPGroup (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) : IsPGroup 2 (generated s.X) := by
  have hVQ : quotientImage a (V R a) ≤ quotientImage a (Q R a) :=
    map_mono (comap_mono (geometry.V_le_Q hb a ha))
  exact ((Q_isPGroup R source.two_group source.core_le a ha).comap_subtype.map
    (quotientMap a)).to_le (s.generated_X_le_V.trans hVQ)

omit [Finite M] in
private theorem square_mem_Z (x : LocalQuotient a) (hx : x ∈ generated s.X) :
    x ^ 2 ∈ quotientImage a (Z R a) := by
  let := f.natural_section.normal_kernel
  let := f.natural_section.elementary
  obtain ⟨v, hv, rfl⟩ := s.generated_X_le_V hx
  let v' : (V R a).subgroupOf (stabilizer R a) := ⟨v, hv⟩
  have hp : (v' ^ 2 : (V R a).subgroupOf (stabilizer R a)) ∈
      ((Z R a).subgroupOf (stabilizer R a)).subgroupOf
        ((V R a).subgroupOf (stabilizer R a)) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk'
      (((Z R a).subgroupOf (stabilizer R a)).subgroupOf
        ((V R a).subgroupOf (stabilizer R a))) v') ^ 2 = 1
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) _
  rw [← map_pow]
  exact mem_map_of_mem _ hp

/-- Elementary V/Z supplies the Frattini hypothesis of (1.7). -/
theorem frattini_le (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) :
    (frattini (generated s.X)).map (generated s.X).subtype ≤ quotientImage a (Z R a) := by
  let : Fact (IsPGroup 2 (generated s.X)) := ⟨s.generated_X_isPGroup source hb ha⟩
  rw [map_le_iff_le_comap, frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (closure_le _).mpr
  rintro x (hx | ⟨y, rfl⟩)
  · have hc : _root_.commutator (generated s.X) ≤
        (quotientImage a (Z R a)).comap (generated s.X).subtype := by
      rw [commutator_def]
      apply commutator_le.mpr
      intro u _ v _
      change ⁅(u : LocalQuotient a), (v : LocalQuotient a)⁆ ∈ quotientImage a (Z R a)
      have he : ⁅(u : LocalQuotient a), (v : LocalQuotient a)⁆ =
          (u : LocalQuotient a) ^ 2 * ((u : LocalQuotient a)⁻¹ * v) ^ 2 *
            ((v : LocalQuotient a) ^ 2)⁻¹ := by
        simp [commutatorElement_def, pow_two, mul_assoc]
      rw [he]
      exact (quotientImage a (Z R a)).mul_mem
        ((quotientImage a (Z R a)).mul_mem (s.square_mem_Z _ u.property)
          (s.square_mem_Z _ ((generated s.X).mul_mem
            ((generated s.X).inv_mem u.property) v.property)))
        ((quotientImage a (Z R a)).inv_mem (s.square_mem_Z _ v.property))
    exact hc hx
  · exact s.square_mem_Z _ y.property

omit [Finite M] in
/-- The image of Q is contained in both marked parabolic preimages. -/
theorem Q_le_parabolic (i : Bool) :
    quotientImage a (Q R a) ≤ parabolic (projection f) s.flag i := by
  intro x hx
  have hk : x ∈ (projection f).ker := by
    rw [projection, quotientProjection_kernel]
    exact hx
  change projection f x ∈ modelParabolic s.flag i
  rw [MonoidHom.mem_ker.mp hk]
  exact one_mem _

/-- The cyclic generator lies in its actual relative parabolic closure. -/
theorem cyclic_le_raw (hb : 2 < geometry.b R) (ha : color R a = false) :
    zpowers (quotientMap a s.element) ≤ s.raw := by
  apply le_localGenerated
  have heQ : s.element ∈ (Q R a).subgroupOf (stabilizer R a) :=
    geometry.V_le_Q hb a ha (moving_Z_le_V s.moving s.element_mem)
  exact (zpowers_le.mpr (mem_map_of_mem (quotientMap a) heQ)).trans
    (s.Q_le_parabolic s.side)

/-- In particular the enlarged seed retains the cyclic generator. -/
theorem cyclic_le_X (hb : 2 < geometry.b R) (ha : color R a = false) :
    zpowers (quotientMap a s.element) ≤ s.X :=
  (s.cyclic_le_raw hb ha).trans le_sup_right

/-- The enlarged seed is contained in both local parabolics. -/
theorem X_le_parabolic (hb : 2 < geometry.b R) (ha : color R a = false) (i : Bool) :
    s.X ≤ parabolic (projection f) s.flag i :=
  (s.X_le_Q hb ha).trans (s.Q_le_parabolic i)

/-- The ambient closure of X is Z joined with the closure of the original
cyclic image; this does not identify X with the raw parabolic closure. -/
theorem generated_X_eq (hb : 2 < geometry.b R) (ha : color R a = false) :
    generated s.X = quotientImage a (Z R a) ⊔
      generated (zpowers (quotientMap a s.element)) := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  apply le_antisymm
  · apply normalClosure_le_normal
    exact sup_le le_sup_left (localGenerated_le_generated _ _ |>.trans le_sup_right)
  · exact sup_le (s.Z_le_X.trans le_normalClosure)
      (normalClosure_le_normal ((s.cyclic_le_X hb ha).trans le_normalClosure))

end SelectedSeed

variable [Finite M]

/-- B maps into the actual fixed preimage for the quotient component. -/
theorem quotientImage_B_le_fixed (source : LocalSource L R)
    (ha : color R a = false) (flag : SL) :
    letI := quotientImage_normal a (Z R a) (Z_normalized R a)
    quotientImage a (B R a (geometry.Z_normal a)) ≤
      centralizerModulo (quotientImage a (V R a)) (component (projection f) flag)
        (quotientImage a (Z R a)) := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  let := geometry.Z_normal a
  rw [quotient_component (source := source) a ha f flag]
  rintro _ ⟨b, hb, rfl⟩
  have hb' : b ∈ centralizerModulo ((V R a).subgroupOf (stabilizer R a))
      (pResidual 2 (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)) := by
    change b ∈ ((centralizerModulo ((V R a).subgroupOf (stabilizer R a))
      (pResidual 2 (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a))).map
        (stabilizer R a).subtype).comap (stabilizer R a).subtype at hb
    rwa [comap_map_eq_self_of_injective (stabilizer R a).subtype_injective] at hb
  obtain ⟨hbV, hbL⟩ := mem_centralizerModulo_iff.mp hb'
  apply mem_centralizerModulo_iff.mpr
  refine ⟨mem_map_of_mem _ hbV, ?_⟩
  simp only [quotientImage, Ltilde_subgroupOf]
  rintro _ ⟨l, hl, rfl⟩
  rw [← map_commutatorElement]
  exact mem_map_of_mem _ (hbL l hl)

namespace SelectedSeed
variable (s : SelectedSeed geometry a f)

/-- In this application the component is normal, so its fixed preimage
is normal in the full local quotient. -/
theorem C_normal (source : LocalSource L R) (ha : color R a = false) : s.C.Normal := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  have hc : (component (projection f) s.flag).Normal :=
    component_normal (s.extension source ha)
  let := hc
  let : ((component (projection f) s.flag).map
      (QuotientGroup.mk' (quotientImage a (Z R a)))).Normal :=
    Normal.map hc _ (QuotientGroup.mk'_surjective _)
  change (generated s.X ⊓
    (centralizer ((component (projection f) s.flag).map
      (QuotientGroup.mk' (quotientImage a (Z R a))) : Set _)).comap
        (QuotientGroup.mk' (quotientImage a (Z R a)))).Normal
  infer_instance

/-- The actual selected residual fixes X modulo the exact denominator C. -/
theorem seed_fixed (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) :
    ⁅s.X, localResidual (parabolic (projection f) s.flag s.side)⁆ ≤ s.C := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  let := s.C_normal source ha
  let P := parabolic (projection f) s.flag s.side
  let T := localResidual P
  have hPT : P ≤ normalizer (T : Set (LocalQuotient a)) := by
    intro t ht
    apply (primeToResidual 2 P).le_normalizer_map P.subtype
    exact ⟨⟨t, ht⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  have hcyc : ⁅zpowers (quotientMap a s.element), T⁆ ≤ s.C := by
    intro x hx
    apply mem_fixedPreimage _ _ _ x |>.mpr
    refine ⟨?_, ?_⟩
    · exact (commutator_mono ((s.cyclic_le_X hb ha).trans le_normalClosure) le_rfl |>.trans
        (commutator_le_left (generated s.X) T)) hx
    · exact (mem_centralizerModulo_iff.mp
        (quotientImage_B_le_fixed (geometry := geometry) source ha s.flag (s.fixes_seed hx))).2
  have hraw : ⁅s.raw, T⁆ ≤ s.C :=
    Incidence.localGenerated_commutator_bound P _ T s.C hPT hcyc
  have hZ : ⁅quotientImage a (Z R a), T⁆ ≤ s.C :=
    (commutator_le_left _ _).trans (le_fixedPreimage _ _ _ s.Z_le_X)
  have hX : s.X ≤ commutatorPreimage ⊤ T s.C :=
    sup_le (le_commutatorPreimage le_top hZ) (le_commutatorPreimage le_top hraw)
  exact (commutator_mono hX le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ T s.C le_normalizer_of_normal)

/-- Moving generation makes a trivial seed pairing contradict the bad branch. -/
theorem commutator_nontrivial_of_moving_le
    {p : Counterexample geometry} {f : FrameAt p.a} (s : SelectedSeed geometry p.a f)
    (hb : 2 < geometry.b R) (transfer : NormalizationTransfer R)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hmoving : quotientImage p.a (Vcirc R p.a) ≤ generated s.X) :
    Nat.card (⁅s.X, quotientImage p.a (Q R p.a)⁆ : Subgroup (LocalQuotient p.a)) ≠ 1 := by
  intro hc
  let := quotientImage_normal p.a (Q R p.a) (Q_normalized R p.a)
  have hfix : generated s.X ≤ centralizer (quotientImage p.a (Q R p.a) : Set _) :=
    normalClosure_le_normal (commutator_eq_bot_iff_le_centralizer.mp (eq_bot_of_card_eq _ hc))
  have hVcirc : Vcirc R p.a ≤ stabilizer R p.a :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le
      ((geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1))
      (Ltilde_le_stabilizer p.a))
  apply H_not_le_fixed transfer bad
  exact (quotient_commutator_eq_bot_iff p.a (Vcirc R p.a) (Q R p.a)
    hVcirc (fun _ hx => hx.1)).mp
      (commutator_eq_bot_iff_le_centralizer.mpr (hmoving.trans hfix))

end SelectedSeed
/-- The genuine moving-neighbor pairing survives in G_alpha/D_alpha. -/
theorem quotient_moving_commutator_nontrivial
    (hb : 2 < geometry.b R) (transfer : NormalizationTransfer R)
    {p : Counterexample geometry} (initial : InitialFacts p)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {d : Vertex R} (hd : d ∈ movingNeighbors geometry p.a) :
    Nat.card (⁅quotientImage p.a (Z R d), quotientImage p.a (Q R p.a)⁆ :
      Subgroup (LocalQuotient p.a)) ≠ 1 := by
  intro hc
  apply moving_commutator_not_le_fixed hb transfer initial bad hd
  apply (quotient_commutator_eq_bot_iff p.a (Z R d) (Q R p.a)
    ((moving_Z_le_V hd).trans ((geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)))
    (fun _ hx => hx.1)).mp
  exact eq_bot_of_card_eq _ hc

/-- Passing to the actual fixed-core quotient cannot enlarge the pairing. -/
theorem quotient_moving_commutator_card_le_four
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (ha : color R a = false)
    {d : Vertex R} (hd : d ∈ movingNeighbors geometry a) :
    Nat.card (⁅quotientImage a (Z R d), quotientImage a (Q R a)⁆ :
      Subgroup (LocalQuotient a)) ≤ 4 := by
  have hZS : Z R d ≤ stabilizer R a :=
    (moving_Z_le_V hd).trans ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1))
  have hQS : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hCS : ⁅Z R d, Q R a⁆ ≤ stabilizer R a :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hZS hQS)
  rw [← quotientImage_commutator a _ _ hZS hQS]
  let := finite_stabilizer R a
  have hle : Nat.card (quotientImage a ⁅Z R d, Q R a⁆) ≤
      Nat.card (⁅Z R d, Q R a⁆.subgroupOf (stabilizer R a)) :=
    Nat.le_of_dvd Nat.card_pos ((⁅Z R d, Q R a⁆.subgroupOf (stabilizer R a)).card_map_dvd _)
  rw [Nat.card_congr (subgroupOfEquivOfLe hCS).toEquiv] at hle
  exact hle.trans (moving_commutator_card_le_four source hb modules ha hd)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
