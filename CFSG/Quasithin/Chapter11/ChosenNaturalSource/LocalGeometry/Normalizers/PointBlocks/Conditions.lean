module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.RadicalAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs

/-!
# The literal nonbinary point MS-pair

Write J=LR₁ and P=L₁T. The point is not L-invariant: the original central
quotient is irreducible, whereas its flag has distinct one- and two-dimensional
members. Hence P is proper in LT. Normality of J in LT shows that P∩J has
two-core R₁, and the normal-product index formula makes its index in J odd.
Characteristic two and the C-component condition restrict to J. Escape from
N_G(L) gives exactly MS3 with normality inside J.

The resulting NonbinaryMSPair contains the literal C.1.31 premises, with
actual core-quotient isomorphisms to the three nonbinary natural models.
It contains no block or module-classification output. The C.1.32/C.1.34
classification, including the point-radical exclusion, remains separate.
Source: Aschbacher--Smith, combined manuscript, C.1.31, printed p.135,
and the first paragraph of 11.1.5, printed p.765.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem point_join_normal (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    ((L ⊔ f.Ri 0).subgroupOf (L ⊔ (T : Subgroup G))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply sup_le
  · exact le_sup_left.trans (L ⊔ f.Ri 0).le_normalizer
  · exact (le_inf D.sylow_normalizes_component (sylow_normalizes_Ri f 0)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem point_join_component (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    (L.subgroupOf (L ⊔ f.Ri 0)).IsCComponent :=
  S.source.maximal_faithful.1.1.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left ((localRadical_le_sylow _).trans le_sup_right))

theorem point_join_characteristicTwo (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    generalizedFitting (L ⊔ f.Ri 0 : Subgroup G) = pCore 2 (L ⊔ f.Ri 0 : Subgroup G) := by
  have hc : HasCharacteristicTwo (L ⊔ (T : Subgroup G) : Subgroup G) :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (S.source.simpleQTKE.evenCharacteristic T)
      ⟨S.source.maximal_faithful.1.1.2.2, fun _ hx => mem_sup_right hx⟩)
  let := point_join_normal D f
  have hh := normal_core_selfCentralizing hc ((L ⊔ f.Ri 0).subgroupOf (L ⊔ (T : Subgroup G)))
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (sup_le le_sup_left
      ((localRadical_le_sylow _).trans le_sup_right)))).mp hh

theorem point_join_sqtk (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    IsSQTK KnownSimple.IsKnownSimple (L ⊔ f.Ri 0 : Subgroup G) := by
  have hn : L ⊔ f.Ri 0 ≤ normalizer (V : Set G) :=
    sup_le D.normalizes ((localRadical_le_sylow _).trans S.sylow_normalizes)
  have ht : IsTwoLocal (normalizer (V : Set G)) := by
    let := D.elementary
    exact ⟨V, D.ne_bot, IsElementaryAbelian.isPGroup 2 V, rfl⟩
  have hq := (S.source.simpleQTKE.twoLocal_sqtk ht).subgroup ((L ⊔ f.Ri 0).subgroupOf _)
  exact ⟨hq.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hn).symm.toMonoidHom (subgroupOfEquivOfLe hn).symm.injective,
    hq.isKGroup.of_injective (subgroupOfEquivOfLe hn).symm.toMonoidHom
      (subgroupOfEquivOfLe hn).symm.injective⟩

theorem point_join_normalizes (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    L ⊔ (T : Subgroup G) ≤ normalizer ((L ⊔ f.Ri 0 : Subgroup G) : Set G) :=
  sup_le (le_sup_left.trans (L ⊔ f.Ri 0).le_normalizer)
    ((le_inf D.sylow_normalizes_component (sylow_normalizes_Ri f 0)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))

theorem point_not_normalized (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    ¬ L ≤ normalizer (f.Vi 0 : Set G) := by
  intro hn
  have hi := (c.component_normalizes_preimage_iff (f.space 0)).mp hn
  let U : Subrepresentation D.centralQuotientAction :=
    ⟨c.binarySubspace (f.space 0), by
      intro g x hx
      change c.linearEquiv (D.centralQuotientAction g x) ∈ f.space 0
      rw [c.intertwines]
      exact hi _ _ hx⟩
  let := D.centralQuotientAction_irreducible
  rcases eq_bot_or_eq_top U with hb | ht
  · apply f.space_ne_bot 0
    apply bot_unique
    intro x hx
    obtain ⟨y, rfl⟩ := c.linearEquiv.surjective x
    have hy : y ∈ U := hx
    rw [hb] at hy
    change y = 0 at hy
    rw [hy, map_zero]
    exact Submodule.zero_mem _
  · have hs : f.space 0 = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨y, rfl⟩ := c.linearEquiv.surjective x
      have hy : y ∈ U := by rw [ht]; trivial
      exact hy
    have hs' : f.space 1 = ⊤ := top_unique (hs ▸ (f.nested (show (0 : Fin 3) ≤ 1 from by decide)))
    have h0 := f.dimension 0
    have h1 := f.dimension 1
    rw [hs] at h0
    rw [hs'] at h1
    norm_num at h0 h1
    omega

theorem point_parabolic_proper (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    f.Li 0 ⊔ (T : Subgroup G) < L ⊔ (T : Subgroup G) := by
  apply lt_of_le_of_ne
    (sup_le ((localResidual_le _).trans inf_le_left |>.trans le_sup_left) le_sup_right)
  intro he
  apply point_not_normalized D f
  calc
    L ≤ L ⊔ (T : Subgroup G) := le_sup_left
    _ = f.Li 0 ⊔ (T : Subgroup G) := he.symm
    _ ≤ normalizer (f.Vi 0 : Set G) :=
      sup_le ((localResidual_le _).trans inf_le_right) (f.invariant 0)

/-- The MS odd-index witness lives in LR₁: intersect L₁T with LR₁. -/
def pointWitness {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) : Subgroup G :=
  (f.Li 0 ⊔ (T : Subgroup G)) ⊓ (L ⊔ f.Ri 0)

theorem pointWitness_core (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    (pointWitness f).pCoreIn 2 = f.Ri 0 := by
  have hP : f.Li 0 ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
    sup_le ((localResidual_le _).trans inf_le_left |>.trans le_sup_left) le_sup_right
  have hr : f.Ri 0 = (f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2 := rfl
  apply le_antisymm
  · rw [hr]
    apply pCoreIn_mono_of_normalizes (show pointWitness f ≤ f.Li 0 ⊔ (T : Subgroup G) from inf_le_left)
    exact (le_inf (f.Li 0 ⊔ (T : Subgroup G)).le_normalizer
      (hP.trans (point_join_normalizes D f))).trans inf_normalizer_le_normalizer_inf
  · have hi : f.Ri 0 ≤ pointWitness f :=
      le_inf (hr ▸ pCoreIn_le _ _) le_sup_right
    exact (le_inf hi (show f.Ri 0 ≤ (f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2 from le_rfl)).trans
      (inf_pCoreIn_le_of_le 2 (show pointWitness f ≤ f.Li 0 ⊔ (T : Subgroup G) from inf_le_left))

theorem pointWitness_odd (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    Odd ((pointWitness f).subgroupOf (L ⊔ f.Ri 0)).index := by
  let H := L ⊔ (T : Subgroup G)
  let P := f.Li 0 ⊔ (T : Subgroup G)
  let J := L ⊔ f.Ri 0
  have hJH : J ≤ H :=
    sup_le le_sup_left ((localRadical_le_sylow _).trans le_sup_right)
  let : (J.subgroupOf H).Normal := point_join_normal D f
  have hPH : P ≤ H :=
    sup_le ((localResidual_le _).trans inf_le_left |>.trans le_sup_left) le_sup_right
  have hgen : J.subgroupOf H ⊔ P.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hJH hPH]
    apply top_unique
    intro x _
    exact (show H ≤ J ⊔ P from sup_le (le_sup_left.trans le_sup_left)
      (le_sup_right.trans le_sup_right)) x.property
  have he : (P.subgroupOf J).index = (P.subgroupOf H).index := by
    calc
      (P.subgroupOf J).index = (P.subgroupOf H).relIndex (J.subgroupOf H) :=
        (relIndex_subgroupOf hJH).symm
      _ = (P.subgroupOf H).relIndex (J.subgroupOf H ⊔ P.subgroupOf H) :=
        (relIndex_sup_of_normal_left _ _).symm
      _ = (P.subgroupOf H).index := by rw [hgen, relIndex_top_right]
  change Odd ((P ⊓ J).subgroupOf J).index
  rw [inf_subgroupOf_right, he]
  apply Odd.of_dvd_nat _ (index_dvd_of_le (show
    (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right) : Subgroup H) ≤
      P.subgroupOf H from fun x hx => mem_sup_right hx))
  exact Nat.not_even_iff_odd.mp (fun he =>
    (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)).not_dvd_index
      (even_iff_two_dvd.mp he))

theorem pointWitness_proper (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    pointWitness f < L ⊔ f.Ri 0 := by
  have hproper := point_parabolic_proper D f
  apply lt_of_le_of_ne inf_le_right
  intro he
  apply hproper.ne
  apply le_antisymm hproper.le
  apply sup_le _ le_sup_right
  exact (le_sup_left.trans he.ge).trans inf_le_left

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- Every C.1.31 premise for the nonbinary natural rows. The quotient models
are actual full groups, and all normality and index conditions are inside LR. -/
structure NonbinaryMSPair (F : BinaryField) (L R : Subgroup G) : Prop where
  nonbinary : 1 < F.degree
  sqtk : IsSQTK KnownSimple.IsKnownSimple (L ⊔ R : Subgroup G)
  fitting : generalizedFitting (L ⊔ R : Subgroup G) = pCore 2 (L ⊔ R : Subgroup G)
  product : ∀ g ∈ L ⊔ R, ∃ l ∈ L, ∃ r ∈ R, l * r = g
  component : (L.subgroupOf (L ⊔ R)).IsCComponent
  model : Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.G2.Model F.Carrier)
  radical : MSOddIndex L R
  characteristic : MSNoCharacteristicNormal L R

/-- The proper odd-index witness and its core are relative to LR₁. -/
theorem point_ms_oddIndex (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) : MSOddIndex L (f.Ri 0) :=
  ⟨pointWitness f, pointWitness_proper D f, pointWitness_odd D f, pointWitness_core D f⟩

/-- The source point gives all MS premises; no classification premise is used. -/
theorem point_msPair (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    NonbinaryMSPair S.field L (f.Ri 0) := by
  refine ⟨S.nonbinary, point_join_sqtk D S f, point_join_characteristicTwo D S f,
    ?_, point_join_component D S f, ?_, point_ms_oddIndex D f, ?_⟩
  · intro g hg
    have hn : f.Ri 0 ≤ normalizer (L : Set G) :=
      (localRadical_le_sylow _).trans D.sylow_normalizes_component
    have hp : g ∈ (L : Set G) * (f.Ri 0 : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (f.Ri 0) hn]
      exact hg
    exact hp
  · cases c with
    | sl3 m => exact Or.inl ⟨m.groupEquiv⟩
    | sp4 m => exact Or.inr (Or.inl ⟨m.groupEquiv⟩)
    | g2 m => exact Or.inr (Or.inr ⟨m.groupEquiv⟩)
  · intro C hc hn
    by_contra hne
    exact point_ms_no_characteristic_normal D S f hescape C hc hne hn

/-- The linear marking supplies the existing literal C.1.34 input, with no
binary restriction and with the full SL₃ quotient unchanged. -/
theorem point_linearThreeMSPair (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (hm : NonbinaryMSPair S.field L (f.Ri 0)) :
    LinearThreeMSPair KnownSimple.IsKnownSimple L (f.Ri 0)
      S.field.degree S.field.Carrier := by
  exact ⟨S.field.degree_pos, S.field.card_eq, ⟨m.groupEquiv⟩, hm.sqtk, hm.fitting,
    ⟨le_sup_left, hm.component⟩, Or.inl hm.radical, hm.characteristic⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
