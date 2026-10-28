module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Actual actions and local inputs for the nonblock endgame

The full root normalizer is a two-local containing T, hence is SQTK and
has characteristic two. Subnormal inheritance gives F*(K_Z) = O₂(K_Z).
Relative normality and the original enlarged-core bound also put the
embedded O₂(K_Z) inside the actual R₂.

The original torus has trivial intersection with K₂, normalizes K₂,
and has cyclic nontrivial image on K_Z/O₂(K_Z). Cauchy's theorem produces
an odd-prime-order automorphism in this image, with its original torus
preimage and a prime dividing 2ⁿ - 1. Only the induced automorphism is
asserted to have prime order. The literal inclusion K₂ → K_Z and projection
to the full quotient identify its conjugation action and perfect image.
No further central quotient or abstract subgroup marking is substituted.

These results supply common inputs to the local automorphism sieve and
the exceptional module branches. The sieve, the U₃(5) chief-factor
contradiction and the L₃(4) extension argument are not asserted here.
In particular, centralizing the quotient of K₂ by its two-core has not
been replaced by centralizing K₂'s entire action image.

Adapted from the saved `NonblockEndgameActions.lean` in the parent task;
these declarations are checked independently in this module.

Source: Aschbacher–Smith, original 4.3.12–16 and conclusion of 4.3.2,
printed pp.617–619; characteristic-two inheritance 1.1.3–4, pp.500–501.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The nontrivial root is a two-group, so its full normalizer is two-local. -/
theorem rootNormalizer_twoLocal (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) : IsTwoLocal (rootNormalizer c) := by
  let := c.c28.module_elementary
  exact ⟨root c, root_ne_bot c D,
    (IsElementaryAbelian.isPGroup 2 (W c)).to_le inf_le_left, rfl⟩

/-- The actual root normalizer satisfies the SQTK input of A.3.18. -/
theorem rootNormalizer_sqtk (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple (rootNormalizer c) :=
  h.simpleQTKE.twoLocal_sqtk (rootNormalizer_twoLocal c D)

/-- Condition (E) applies because the root normalizer contains T. -/
theorem rootNormalizer_characteristicTwo (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    HasCharacteristicTwo (rootNormalizer c) :=
  Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.simpleQTKE.evenCharacteristic T) (rootNormalizer_twoLocal c D) (root_normalized c D))

/-- The characteristic-two claim used for the original exceptional component. -/
theorem SecondaryData.component_fitting (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    generalizedFitting s.component = pCore 2 s.component :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (subnormal_core_selfCentralizing (rootNormalizer_characteristicTwo c D h)
      s.component s.isComponent.subnormal)

omit [Finite G] in
/-- Relative normality gives normalization of the component embedded in G. -/
theorem SecondaryData.component_normalized (s : SecondaryData c n) :
    rootNormalizer c ≤ normalizer (s.component.map (rootNormalizer c).subtype : Set G) := by
  let := s.normal
  have h := s.component.le_normalizer_map (rootNormalizer c).subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h

omit [Finite G] in
/-- The original component core lies in R₂, as needed for the chief-factor comparison. -/
theorem SecondaryData.component_core_le (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (s.component.map (rootNormalizer c).subtype).pCoreIn 2 ≤ R₂ c := by
  exact (pCoreIn_mono_of_normalizes le_sup_left
    ((sup_le (map_subtype_le _) (root_normalized c D)).trans (SecondaryData.component_normalized s))).trans
      s.enlarged_core_le

omit [Finite G] in
/-- The literal solvable residual K₂ still centralizes the root. -/
theorem secondary_le_centralizer (c : SourceConfiguration T L) :
    secondary c ≤ centralizer (root c : Set G) :=
  (map_subtype_le _).trans inf_le_right

omit [Finite G] in
/-- Faithfulness on the root separates the actual torus from K₂. -/
theorem SecondaryData.torus_disjoint_secondary (s : SecondaryData c n) :
    s.torus ⊓ secondary c = ⊥ :=
  bot_unique ((inf_le_inf_left _ (secondary_le_centralizer c)).trans_eq s.torus_faithful)

omit [Finite G] in
/-- The specified commutator bound gives normalization of the actual K₂. -/
theorem SecondaryData.torus_normalizes_secondary (s : SecondaryData c n) :
    s.torus ≤ normalizer (secondary c : Set G) :=
  le_normalizer_iff_commutator_le_left.mpr
    (s.torus_secondary.trans (pCoreIn_le 2 (secondary c)))

omit [Finite G] in
/-- The characteristic normalizer bound places the original torus inside H. -/
theorem SecondaryData.torus_le_H (s : SecondaryData c n) : s.torus ≤ c.H :=
  s.torus_normalizes_radical.trans (s.radical_normalizer.trans inf_le_left)

omit [Finite G] in
/-- The torus normalizes the actual original K. Containment in K is not asserted. -/
theorem SecondaryData.torus_normalizes_original (s : SecondaryData c n) :
    s.torus ≤ normalizer (K c : Set G) :=
  (SecondaryData.torus_le_H s).trans c.normalizer_component.le

/-- The actual torus image on the full K_Z/O₂(K_Z). -/
def SecondaryData.torusImage (s : SecondaryData c n) :
    Subgroup (MulAut (s.component ⧸ pCore 2 s.component)) :=
  (s.torus.subgroupOf (rootNormalizer c)).map s.action

omit [Finite G] in
/-- The order of the action image divides the original torus order. -/
theorem SecondaryData.torusImage_card_dvd (s : SecondaryData c n) :
    Nat.card (SecondaryData.torusImage s) ∣ 2 ^ n - 1 := by
  have hc := (s.torus.subgroupOf (rootNormalizer c)).card_map_dvd s.action
  rw [Nat.card_congr (subgroupOfEquivOfLe s.torus_le).toEquiv, s.torus_card] at hc
  exact hc

omit [Finite G] in
/-- Cyclicity descends through the actual quotient-action map. -/
theorem SecondaryData.torusImage_cyclic (s : SecondaryData c n) : IsCyclic (SecondaryData.torusImage s) := by
  let := s.torus_cyclic
  let := isCyclic_of_surjective (subgroupOfEquivOfLe s.torus_le).symm
    (subgroupOfEquivOfLe s.torus_le).symm.surjective
  exact isCyclic_of_surjective (s.action.subgroupMap _) (s.action.subgroupMap_surjective _)


/-- A nontrivial odd-prime action with its original torus preimage.
The order assertion concerns the action, not the preimage. -/
theorem SecondaryData.torus_prime_action (s : SecondaryData c n) (hn : 0 < n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ 2 ^ n - 1 ∧
      ∃ y : rootNormalizer c, (y : G) ∈ s.torus ∧ orderOf (s.action y) = p := by
  have hne : Nat.card (SecondaryData.torusImage s) ≠ 1 := fun he =>
    s.torus_action_ne_bot ((SecondaryData.torusImage s).eq_bot_of_card_eq he)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hd := hpd.trans (SecondaryData.torusImage_card_dvd s)
  have ho : Odd (2 ^ n - 1) := by
    rw [Nat.odd_iff]
    have h2 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))
    have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    omega
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := (SecondaryData.torusImage s)) p hpd
  obtain ⟨y, hy, he⟩ := a.property
  refine ⟨p, hp, ho.of_dvd_nat hd, hd, y, hy, ?_⟩
  rw [he, Subgroup.orderOf_coe]
  exact ha

/-- The original inclusion K₂ ≤ K_Z, with both ambient subtype maps retained. -/
def SecondaryData.secondaryToComponent (s : SecondaryData c n) :
    secondary c →* s.component where
  toFun x := ⟨⟨x, (s.secondary_le.trans (map_subtype_le _)) x.property⟩, by
    obtain ⟨a, ha, he⟩ := s.secondary_le x.property
    exact (Subtype.ext he : a = ⟨x, _⟩) ▸ ha⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
/-- The original K₂ inclusion is injective before passage to the quotient. -/
theorem SecondaryData.secondaryToComponent_injective (s : SecondaryData c n) :
    Function.Injective (SecondaryData.secondaryToComponent s) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : s.component => ((z : rootNormalizer c) : G)) hxy

/-- The literal projection K₂ → K_Z/O₂(K_Z). -/
def SecondaryData.secondaryProjection (s : SecondaryData c n) :
    secondary c →* (s.component ⧸ pCore 2 s.component) :=
  (QuotientGroup.mk' (pCore 2 s.component)).comp (SecondaryData.secondaryToComponent s)

omit [Finite G] in
/-- Conjugation by K₂ agrees with inner conjugation by its literal quotient image. -/
theorem SecondaryData.action_secondary (s : SecondaryData c n) (x : secondary c) :
    s.action ⟨x, (s.secondary_le.trans (map_subtype_le _)) x.property⟩ =
      MulAut.conj ((SecondaryData.secondaryProjection s) x) := by
  let := s.normal
  exact normalQuotientAction_inner s.component (pCore 2 s.component) ((SecondaryData.secondaryToComponent s) x)

omit [Finite G] in
/-- The source K₂-star is exactly the inner image of the literal projection.
This equality does not assert injectivity of inner conjugation. -/
theorem SecondaryData.secondary_action_image (s : SecondaryData c n) :
    ((secondary c).subgroupOf (rootNormalizer c)).map s.action =
      (SecondaryData.secondaryProjection s).range.map (MulAut.conj :
        (s.component ⧸ pCore 2 s.component) →* MulAut _) := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(SecondaryData.secondaryProjection s) ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩,
      ((SecondaryData.action_secondary s) ⟨x, hx⟩).symm⟩
  · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
    exact ⟨⟨x, (s.secondary_le.trans (map_subtype_le _)) x.property⟩,
      x.property, (SecondaryData.action_secondary s) x⟩

omit [Finite G] in
/-- Torus commutators in K₂-star lie in the image of the original O₂(K₂).
No centralization of the whole image is inferred from this bound. -/
theorem SecondaryData.secondary_action_commutator (s : SecondaryData c n) :
    ⁅((secondary c).subgroupOf (rootNormalizer c)).map s.action, (SecondaryData.torusImage s)⁆ ≤
      (((secondary c).pCoreIn 2).subgroupOf (rootNormalizer c)).map s.action := by
  have hK : secondary c ≤ rootNormalizer c := s.secondary_le.trans (map_subtype_le _)
  have he : ⁅(secondary c).subgroupOf (rootNormalizer c),
      s.torus.subgroupOf (rootNormalizer c)⁆ =
      ⁅secondary c, s.torus⁆.subgroupOf (rootNormalizer c) := by
    apply map_injective (rootNormalizer c).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hK,
      map_subgroupOf_eq_of_le s.torus_le,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans (sup_le hK s.torus_le))]
  unfold SecondaryData.torusImage
  rw [← map_commutator, he]
  exact map_mono (subgroupOf_mono _ s.torus_secondary)

/-- K₂ is perfect because it is the solvable residual of the actual root centralizer. -/
theorem secondary_perfect (c : SourceConfiguration T L) : Group.IsPerfect (secondary c) :=
  Group.IsPerfect.map _

/-- The literal quotient image of the original K₂ is perfect. -/
theorem SecondaryData.secondaryProjection_perfect (s : SecondaryData c n) :
    Group.IsPerfect (SecondaryData.secondaryProjection s).range := by
  let := secondary_perfect c
  exact Group.IsPerfect.range _

omit [Finite G] in
/-- The kernel of the literal projection lies in the component two-core. -/
theorem SecondaryData.secondaryProjection_kernel_two (s : SecondaryData c n) :
    IsPGroup 2 (SecondaryData.secondaryProjection s).ker := by
  let f : (SecondaryData.secondaryProjection s).ker →* pCore 2 s.component :=
    ((SecondaryData.secondaryToComponent s).comp (SecondaryData.secondaryProjection s).ker.subtype).codRestrict _
      (fun x => (QuotientGroup.eq_one_iff ((SecondaryData.secondaryToComponent s) x.val)).mp x.property)
  apply (pCore_isPGroup (p := 2) (G := s.component)).of_injective f
  intro x y hxy
  apply Subtype.ext
  apply (SecondaryData.secondaryToComponent_injective s)
  exact congrArg Subtype.val hxy

/-- The full quotient image retains K₂/O₂(K₂), with its actual projection. -/
def SecondaryData.secondaryProjectionCoreEquiv (s : SecondaryData c n) :
    secondary c ⧸ pCore 2 (secondary c) ≃*
      (SecondaryData.secondaryProjection s).range ⧸ pCore 2 (SecondaryData.secondaryProjection s).range :=
  (SecondaryData.secondaryProjection s).rangeRestrict.pCoreQuotientEquiv
    (SecondaryData.secondaryProjection s).rangeRestrict_surjective (by
      rw [MonoidHom.ker_rangeRestrict]
      exact (SecondaryData.secondaryProjection_kernel_two s))

/-- The rank-one model survives in the literal full quotient image. -/
theorem SecondaryData.secondaryProjection_model (s : SecondaryData c n) :
    ClassicalGroup.IsPSL
      ((SecondaryData.secondaryProjection s).range ⧸ pCore 2 (SecondaryData.secondaryProjection s).range) 2 (2 ^ n) :=
  s.secondary_model.of_mulEquiv (SecondaryData.secondaryProjectionCoreEquiv s).symm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

end
