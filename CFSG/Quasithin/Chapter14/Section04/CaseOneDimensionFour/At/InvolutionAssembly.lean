module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.InvolutionAssembly
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Normalizer

/-!
# Actual involutions and the remaining order-32 assembly at the original G,T

The literal W is the centralizer in U of a noncentral involution, so its
involutions generate it. Since Wᵍ has order 16 and U∩Wᵍ=V has order eight,
there is an involution s in Wᵍ outside U. The original parabolic calculation
then gives T∩L=U⟨s⟩, retaining the same conjugator and full central cover.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original point normalizer has no prime divisors other than two and three. -/
theorem source_point_twoThree (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    IsPiGroup twoThreePrimes F.H := by
  apply IsPiGroup.of_normal_subgroup_and_quotient (pCore 2 F.H)
  · intro p hp
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := F.H)).exists_card_eq
    have hp' : p.val ∣ Nat.card (pCore 2 F.H) := hp
    rw [hn] at hp'
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hp') |>.resolve_left p.property.ne_one)
  · apply (IsPiGroup_iff _ _).mpr
    intro p hp
    have hc := source_quotient_card_cases d setup structural alternatives F hne hZ hcard
    have hd : p.val ∣ 36 := by
      rcases hc with hc | hc
      · change Nat.card (F.H ⧸ pCore 2 F.H) = 18 at hc
        rw [hc] at hp
        exact hp.trans (by decide)
      · change Nat.card (F.H ⧸ pCore 2 F.H) = 36 at hc
        rwa [hc] at hp
    change p.val = 2 ∨ p.val = 3
    have hprod : p.val ∣ 2 ^ 2 * 3 ^ 2 := hd
    rcases p.property.dvd_mul.mp hprod with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (p.property.dvd_of_dvd_pow h3) |>.resolve_left p.property.ne_one)

/-- Apply the source prime restriction at the actual flag point to the split-image obstruction. -/
theorem source_no_markedLocalActions (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (A P R : Subgroup G) (z : A) (hz : F.Vi 1 = zpowers (z : G)) :
    ¬ Nonempty (DimensionFour.SplitImage.MarkedLocalActions A P R z) := by
  let := setup.chosen.elementary
  exact DimensionFour.SplitImage.no_markedLocalActions A F.H P R z
    (F.H_eq_centralizer (by decide) z hz)
    (source_point_twoThree d setup structural alternatives F hne hZ hcard)

/-- Fusion and the selected inverter discharge the core, order and generation fields of SourceLocalData. -/
theorem source_localData_of_fusion_and_inversion (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (hfusion : normalizer (L : Set G) = L)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hinv : ∀ k : pResidual 2 F.H,
      QuotientGroup.mk' (pCore 2 F.H) (s * k * s⁻¹) =
        (QuotientGroup.mk' (pCore 2 F.H) k)⁻¹) :
    Nonempty (SourceLocalData L F) := by
  have hT : (T : Subgroup G) ≤ L := by
    rw [← hfusion, source_normalizer_eq_join d setup structural alternatives F hne hZ hcard]
    exact le_sup_right
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := (pCore_isPGroup (p := 2) (G := F.H)).le_sylow_of_normal
      (T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1))
    rintro x ⟨y, hy, rfl⟩
    exact hh hy
  have hcore : F.U = F.H.pCoreIn 2 := by
    have he := source_twoCore_inf_block d setup structural
      alternatives F hne hZ hcard
    rw [inf_eq_right.mpr (hQT.trans hT)] at he
    exact he.symm
  have hTgen : (T : Subgroup G) = F.U ⊔ zpowers (s : G) := by
    have hh := (source_involution_sylow d setup structural
      alternatives F hne hZ hcard g s hgP hgH hsX
      (congrArg Subtype.val hs) hout).1
    rwa [inf_eq_left.mpr hT] at hh
  have hUK := (source_point_cubic d setup structural
    alternatives F hne hZ hcard).2.1
  have hgen : pResidual 2 F.H ⊔ zpowers s = ⊤ := by
    apply (map_injective F.H.subtype_injective)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype]
    have hh := (source_normalizer_factors d setup structural alternatives F hne hZ hcard).2
    rw [hTgen, ← sup_assoc, sup_eq_left.mpr hUK] at hh
    exact hh.symm
  exact ⟨{
    seed_core := (source_block_core d setup structural
      alternatives F hne hZ hcard).1
    closure_core := hcore
    quotient_card := source_quotient_card_of_generator d setup structural alternatives
      F hne hZ hcard s hgen
    inverter := s
    generates := hgen
    inverts := hinv }⟩

private theorem source_W_as_involution_centralizer
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 V] (hZ : F.ZU = F.Vi 1) :
    ∃ t : F.U, orderOf t = 2 ∧ t ∉ center F.U ∧
      F.W = (centralizer ({t} : Set F.U)).map F.U.subtype := by
  classical
  have hV : Nat.card (F.Vi 2)=4 := by simpa using F.card 2 (by decide)
  have hpoint : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by omega)
  have hnle : ¬ F.Vi 2 ≤ F.Vi 1 := by
    intro hh
    have hc := card_le_of_le hh
    omega
  obtain ⟨t,ht,hnt⟩ := SetLike.not_le_iff_exists.mp hnle
  have htU : t ∈ F.U := (show V ≤ F.U from le_conjugateSpanBy V F.H) (F.le_seed 2 ht)
  let u : F.U := ⟨t,htU⟩
  have hnc : u ∉ center F.U := by
    intro hh
    apply hnt
    rw [←hZ]
    exact mem_map_of_mem F.U.subtype hh
  have htne : t ≠ 1 := by intro hh; exact hnt (hh ▸ one_mem _)
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian (A:=V) t (F.le_seed 2 ht)
  have hu2 : orderOf u=2 := orderOf_eq_prime (Subtype.ext ht2)
    (fun hh => htne (congrArg Subtype.val hh))
  let B := zpowers t ⊔ F.Vi 1
  have hBV : B ≤ F.Vi 2 := sup_le (zpowers_le.mpr ht) (F.monotone (by decide))
  have hPB : F.Vi 1 ≤ B := le_sup_right
  have hBgt : 2 < Nat.card B := by
    by_contra! hc
    have he : F.Vi 1=B := eq_of_le_of_card_ge hPB (by omega)
    exact hnt (he.symm ▸ (show t ∈ B from
      (show zpowers t ≤ B from le_sup_left) (mem_zpowers t)))
  have hBdiv : Nat.card B ∣ 4 := hV ▸ card_dvd_of_le hBV
  have hBbound : Nat.card B ≤ 4 := hV ▸ card_le_of_le hBV
  have hBne3 : Nat.card B ≠ 3 := by intro hh; rw [hh] at hBdiv; norm_num at hBdiv
  have hB : B=F.Vi 2 := eq_of_le_of_card_ge hBV (by omega)
  refine ⟨u,hu2,hnc,?_⟩
  apply le_antisymm
  · intro w hw
    refine ⟨⟨w,hw.1⟩,?_,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact (hw.2 t ht).symm
  · rintro w ⟨a,ha,rfl⟩
    refine ⟨a.property,?_⟩
    have hat : t * (a:G)=(a:G) * t := by
      have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
      exact hh.symm
    have hPC : F.Vi 1 ≤ centralizer ({(a:G)} : Set G) := by
      intro z hz
      obtain ⟨c,hc,hcz⟩ := (show z ∈ (center F.U).map F.U.subtype from
        (show z ∈ F.ZU from hZ.symm ▸ hz))
      apply mem_centralizer_singleton_iff.mpr
      exact hcz ▸ congrArg Subtype.val (mem_center_iff.mp hc a).symm
    have hVC : F.Vi 2 ≤ centralizer ({(a:G)} : Set G) := by
      have hh : B ≤ centralizer ({(a:G)} : Set G) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hat)) hPC
      exact hB.symm.le.trans hh
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hVC hz)


/-- The actual W, including its center, is generated by square-one elements. -/
theorem source_W_involution_generated (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    closure {x : F.W | x ^ 2 = 1} = ⊤ := by
  let := setup.chosen.elementary
  obtain ⟨q⟩ := source_quaternion d setup structural alternatives F hne hZ hcard
  obtain ⟨t, ht, hnc, hW⟩ := source_W_as_involution_centralizer F hZ
  exact QuaternionCentralProductData.ambient_involution_centralizer_generated
    F.U F.W q t ht hnc hW

/-- Choose a square-one element in the literal Wᵍ outside U, without assuming Wᵍ elementary. -/
theorem source_selected_involution (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ s : F.H, (s : G) ∈ F.X g ∧ s ^ 2 = 1 ∧ (s : G) ∉ F.U := by
  have hgen := source_W_involution_generated d setup structural
    alternatives F hne hZ hcard
  obtain ⟨hprod, hW, hinter, _⟩ := source_sylow_product d setup structural
    alternatives F hne hZ hcard g hgP hgH
  have hX : Nat.card (F.X g) = 16 := by
    change Nat.card (F.W.map (MulAut.conj g⁻¹).toMonoidHom) = 16
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hW]
  have hXU : ¬ F.X g ≤ F.U := by
    intro h
    rw [inf_eq_right.mpr h] at hinter
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hinter, hc] at hX
    omega
  have hex : ∃ a : G, a ∈ F.X g ∧ a ^ 2 = 1 ∧ a ∉ F.U := by
    by_contra! hn
    apply hXU
    have hle : closure {x : F.W | x ^ 2 = 1} ≤
        (F.U.comap (MulAut.conj g⁻¹).toMonoidHom).subgroupOf F.W := by
      apply (Subgroup.closure_le _).mpr
      intro w hw
      apply hn _ (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom w.property)
      change (MulAut.conj g⁻¹) (w : G) ^ 2 = 1
      rw [← map_pow, show (w : G) ^ 2 = 1 from congrArg Subtype.val hw, map_one]
    rw [hgen] at hle
    rintro a ⟨w, hw, rfl⟩
    exact hle (mem_top (⟨w, hw⟩ : F.W))
  obtain ⟨a, haX, ha2, haU⟩ := hex
  have haT : a ∈ (T : Subgroup G) := (hprod ▸ mem_sup_right haX).1
  exact ⟨⟨a, F.invariant 1 haT⟩, haX, Subtype.ext ha2, haU⟩

/-- Construct both the omitted-point conjugator and the involution generating T∩L over U. -/
theorem source_involution_sylow_exists (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ (g : G) (s : F.H), g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧
      (s : G) ∈ F.X g ∧ s ^ 2 = 1 ∧ (s : G) ∉ F.U ∧
      (T : Subgroup G) ⊓ L = F.U ⊔ zpowers (s : G) := by
  obtain ⟨g, hgL, hgP, hgH⟩ := source_internal_conjugator d setup
    structural alternatives F hne hZ hcard
  obtain ⟨s, hsX, hs, hout⟩ := source_selected_involution d setup
    structural alternatives F hne hZ hcard g hgP hgH
  exact ⟨g, s, hgL, hgP, hgH, hsX, hs, hout,
    (source_involution_sylow d setup structural alternatives
      F hne hZ hcard g s hgP hgH hsX (congrArg Subtype.val hs) hout).1⟩


/-- The c₂ action inverts the whole residual image under H → H/O₂(H). -/
theorem source_inversion_of_c2 (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (q : QuaternionCentralProductData F.U) (s : F.H) (hs : s ^ 2 = 1)
    (hc2 : q.IsC2 (F.uAction s)) :
    ∀ k : pResidual 2 F.H,
      QuotientGroup.mk' (pCore 2 F.H) (s * k * s⁻¹) =
        (QuotientGroup.mk' (pCore 2 F.H) k)⁻¹ := by
  have hk := source_uhat_kernel d setup structural alternatives F hZ
  let π := QuotientGroup.mk' (pCore 2 F.H)
  let φ := QuotientGroup.lift (pCore 2 F.H) F.uhatAction hk.ge
  have hφ : Function.Injective φ :=
    (QuotientGroup.injective_lift_iff _ _ hk.ge).mpr hk.symm
  let := (source_residual_nine d setup structural alternatives F hne hZ hcard).1
  have ha : (F.uAction s) ^ 2 = 1 := by rw [← map_pow, hs, map_one]
  intro k
  have hcube : (π k) ^ 3 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (π k) (mem_map_of_mem π k.property)
  have hkQ : (k : F.H) ^ 3 ∈ pCore 2 F.H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π ((k : F.H) ^ 3) = 1
    rwa [map_pow]
  have hc : (quotientAut (center F.U) (F.uAction k)) ^ 3 = 1 := by
    have hact : (k : F.H) ^ 3 ∈ F.uhatAction.ker := hk.symm ▸ hkQ
    change F.uhatAction ((k : F.H) ^ 3) = 1 at hact
    rw [map_pow] at hact
    exact hact
  have hi := QuaternionCentralProductData.BothOuter.inverts_cubic q
    (QuaternionCentralProductData.IsC2.bothOuter q hc2) ha (F.uAction k) hc
  rw [← map_inv]
  apply hφ
  change quotientAut (center F.U) (F.uAction (s * k * s⁻¹)) =
    quotientAut (center F.U) (F.uAction ((k : F.H)⁻¹))
  simpa only [map_mul, map_inv] using hi

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
