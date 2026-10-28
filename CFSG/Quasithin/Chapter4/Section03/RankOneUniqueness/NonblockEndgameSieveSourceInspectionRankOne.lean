module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceSmallModels
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsBenderCubic
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Excluding the Bender rows on the literal inner image

The secondary PSL₂ section embeds in the component's inner image, so its
order divides the order of that image. This excludes Suzuki, whose order
is prime to three. For binary linear and unitary models, automorphisms of
the full perfect quotient descend faithfully to its central quotient.
The same map transports the actual secondary, radical, core and torus
images, their normalization, core movement and whole-radical generation.
The checked generated-two-group exclusions then kill the radical image.

The field degree of the model need not equal the source degree. The argument
retains the full central cover and does not assume movement of the whole
radical by the torus. Its consumer is the reduced Theorem C inspection in
`NonblockEndgameSieveSourceInspectionSmall`.
Source: Aschbacher--Smith, original 4.3.12--16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
/-- The actual secondary action is contained in the full inner component. -/
theorem SecondarySourceData.secondaryImage_le_componentImage (s : SecondarySourceData c n) :
    SecondarySourceData.secondaryImage s ≤ SecondarySourceData.componentImage s := by
  rw [SecondarySourceData.componentImage_eq_inner]
  let := s.normal
  exact SourceImages.secondary_inner c s.component s.secondary_le

/-- The order of the rank-one section divides the order of the inner component,
including when the full quotient has nontrivial center. -/
theorem SecondarySourceData.secondary_order_dvd_inner (s : SecondarySourceData c n) :
    2^n * ((2^n)^2-1) ∣ Nat.card (SecondarySourceData.componentImage s) := by
  let := s.normal
  let X := SourceImages.image c s.component (secondary c)
  have hc : Nat.card (X ⧸ pCore 2 X) = 2^n * ((2^n)^2-1) := by
    have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^n) :=
      SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    rw [Nat.card_congr (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
  rw [←hc]
  exact (card_quotient_dvd_card (pCore 2 X)).trans
    (card_dvd_of_le (SecondarySourceData.secondaryImage_le_componentImage s))

/-- Identify the full quotient's central quotient with its actual inner image. -/
def SecondarySourceData.centralQuotientEquiv (s : SecondarySourceData c n) :
    (s.component ⧸ pCore 2 s.component) ⧸ center (s.component ⧸ pCore 2 s.component) ≃*
      SecondarySourceData.componentImage s :=
  innerEquivCentralQuotient.symm.trans
    (MulEquiv.subgroupCongr (SecondarySourceData.componentImage_eq_inner s).symm)

/-- Binary unitary models of any degree are excluded even on the inner quotient.
Faithful descent retains every image of the original action. -/
theorem SecondarySourceData.not_unitary_inner_of_generation (s : SecondarySourceData c n)
    (hg : SecondarySourceData.ActionGeneration s) {m : ℕ} (hm : 1 < m)
    (hmodel : ClassicalGroup.IsPSU (SecondarySourceData.componentImage s) 3 (2^m)) : False := by
  let := s.normal
  let := s.quasisimple
  let e := SecondarySourceData.centralQuotientEquiv s
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  let X := SourceImages.image c s.component (secondary c)
  let R := SourceImages.image c s.component (R₂ c)
  let Q := SourceImages.image c s.component (Q c)
  let Y := SourceImages.image c s.component s.torus
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect (X.map f) := Group.IsPerfect.map f
  have hX : X.map f ≠ ⊥ := fun hzero =>
    SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model
      ((X.map_eq_bot_iff_of_injective hf).mp hzero)
  have hXi : X.map f ≤ MulAut.innerSubgroup (SecondarySourceData.componentImage s) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,rfl⟩ := SourceImages.secondary_inner c s.component s.secondary_le hx
    exact ⟨e (QuotientGroup.mk' _ a),(MulAut.centralQuotientAction_conj e a).symm⟩
  obtain ⟨h2,hQR,_,hXR,_⟩ := SourceImages.radical_geometry c s.component s.radical_normalizer
  have hmove : ⁅Q.map f,Y.map f⁆ = Q.map f := by
    rw [←map_commutator,SourceImages.core_moved c s.component s.torus s.radical_le s.torus_le s.core_moved]
  have hgen : Q.map f ⊔ ⁅R.map f,X.map f⁆ = R.map f := by
    rw [←map_commutator,←Subgroup.map_sup]
    exact congrArg (Subgroup.map f) hg
  apply s.radical_action
  apply (R.map_eq_bot_iff_of_injective hf).mp
  exact unitary_generated_twoGroup_eq_bot hm hmodel _ hX hXi _ _ _
    (h2.map f) (map_mono hQR)
    ((map_mono hXR).trans (R.le_normalizer_map f)) hmove hgen

private theorem binary_mapped_torus_centralizes {A U : Type*} [Group A] [Group U]
    [Finite U] {m : ℕ} (hm : ClassicalGroup.IsPSL U 2 (2^m))
    (f : A →* MulAut U) (hf : Function.Injective f)
    (X Y : Subgroup A) [Group.IsPerfect X]
    (hi : X.map f ≤ MulAut.innerSubgroup U) (hc : ⁅X,Y⁆ ≤ X.pCoreIn 2) :
    Y.map f ≤ centralizer (X.map f : Set _) := by
  let : Group.IsPerfect (X.map f) := Group.IsPerfect.map f
  have hb : (⁅X,Y⁆).map f ≤ (X.pCoreIn 2).map f := map_mono hc
  have he := map_pCoreIn_of_injective 2 X f hf
  have hz := binary_inner_twoCore_eq_bot hm (X.map f) hi
  rw [he,hz] at hb
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm,←map_commutator]
  exact bot_unique hb

/-- Binary linear models are likewise excluded through faithful central descent. -/
theorem SecondarySourceData.not_binary_inner_of_generation (s : SecondarySourceData c n)
    (hg : SecondarySourceData.ActionGeneration s) {m : ℕ}
    (hmodel : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 2 (2^m)) : False := by
  let := s.normal
  let := s.quasisimple
  let e := SecondarySourceData.centralQuotientEquiv s
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  let X := SourceImages.image c s.component (secondary c)
  let R := SourceImages.image c s.component (R₂ c)
  let Q := SourceImages.image c s.component (Q c)
  let Y := SourceImages.image c s.component s.torus
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect (X.map f) := Group.IsPerfect.map f
  have hX : X.map f ≠ ⊥ := fun hzero =>
    SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model
      ((X.map_eq_bot_iff_of_injective hf).mp hzero)
  have hXi : X.map f ≤ MulAut.innerSubgroup (SecondarySourceData.componentImage s) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,rfl⟩ := SourceImages.secondary_inner c s.component s.secondary_le hx
    exact ⟨e (QuotientGroup.mk' _ a),(MulAut.centralQuotientAction_conj e a).symm⟩
  obtain ⟨h2,hQR,hXQ,hXR,hRX⟩ := SourceImages.radical_geometry c s.component s.radical_normalizer
  have hmove : ⁅Q.map f,Y.map f⁆ = Q.map f := by
    rw [←map_commutator,SourceImages.core_moved c s.component s.torus s.radical_le s.torus_le s.core_moved]
  have hgen : Q.map f ⊔ ⁅R.map f,X.map f⁆ = R.map f := by
    rw [←map_commutator,←Subgroup.map_sup]
    exact congrArg (Subgroup.map f) hg
  have hcomm : ⁅X,Y⁆ ≤ X.pCoreIn 2 := by
    change ⁅SourceImages.image c s.component (secondary c),SourceImages.image c s.component s.torus⁆ ≤ _
    rw [←SourceImages.image_commutator c s.component _ _
      (s.secondary_le.trans (map_subtype_le _)) s.torus_le]
    exact (map_mono (subgroupOf_mono _ s.torus_secondary)).trans
      (SourceImages.secondary_core_le c s.component)
  have hY := binary_mapped_torus_centralizes hmodel f hf X Y hXi hcomm
  apply s.radical_action
  apply (R.map_eq_bot_iff_of_injective hf).mp
  exact binary_generated_twoGroup_eq_bot hmodel _ hX hXi _ _ _
    (h2.map f) (map_mono hQR)
    ((map_mono hXQ).trans (Q.le_normalizer_map f))
    ((map_mono hXR).trans (R.le_normalizer_map f))
    ((map_mono hRX).trans (X.le_normalizer_map f)) hY hmove hgen


/-- The secondary binary section always has an element of order three. -/
theorem SecondarySourceData.three_dvd_inner_order (s : SecondarySourceData c n) (_hn : 0<n) :
    3 ∣ Nat.card (SecondarySourceData.componentImage s) := by
  have h3 : 3 ∣ (2^n)^2-1 := by
    rw [←pow_mul]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr ⟨n,by omega⟩
  exact (h3.trans (dvd_mul_left _ _)).trans (SecondarySourceData.secondary_order_dvd_inner s)

/-- The Suzuki rows are excluded by the actual secondary section's order. -/
theorem SecondarySourceData.not_suzuki_inner (s : SecondarySourceData c n) (hn : 0<n)
    {m : ℕ} (hm : 1≤m)
    (e : SecondarySourceData.componentImage s ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    False := by
  have hd := SecondarySourceData.three_dvd_inner_order s hn
  rw [Nat.card_congr e.toEquiv] at hd
  exact (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).2 hd

/-- The whole Bender family is excluded, with no matching-field assumption. -/
theorem SecondarySourceData.not_bender_inner_of_generation (s : SecondarySourceData c n)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    (hm : ClassificationModels.IsBenderModel (SecondarySourceData.componentImage s)) : False := by
  cases hm with
  | linear m _ hm => exact SecondarySourceData.not_binary_inner_of_generation s hg hm
  | unitary m hml hm => exact SecondarySourceData.not_unitary_inner_of_generation s hg (by omega) hm
  | suzuki m hml he => exact SecondarySourceData.not_suzuki_inner s (by omega) hml (Classical.choice he)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
