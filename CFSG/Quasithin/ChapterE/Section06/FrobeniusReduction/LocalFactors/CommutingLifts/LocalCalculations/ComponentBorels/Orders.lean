module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.Defs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree.Centers
public import Theory.SpecificGroups.PSL3.LinearThreeBorelOrder
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.Suzuki.RootCenter

/-!
# Component Borel models with only the distinguished odd factor

For PSL₂ and Suzuki, the Borel has order a power of two times 2ⁿ−1.
For a central two-cover of PSL₃(4), its central quotient Borel has order
192 = 2⁶ · 3, and the covering kernel is a two-group. The faithful cyclic
subgroup X therefore detects the entire odd factor in all three cases.

A divisibility version of the action-kernel argument puts C_{L ∩ M}(V)
in O₂(L ∩ M). The earlier C-component theorem makes every relevant odd
actor normalize L ∩ M, and commuting induced actions put its commutator
with X in that kernel. Thus X itself supplies the requested lift.

All cardinality comparisons use the specified model isomorphisms and
actual Sylow normalizers. The ordinary PSL₃ and PSU₃ cases have larger
odd factors and are deliberately left to their separate action calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3b)
and the factor-count paragraph of E.6.25, printed pp.249–250,255.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components Components.BorelActions
variable {G : Type*} [Group G] [Finite G]

private theorem kernel_two_of_faithful_card_dvd {H D : Type*}
    [Group H] [Finite H] [Group D]
    (f : H →* D) (X : Subgroup H) (hf : Function.Injective (f.comp X.subtype))
    {k : ℕ} (hc : Nat.card H ∣ 2 ^ k * Nat.card X) : IsPGroup 2 f.ker := by
  let g : X →* f.range := f.rangeRestrict.comp X.subtype
  have hg : Function.Injective g := fun a b hab => hf (congrArg Subtype.val hab)
  have hd : Nat.card X ∣ Nat.card f.range := card_dvd_of_injective g hg
  have hh := f.ker.card_mul_index
  rw [index_ker] at hh
  have hmul : Nat.card f.ker * Nat.card X ∣ 2 ^ k * Nat.card X :=
    ((Nat.mul_dvd_mul_left (Nat.card f.ker) hd).trans (hh ▸ hc))
  exact IsPGroup.of_card_dvd_pow
    ((Nat.mul_dvd_mul_iff_right (Nat.card_pos (α := X))).mp hmul)

/-- Divisibility by a two-power times the order of a faithful subgroup
already bounds the local action kernel by the intrinsic two-core. -/
theorem componentBorel_local_kernel_le_core_of_card_dvd {V B X : Subgroup G}
    (hB : B ≤ normalizer (V : Set G)) (hX : X ≤ B)
    (hf : X ⊓ centralizer (V : Set G) = ⊥)
    {k : ℕ} (hc : Nat.card B ∣ 2 ^ k * Nat.card X) :
    B ⊓ centralizer (V : Set G) ≤ B.pCoreIn 2 := by
  let f : B →* MulAut V := V.normalizerMonoidHom.comp (inclusion hB)
  have hinj : Function.Injective (f.comp (X.subgroupOf B).subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxC : (x.val : G) ∈ centralizer (V : Set G) := by
      have hh : inclusion hB x.val ∈ V.normalizerMonoidHom.ker := hx
      rwa [normalizerMonoidHom_ker] at hh
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    exact mem_bot.mp (hf ▸ (show (x.val : G) ∈ X ⊓ centralizer (V : Set G) from
      ⟨x.property, hxC⟩))
  have hk : IsPGroup 2 f.ker := kernel_two_of_faithful_card_dvd f
    (X.subgroupOf B) hinj
    (by simpa only [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv] using hc)
  have hkcore : f.ker ≤ pCore 2 B := le_sSup ⟨inferInstance, hk⟩
  rintro x ⟨hxB, hxC⟩
  refine ⟨⟨x, hxB⟩, hkcore ?_, rfl⟩
  change inclusion hB ⟨x, hxB⟩ ∈ V.normalizerMonoidHom.ker
  rwa [normalizerMonoidHom_ker]

/-- The odd-actor calculation once the actual Borel order has been computed.
The three order branches below discharge this numerical premise. -/
theorem odd_commutator_le_core_of_componentBorel_card
    {K : GroupClass} {T : Sylow 2 G} {M V U X L A : Subgroup G}
    [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (hcard : ∃ k, Nat.card (L ⊓ M : Subgroup G) ∣ 2 ^ k * Nat.card X)
    (hA : A ≤ normalizer (V : Set G)) (ho : Odd (Nat.card A))
    (hc : ∀ a ∈ inducedAutomizer V A, ∀ x ∈ inducedAutomizer V X, Commute a x) :
    ⁅A, X⁆ ≤ (L ⊓ M).pCoreIn 2 := by
  have hXB : X ≤ L ⊓ M := le_inf hXL
    (hX.contained.trans (inf_le_left.trans inf_le_left))
  have hn := odd_normalizes_local_intersection h earlier hU hX hL hA ho hc
  have hcomm : ⁅A, X⁆ ≤ L ⊓ M :=
    (commutator_mono le_rfl hXB).trans (le_normalizer_iff_commutator_le_right.mp hn)
  obtain ⟨k, hk⟩ := hcard
  exact (le_inf hcomm (cross_commutator_le_kernel hA
    (hX.contained.trans (inf_le_left.trans inf_le_right)) hc)).trans
      (componentBorel_local_kernel_le_core_of_card_dvd
        (component_intersection_normalizes h hU hL.1) hXB hX.faithful hk)

private theorem card_normalizer_equiv {H D : Type*} [Group H] [Group D]
    (e : H ≃* D) (S : Subgroup H) :
    Nat.card (normalizer (S : Set H)) =
      Nat.card (normalizer (S.map e.toMonoidHom : Set D)) := by
  exact Nat.card_congr ((e.subgroupMap (normalizer (S : Set H))).trans
    (MulEquiv.subgroupCongr (map_equiv_normalizer_eq S e))).toEquiv

/-- The ordinary PSL₂ Borel has exactly the torus's odd order. -/
theorem componentBorel_card_linear_two
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 K T M V) (b : BorelAlternative M V U L n)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    Nat.card (L ⊓ M : Subgroup G) = 2 ^ n * (2 ^ n - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hz : center L = ⊥ := by
    apply (center L).eq_bot_iff_forall.mpr
    intro x hx
    apply e.injective
    rw [map_one]
    have he := (centerCongr e ⟨x, hx⟩).property
    change e x ∈ center PSL(2,F) at he
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using he
  have hB := borel_eq_sylow_normalizer h b hQ S hS
    (show IsPGroup 2 (center L) by rw [hz]; exact IsPGroup.of_bot)
  let R : Sylow 2 PSL(2,F) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  calc
    Nat.card (L ⊓ M : Subgroup G) = Nat.card ((L ⊓ M).subgroupOf L) :=
      (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    _ = Nat.card (normalizer (S : Set L)) := by rw [hB]
    _ = Nat.card (normalizer (R : Set PSL(2,F))) := card_normalizer_equiv e S
    _ = Nat.card (Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F) :=
      Nat.card_congr
        (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F R).toEquiv
    _ = 2 ^ n * (2 ^ n - 1) := by
      rw [Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel, hF]


private theorem card_sylow_normalizer_eq {H : Type*} [Group H] [Finite H]
    (S R : Sylow 2 H) :
    Nat.card (normalizer (S : Set H)) = Nat.card (normalizer (R : Set H)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S R
  have he : (S : Subgroup H).map (MulAut.conj g).toMonoidHom = (R : Subgroup H) :=
    congrArg Sylow.toSubgroup hg
  exact (card_normalizer_equiv (MulAut.conj g) S).trans (by rw [he]; rfl)

/-- The Suzuki Borel's full odd factor is 2ⁿ−1, at the specified Sylow.
The center is shown to be a two-group using root centralizers, without
appealing to a new simplicity or model-order certificate. -/
theorem componentBorel_card_suzuki
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 K T M V) (b : BorelAlternative M V U L n)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (m : ℕ) (hm : 1 ≤ m) (hnm : n = 2 * m + 1)
    (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Nat.card (L ⊓ M : Subgroup G) = 2 ^ (2 * n) * (2 ^ n - 1) := by
  have hm0 : 0 < m := by omega
  obtain ⟨hcent, hC, _⟩ := BenderSuzuki.MatrixGroups.suzukiSylow_borel_structure hm0 e S
  have hz : IsPGroup 2 (center L) := by
    have : Nontrivial (center S) := Finite.one_lt_card_iff_nontrivial.mp
      (hcent.symm ▸ (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega)))
    obtain ⟨z, hz⟩ := exists_ne (1 : center S)
    apply S.isPGroup'.to_le
    intro x hx
    apply hC z.val z.val.property (fun he => hz (Subtype.ext (Subtype.ext he)))
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hx z.val).symm
  have hB := borel_eq_sylow_normalizer h b hQ S hS hz
  let R : Sylow 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨P, hP⟩ := BenderSuzuki.MatrixGroups.suzukiRootSubgroup_isSylow m hm0
  calc
    Nat.card (L ⊓ M : Subgroup G) = Nat.card ((L ⊓ M).subgroupOf L) :=
      (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    _ = Nat.card (normalizer (S : Set L)) := by rw [hB]
    _ = Nat.card (normalizer (R : Set (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) :=
      card_normalizer_equiv e S
    _ = Nat.card (normalizer (P : Set (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) :=
      card_sylow_normalizer_eq R P
    _ = (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
      change Nat.card (normalizer ((P : Subgroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : Set (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) = _
      rw [hP, BenderSuzuki.MatrixGroups.suzukiRootSubgroup_normalizer m hm0,
        BenderSuzuki.MatrixGroups.suzukiBorelSubgroup_card m hm0]
    _ = 2 ^ (2 * n) * (2 ^ n - 1) := by rw [hnm, ← pow_mul, Nat.mul_comm (2 * m + 1) 2]

private theorem card_dvd_two_pow_mul_of_quotient_image
    {H : Type*} [Group H] [Finite H] {Z B : Subgroup H} [Z.Normal]
    (hZ : IsPGroup 2 Z) {j d : ℕ}
    (himg : Nat.card (B.map (QuotientGroup.mk' Z)) ∣ 2 ^ j * d) :
    ∃ k, Nat.card B ∣ 2 ^ k * d := by
  let f := (QuotientGroup.mk' Z).comp B.subtype
  have hrange : f.range = B.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hker : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' Z).ker).comap B.subtype)
    rw [QuotientGroup.ker_mk']
    exact hZ.comap_subtype
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  refine ⟨k + j, ?_⟩
  rw [← f.ker.card_mul_index, index_ker, hrange, hk, pow_add, mul_assoc]
  exact Nat.mul_dvd_mul_left _ himg

/-- Every central two-cover of PSL₃(4) has a Borel whose odd factor
is at most three. The quotient is the specified actual PSL₃ model. -/
theorem componentBorel_card_linear_three_cover
    {M L : Subgroup G} (b : BorelPreimage L (L ⊓ M))
    (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    ∃ k, Nat.card (L ⊓ M : Subgroup G) ∣ 2 ^ k * 3 := by
  obtain ⟨_, S, hB⟩ := b
  let q := QuotientGroup.mk' (center L)
  have himage : ((L ⊓ M).subgroupOf L).map q = normalizer (S : Set (L ⧸ center L)) := by
    rw [hB]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  let R : Sylow 2 PSL(3,F) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hnorm : Nat.card (normalizer (S : Set (L ⧸ center L))) = 192 := by
    calc
      _ = Nat.card (normalizer (R : Set PSL(3,F))) := card_normalizer_equiv e S
      _ = Nat.card (Matrix.PSL3.LinearThree.borel F) :=
        Nat.card_congr (Matrix.PSL3.CartanActions.BorelQuotient.sylowNormalizerEquiv
          F (n := 2) (by decide) hF R).toEquiv
      _ = 192 := Matrix.PSL3.CartanActions.BorelQuotient.card_borel_linear_three_four F hF
  obtain ⟨k, hk⟩ := card_dvd_two_pow_mul_of_quotient_image hz
    (B := (L ⊓ M).subgroupOf L) (j := 6) (d := 3)
    (by rw [himage, hnorm]; norm_num)
  exact ⟨k, by simpa only [Nat.card_congr (subgroupOfEquivOfLe
    (inf_le_left : L ⊓ M ≤ L)).toEquiv] using hk⟩


private theorem componentBorel_lift_of_card
    {K : GroupClass} {T : Sylow 2 G} {M V U X L : Subgroup G}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (hcard : ∃ k, Nat.card (L ⊓ M : Subgroup G) ∣ 2 ^ k * Nat.card X) :
    ComponentBorelLiftConclusion M V U L X := by
  let _ := h.elementary
  refine ⟨X, hXL, hX, rfl, ?_⟩
  intro A hA ho hc
  exact odd_commutator_le_core_of_componentBorel_card h earlier hU hX hL hXL
    hcard hA ho hc

/-- The PSL₂ model supplies the complete local output with Y = X. -/
theorem componentBorel_lift_linear_two
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L X : Subgroup G}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (b : BorelAlternative M V U L (subgroupCorank V U))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSL L 2 (2 ^ subgroupCorank V U)) :
    ComponentBorelLiftConclusion M V U L X := by
  apply componentBorel_lift_of_card h earlier hU hX hL hXL
  exact ⟨subgroupCorank V U, by
    rw [componentBorel_card_linear_two h b hQ S hS iso, hX.card_eq]⟩

/-- The Suzuki model supplies the complete local output with Y = X. -/
theorem componentBorel_lift_suzuki
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L X : Subgroup G}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (b : BorelAlternative M V U L (subgroupCorank V U))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (m : ℕ) (hm : 1 ≤ m) (hnm : subgroupCorank V U = 2 * m + 1)
    (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ComponentBorelLiftConclusion M V U L X := by
  apply componentBorel_lift_of_card h earlier hU hX hL hXL
  exact ⟨2 * subgroupCorank V U, by
    rw [componentBorel_card_suzuki h b hQ S hS m hm hnm e, hX.card_eq]⟩

/-- Every central two-cover of PSL₃(4) supplies the complete local output
with Y = X. The size of its covering center is unrestricted. -/
theorem componentBorel_lift_linear_three_cover
    {K : GroupClass} {T : Sylow 2 G} {M V U L X : Subgroup G}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (b : BorelAlternative M V U L (subgroupCorank V U))
    (hn : subgroupCorank V U = 2) (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    ComponentBorelLiftConclusion M V U L X := by
  apply componentBorel_lift_of_card h earlier hU hX hL hXL
  simpa only [hX.card_eq, hn, show 2 ^ 2 - 1 = (3 : ℕ) from rfl] using
    componentBorel_card_linear_three_cover b.borel hz iso

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
