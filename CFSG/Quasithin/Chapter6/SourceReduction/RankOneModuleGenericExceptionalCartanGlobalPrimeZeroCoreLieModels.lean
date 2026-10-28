module
public import Theory.GroupTheory.Amalgam.Reversal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionRee
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreTrialityExclusion
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.G2
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.Diagram
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicSolvable
public import Theory.AtlasPort.LinearGroups.G2.ParabolicPrimeToResidual

/-!
# Lie-model exclusions for the zero-core Cartan pair

The original prime pair has a solvable left parabolic and a nonsolvable
right parabolic. In the split linear-three, symplectic-four, G₂ and Ree
families both endpoints are solvable at field two and nonsolvable at
larger fields, as witnessed by their literal local quotients. The triality
arms quotient is always nonsolvable. Its central quotient is nonsolvable
above field two; at field two the reversed marking is excluded by the
original moved-module and seven-torus calculation.

These arguments preserve the whole overlap, projective scalar kernels
and each model's actual field degree. They exclude five concrete F.1.12
families in both orientations using only parabolic equivalence. Exhaustive
recognition and the unitary families are separate obligations.
Source: Aschbacher–Smith 5.2.2, printed pp.647–648, and F.1.12(I)(1–5),
printed pp.262–264, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

private theorem not_solvable_of_local_SL2
    {X : Type*} [Group X] {Q P : Subgroup X} (hQP : Q ≤ P)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (e : (Q ⧸ pCore 2 Q) ≃* SL(2,F)) :
    ¬ Group.IsSolvable P := by
  intro hs
  let := hs
  let : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hQP) (inclusion_injective hQP)
  let : Group.IsSolvable SL(2,F) := Group.isSolvable_of_surjective
    (f := e.toMonoidHom) e.surjective
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable SL(2,F) inferInstance

private theorem linear_binary_solvable {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    Group.IsSolvable (Matrix.PSL3.LinearThree.pointParabolic F) ∧
      Group.IsSolvable (Matrix.PSL3.LinearThree.lineParabolic F) := by
  let : Fintype F := Fintype.ofFinite F
  let s : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by rwa [←Nat.card_eq_fintype_card])).symm
  let a := Atlas.fieldEquivPSL 3 s
  let e0 := ((Matrix.PSL3.LinearThree.pointParabolic F).equivMapOfInjective
    a.toMonoidHom a.injective).trans
      ((MulEquiv.subgroupCongr (Matrix.PSL3.LinearThree.FieldTransport.field_map_pointParabolic s)).trans
        Matrix.PSL3Two.pointParabolicEquivS4)
  let e1 := ((Matrix.PSL3.LinearThree.lineParabolic F).equivMapOfInjective
    a.toMonoidHom a.injective).trans
      ((MulEquiv.subgroupCongr (Matrix.PSL3.LinearThree.FieldTransport.field_map_lineParabolic s)).trans
        Matrix.PSL3Two.lineParabolicEquivS4)
  let := Equiv.Perm.isSolvable_fin_four
  exact ⟨Group.isSolvable_of_isSolvable_injective (f := e0.toMonoidHom) e0.injective,
    Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective⟩

private theorem mixed_not_parabolic_equiv
    {X E Y X' E' Y' : Type*} [Group X] [Group E] [Group Y]
    [Group X'] [Group E'] [Group Y']
    {α : RankTwoAmalgam X E Y} {β : RankTwoAmalgam X' E' Y'}
    (hX : Group.IsSolvable X) (hY : ¬ Group.IsSolvable Y)
    (hm : Group.IsSolvable X' ↔ Group.IsSolvable Y') :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv α β) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv α β.reverse) := by
  constructor
  · rintro ⟨e⟩
    let := hX
    have hx := Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective
    let := hm.mp hx
    exact hY (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
  · rintro ⟨e⟩
    let := hX
    have hy := Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective
    let := hm.mpr hy
    exact hY (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)

/-- The original zero-core pair excludes every split linear-three marking,
retaining the scalar kernel and both possible endpoint orientations. -/
theorem LocalData.zeroCore_not_linear_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.LinearThree.amalgam F)) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.LinearThree.amalgam F).reverse) := by
  obtain ⟨hs,hn⟩ := d.zeroCore_mixed_solvability h hH c hd hz
  apply mixed_not_parabolic_equiv hs hn
  by_cases hm1 : m = 1
  · have hh := linear_binary_solvable (by simpa [hm1] using hF)
    exact ⟨fun _ => hh.2,fun _ => hh.1⟩
  · have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < m))
    open Matrix.PSL3.LinearThree in
      have h0 := not_solvable_of_local_SL2
        (show pointLocal F ≤ pointParabolic F from (pointParabolic_eq_sup F) ▸ le_sup_left)
        hlarge (pointLocalCoreQuotientEquiv F)
      have h1 := not_solvable_of_local_SL2
        (show lineLocal F ≤ lineParabolic F from (lineParabolic_eq_sup F) ▸ le_sup_left)
        hlarge (lineLocalCoreQuotientEquiv F)
      exact ⟨fun hh => (h0 hh).elim,fun hh => (h1 hh).elim⟩

/-- The existing native parabolic calculations give matching solvability,
also at the binary parameter. This form supports original extension filtering. -/
theorem symplectic_parabolics_solvable_iff
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) :
    Group.IsSolvable (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)) ↔
      Group.IsSolvable (Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)) := by
  by_cases hm1 : m = 1
  · have htwo : Nat.card F = 2 := by simpa [hm1] using hF
    let := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 2)) := Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 2 ≤ 4)))
    let e0 := Theory.SpecificGroups.SymplecticFour.Binary.pointParabolicEquivProd htwo
    let e1 := Theory.SpecificGroups.SymplecticFour.Binary.planeParabolicEquivProd htwo
    have h0 := Group.isSolvable_of_isSolvable_injective (f := e0.toMonoidHom) e0.injective
    have h1 := Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective
    exact ⟨fun _ => h1,fun _ => h0⟩
  · have hm' : 1 < m := by omega
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) hm'
    open Theory.SpecificGroups.SymplecticFour in
      have h0 := not_solvable_of_local_SL2 pointLocal_le hlarge (pointLocalCoreQuotientEquiv hF hm')
      have h1 := not_solvable_of_local_SL2 planeLocal_le hlarge (planeLocalCoreQuotientEquiv hF hm')
      exact ⟨fun hh => (h0 hh).elim,fun hh => (h1 hh).elim⟩

/-- The actual symplectic point/plane models have the same solvability and
cannot be the two endpoints of the original prime pair. -/
theorem LocalData.zeroCore_not_symplectic_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.SymplecticFour.amalgam F)) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.SymplecticFour.amalgam F).reverse) := by
  obtain ⟨hs,hn⟩ := d.zeroCore_mixed_solvability h hH c hd hz
  exact mixed_not_parabolic_equiv hs hn (symplectic_parabolics_solvable_iff hm hF)

/-- The existing native parabolic calculations give matching solvability,
also at the binary parameter. This form supports original extension filtering. -/
theorem g2_parabolics_solvable_iff
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) :
    Group.IsSolvable (Atlas.G2.LieParabolicSetup.parabolic₁ (F := F)) ↔
      Group.IsSolvable (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F)) := by
  by_cases hm1 : m = 1
  · have htwo : Nat.card F = 2 := by simpa [hm1] using hF
    have h0 := Atlas.G2.BinaryParabolicSolvable.parabolic_isSolvable htwo 0
    have h1 := Atlas.G2.BinaryParabolicSolvable.parabolic_isSolvable htwo 1
    exact ⟨fun _ => h1,fun _ => h0⟩
  · have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < m)
    constructor
    · intro hh
      let : Group.IsSolvable (Atlas.G2.LieParabolicSetup.parabolic₁ (F := F)) := hh
      have hr : Group.IsSolvable (primeToResidual 3
          (Atlas.G2.LieParabolicSetup.parabolic₁ (F := F))) := inferInstance
      exact (Atlas.G2.LieParabolicSetup.parabolic_primeToResidual_not_solvable hlarge 0
        (by simpa using hr)).elim
    · intro hh
      let : Group.IsSolvable (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F)) := hh
      have hr : Group.IsSolvable (primeToResidual 3
          (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F))) := inferInstance
      exact (Atlas.G2.LieParabolicSetup.parabolic_primeToResidual_not_solvable hlarge 1
        (by simpa using hr)).elim

/-- Both root parabolics of G₂ have matching solvability at every binary
field degree, excluding both orientations on the actual source pair. -/
theorem LocalData.zeroCore_not_g2_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.G2.amalgam (F := F))) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.G2.amalgam (F := F)).reverse) := by
  obtain ⟨hs,hn⟩ := d.zeroCore_mixed_solvability h hH c hd hz
  exact mixed_not_parabolic_equiv hs hn (g2_parabolics_solvable_iff hm hF)

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics in
/-- The triality family is excluded at every actual field degree. The binary
reversed marking uses the original moved-module/seven-torus contradiction. -/
theorem LocalData.zeroCore_not_triality_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.Triality.amalgam (binaryParameters m hm))) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.Triality.amalgam (binaryParameters m hm)).reverse) := by
  let P := binaryParameters m hm
  have hs := (d.zeroCore_mixed_solvability h hH c hd hz).1
  let := hs
  constructor
  · rintro ⟨e⟩
    have hlarge : 2 < Nat.card (ExtensionField P) := by
      rw [card_extensionField]
      change 2 < (2^m)^3
      rw [← pow_mul]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < m*3)
    have hn := not_solvable_of_local_SL2 (localFactor_le_parabolic P .arms) hlarge
      ((localFactorArmsQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
    exact hn (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)
  · by_cases hm1 : m = 1
    · subst m
      exact d.zeroCore_not_binaryTriality_parabolic h hH c hd hz
    · rintro ⟨e⟩
      have hlarge : 2 < Nat.card (GaloisField P.prime P.exponent) := by
        rw [GaloisField.card P.prime P.exponent (by change m ≠ 0; omega)]
        change 2 < 2^m
        exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < m)
      have hn := not_solvable_of_local_SL2 (localFactor_le_parabolic P .central) hlarge
        ((localFactorCentralQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
      exact hn (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)

open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds in
/-- The existing native parabolic calculations give matching solvability,
also at the binary parameter. This form supports original extension filtering. -/
theorem ree_parabolics_solvable_iff (m : ℕ) :
    Group.IsSolvable (parabolic m .suzuki) ↔ Group.IsSolvable (parabolic m .linear) := by
  by_cases hm : m = 0
  · subst m
    exact ⟨fun _ => Global.ReeComparison.binary_parabolic_solvable .linear,
      fun _ => Global.ReeComparison.binary_parabolic_solvable .suzuki⟩
  · have hlarge : 2 < Nat.card (CoefficientField m) := by
      rw [field_card]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < 2*m+1)
    have hlin := not_solvable_of_local_SL2 (localFactor_le_parabolic m .linear) hlarge
      ((linearLocalQuotientEquiv m).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
    have hsz : ¬ Group.IsSolvable (parabolic m .suzuki) := by
      intro hh
      let := hh
      let : Group.IsSolvable (localFactor m .suzuki) :=
        Group.isSolvable_of_isSolvable_injective
          (f := inclusion (localFactor_le_parabolic m .suzuki))
          (inclusion_injective (localFactor_le_parabolic m .suzuki))
      have hq := Group.isSolvable_of_surjective
        (f := (suzukiLocalQuotientEquiv m).toMonoidHom) (suzukiLocalQuotientEquiv m).surjective
      exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m (by omega) hq
    exact ⟨fun hh => (hsz hh).elim, fun hh => (hlin hh).elim⟩

open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds in
/-- The two Ree parabolics are both solvable at field two and both nonsolvable
at every larger actual field, excluding the mixed source pair. -/
theorem LocalData.zeroCore_not_ree_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) (m : ℕ) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.ReeFour.amalgam m)) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.ReeFour.amalgam m).reverse) := by
  obtain ⟨hs,hn⟩ := d.zeroCore_mixed_solvability h hH c hd hz
  exact mixed_not_parabolic_equiv hs hn (ree_parabolics_solvable_iff m)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
