module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.SolvableFlags
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Sylow
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Bruhat
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.StandardOvergroups

/-!
# Intrinsic recognition of binary single-node parabolics

A subgroup containing an actual binary Sylow subgroup is first reconstructed as
an actual partial-flag stabilizer.  In dimensions four and five, the solvable
`O^{3'}` hypothesis then removes every block of dimension at least three; the
three-subgroup bound removes a second two-dimensional block.  The remaining
partial flag deletes one node, with the supplied basis and node labels retained.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the second
paragraph of 15.3.28, printed pp.1130--1132 (PDF pp.1147--1149), and B.5.5--6,
printed pp.104--105 (PDF pp.115--116).
-/

@[expose] public section
open Subgroup
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.BinaryHigher.FlagRecognition
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem four_linearGroup_card_formula (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp
private theorem four_perfect_isPPerfect {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] : IsPPerfect 2 K := by
  intro N hN hp
  let := hN
  by_contra hne
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
private theorem linear_residual_top_three : primeToResidual 3 (LinearGroup 3) = ⊤ := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (LinearGroup 3) := (projectiveEquivLinear (by decide : 0 < 3)).symm.isSimpleGroup
  let : Group.IsPerfect (LinearGroup 3) := linearGroup_isPerfect 3 (by decide)
  let : IsSimpleGroup ((LinearGroup 3) ⧸ (⊥ : Subgroup (LinearGroup 3))) := QuotientGroup.quotientBot.isSimpleGroup
  have h3 : 3 ∣ Nat.card (LinearGroup 3) := by rw [four_linearGroup_card_formula]; decide
  exact primeToResidual_eq_top_of_simple_quotient 3 2 (⊥ : Subgroup (LinearGroup 3))
    (IsPGroup.of_subsingleton 2 _) four_perfect_isPPerfect
    (by simpa only [Nat.card_congr QuotientGroup.quotientBot.toEquiv] using h3)
lemma factor_contra {W : Submodule (ZMod 2) (Space 4)}
    (f : parabolic W →* LinearGroup 3) (hf : Function.Surjective f)
    (hres : Group.IsSolvable (primeToResidual 3 (parabolic W))) : False := by
  let : Finite (parabolic W) :=
    Finite.of_injective (fun g : parabolic W => (g.val : Space 4 → Space 4))
      (fun x y h => Subtype.ext (DFunLike.coe_injective h))
  have hm := Subgroup.map_primeToResidual_of_surjective 3 f hf
  let R := primeToResidual 3 (parabolic W)
  have hsmap : Group.IsSolvable (R.map f) := by
    let := hres
    exact Group.isSolvable_of_surjective (f := f.subgroupMap R)
      (f.subgroupMap_surjective R)
  have hsB : Group.IsSolvable (primeToResidual 3 (LinearGroup 3)) := by
    rw [← hm]
    exact hsmap
  rw [linear_residual_top_three] at hsB
  let : Group.IsSolvable (⊤ : Subgroup (LinearGroup 3)) := hsB
  have hsol : Group.IsSolvable (LinearGroup 3) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup (LinearGroup 3)) ≃* LinearGroup 3).toMonoidHom)
      Subgroup.topEquiv.surjective
  let : Group.IsSolvable (LinearGroup 3) := hsol
  let : Group.IsPerfect (LinearGroup 3) := linearGroup_isPerfect 3 (by decide)
  have : Nontrivial (LinearGroup 3) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [four_linearGroup_card_formula]
    decide
  exact (Group.IsPerfect.not_isSolvable (LinearGroup 3)) inferInstance

lemma endpoint_parabolic_contra (b : BinaryLinear.InvariantNodeActions.Basis 3)
    (i : Fin 3) (hi : i = 0 ∨ i = 2)
    (hres : Group.IsSolvable (primeToResidual 3 (BinaryLinear.InvariantNodeActions.cutStabilizer b {i}))) : False := by
  let W := BinaryLinear.InvariantNodeActions.cutSpace b i
  have hpar : BinaryLinear.InvariantNodeActions.cutStabilizer b {i} = parabolic W := by
    simp [BinaryLinear.InvariantNodeActions.cutStabilizer, W]
  rw [hpar] at hres
  have hdimW : Module.finrank (ZMod 2) W = i.val + 1 := cutSpace_finrank b i
  rcases hi with rfl | rfl
  · have hdimQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 3 := by
      have h : Module.finrank (ZMod 2) (Space 4 ⧸ W) +
          Module.finrank (ZMod 2) W = 4 := by
        simpa only [Module.finrank_fin_fun] using W.finrank_quotient_add_finrank
      rw [hdimW] at h
      norm_num at h ⊢
      omega
    let eQ : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 3 :=
      LinearEquiv.ofFinrankEq (Space 4 ⧸ W) (Space 3) (by simpa only [Module.finrank_fin_fun] using hdimQ)
    let q : parabolic W →* LinearGroup 3 :=
      (linearGroupCongr eQ).toMonoidHom.comp
        ((MonoidHom.snd (BinaryLinear.GL W) (BinaryLinear.GL (Space 4 ⧸ W))).comp (blockAction W))
    have hsnd : Function.Surjective
        (MonoidHom.snd (BinaryLinear.GL W) (BinaryLinear.GL (Space 4 ⧸ W))) := by
      intro z
      exact ⟨(1, z), rfl⟩
    have hq : Function.Surjective q := by
      apply (linearGroupCongr eQ).surjective.comp
      apply hsnd.comp
      exact blockAction_surjective W
    exact factor_contra q hq hres
  · have hdimW3 : Module.finrank (ZMod 2) W = 3 := by simpa using hdimW
    let eW : W ≃ₗ[ZMod 2] Space 3 :=
      LinearEquiv.ofFinrankEq W (Space 3) (by simpa only [Module.finrank_fin_fun] using hdimW3)
    let q : parabolic W →* LinearGroup 3 :=
      (linearGroupCongr eW).toMonoidHom.comp
        ((MonoidHom.fst (BinaryLinear.GL W) (BinaryLinear.GL (Space 4 ⧸ W))).comp (blockAction W))
    have hfst : Function.Surjective
        (MonoidHom.fst (BinaryLinear.GL W) (BinaryLinear.GL (Space 4 ⧸ W))) := by
      intro z
      exact ⟨(z, 1), rfl⟩
    have hq : Function.Surjective q := by
      apply (linearGroupCongr eW).surjective.comp
      apply hfst.comp
      exact blockAction_surjective W
    exact factor_contra q hq hres

private theorem fin3_cases : ∀ s : Finset (Fin 3),
    s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {2} ∨ s = {0,1} ∨ s = {0,2} ∨ s = {1,2} ∨ s = Finset.univ := by decide

lemma four_exhaust (U : Sylow 2 (LinearGroup 4))
    (b : BinaryLinear.InvariantNodeActions.Basis 3)
    (hU : (U : Subgroup (LinearGroup 4)) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup 4)) (hUP : (U : Subgroup (LinearGroup 4)) ≤ P) :
    ∃ cuts : Set (Fin 3), P = cutStabilizer b cuts := by
  let : Finite (LinearGroup 4) :=
    Finite.of_injective (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup 4)
    CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardSylow U
  have hmap : CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardBorel.map (MulAut.conj g).toMonoidHom =
      (U : Subgroup (LinearGroup 4)) := by
    change ((g • CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardSylow : Sylow 2 (LinearGroup 4)) : Subgroup (LinearGroup 4)) = _
    rw [hg]
  let Q := P.map (MulAut.conj g).symm.toMonoidHom
  have hBQ : CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardBorel ≤ Q := by
    intro u hu
    apply Subgroup.mem_map_equiv.mpr
    apply hUP
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨cuts, hQ⟩ := CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standard_overgroups_of_bruhat
    CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.hasBruhatDecomposition Q hBQ
  have hPQ : Q.map (MulAut.conj g).toMonoidHom = P :=
    (Subgroup.map_symm_eq_iff_map_eq Q (e := MulAut.conj g) (H := P)).mp rfl
  have hPc : P = cutStabilizer
      (CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardBasis.map g) cuts := by
    rw [← hPQ, hQ]
    exact BinaryLinear.InvariantNodeActions.cutStabilizer_map_conj _ _ _
  have hfull : cutStabilizer b Set.univ ≤ cutStabilizer
      (CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardBasis.map g) cuts := by
    calc
      cutStabilizer b Set.univ = (U : Subgroup (LinearGroup 4)) := hU.symm
      _ ≤ P := hUP
      _ = _ := hPc
  have halign := cutStabilizer_eq_of_fullFlag_le b
      (CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardBasis.map g) cuts hfull
  exact ⟨cuts, hPc.trans halign⟩

lemma four_factorization_le_one_of_bound (P : Subgroup (LinearGroup 4))
    (hbound : ∀ X : Subgroup (LinearGroup 4), X ≤ P → IsPGroup 3 X → Nat.card X ≤ 3) :
    (Nat.card P).factorization 3 ≤ 1 := by
  let : Finite P := Finite.of_injective (fun x : P => (x : LinearGroup 4)) Subtype.val_injective
  by_contra hn
  have hfac : 2 ≤ (Nat.card P).factorization 3 := by omega
  have h9 : 9 ∣ Nat.card P := by
    have hpow := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3)
      (Nat.card_pos.ne' : Nat.card P ≠ 0)).mpr hfac
    norm_num at hpow ⊢
    exact hpow
  obtain ⟨Y, hY⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) h9
  let X := Y.map P.subtype
  have hXle : X ≤ P := map_subtype_le Y
  have hXp : IsPGroup 3 X := (IsPGroup.of_card hY).map P.subtype
  have hXcard : Nat.card X = 9 := by
    rw [card_map_of_injective P.subtype_injective, hY]
    norm_num
  have hb := hbound X hXle hXp
  rw [hXcard] at hb
  omega

lemma middle_nine (b : BinaryLinear.InvariantNodeActions.Basis 3) :
    9 ∣ Nat.card (BinaryLinear.InvariantNodeActions.cutStabilizer b {(1 : Fin 3)}) := by
  let W := BinaryLinear.InvariantNodeActions.cutSpace b (1 : Fin 3)
  have hpar : BinaryLinear.InvariantNodeActions.cutStabilizer b {(1 : Fin 3)} = parabolic W := by
    simp [BinaryLinear.InvariantNodeActions.cutStabilizer, W]
  have hdimW : Module.finrank (ZMod 2) W = 2 := by simpa using cutSpace_finrank b (1 : Fin 3)
  have hdimQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
    have h : Module.finrank (ZMod 2) (Space 4 ⧸ W) + Module.finrank (ZMod 2) W = 4 := by
      simpa only [Module.finrank_fin_fun] using W.finrank_quotient_add_finrank
    rw [hdimW] at h
    omega
  let eW : W ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq W (Space 2) (by simpa only [Module.finrank_fin_fun] using hdimW)
  let eQ : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq (Space 4 ⧸ W) (Space 2)
      (by simpa only [Module.finrank_fin_fun] using hdimQ)
  let E := (linearGroupCongr eW).prodCongr (linearGroupCongr eQ)
  have hprod : 9 ∣ Nat.card (BinaryLinear.GL W × BinaryLinear.GL (Space 4 ⧸ W)) := by
    rw [Nat.card_prod, Nat.card_congr (linearGroupCongr eW).toEquiv,
      Nat.card_congr (linearGroupCongr eQ).toEquiv]
    change 9 ∣ Nat.card (LinearGroup 2) * Nat.card (LinearGroup 2)
    rw [four_linearGroup_card_formula]
    decide
  have hquot : Nat.card (parabolic W ⧸ pCore 2 (parabolic W)) =
      Nat.card (BinaryLinear.GL W × BinaryLinear.GL (Space 4 ⧸ W)) :=
    Nat.card_congr (quotientTwoCoreEquiv W).toEquiv
  have hcard : 9 ∣ Nat.card (parabolic W) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hquot]
    exact dvd_mul_of_dvd_left hprod _
  simpa [hpar] using hcard


theorem four (U : Sylow 2 (LinearGroup 4))
    (b : BinaryLinear.InvariantNodeActions.Basis 3)
    (hU : (U : Subgroup (LinearGroup 4)) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup 4)) (hUP : (U : Subgroup (LinearGroup 4)) ≤ P)
    (hproper : P ≠ ⊤)
    (hres : Group.IsSolvable (primeToResidual 3 P))
    (h3 : 3 ∣ Nat.card P)
    (hbound : ∀ X : Subgroup (LinearGroup 4), X ≤ P → IsPGroup 3 X → Nat.card X ≤ 3) :
    ∃ i : Fin 3, P = minimalParabolic b i := by
  classical
  obtain ⟨cuts, hP⟩ := four_exhaust U b hU P hUP
  let s : Finset (Fin 3) := Finset.univ.filter (fun i => i ∈ cuts)
  have hs : (s : Set (Fin 3)) = cuts := by
    ext i
    simp [s]
  rcases fin3_cases s with hs0 | hs0 | hs0 | hs0 | hs0 | hs0 | hs0 | hs0
  · have : P = ⊤ := by rw [hP, ← hs, hs0]; simp [cutStabilizer]
    exact (hproper this).elim
  · have hc : cuts = ({(0 : Fin 3)} : Set (Fin 3)) := by simpa [hs0] using hs.symm
    have hr : Group.IsSolvable (primeToResidual 3 (cutStabilizer b ({(0 : Fin 3)} : Set (Fin 3)))) := by
      have hr := hres
      rw [hP, hc] at hr
      exact hr
    exact (endpoint_parabolic_contra b 0 (Or.inl rfl) hr).elim
  · have hc : cuts = ({(1 : Fin 3)} : Set (Fin 3)) := by simpa [hs0] using hs.symm
    have h9 : 9 ∣ Nat.card P := by rw [hP, hc]; exact middle_nine b
    have hfac := four_factorization_le_one_of_bound P hbound
    have hpow : 3 ^ 2 ∣ Nat.card P := by norm_num; exact h9
    have hfac := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3)
      (Nat.card_pos.ne' : Nat.card P ≠ 0)).mp hpow
    omega
  · have hc : cuts = ({(2 : Fin 3)} : Set (Fin 3)) := by simpa [hs0] using hs.symm
    have hr : Group.IsSolvable (primeToResidual 3 (cutStabilizer b ({(2 : Fin 3)} : Set (Fin 3)))) := by
      have hr := hres
      rw [hP, hc] at hr
      exact hr
    exact (endpoint_parabolic_contra b 2 (Or.inr rfl) hr).elim
  · refine ⟨2, ?_⟩
    rw [hP, ← hs, hs0]
    congr 1
    ext j
    fin_cases j <;> simp
  · refine ⟨1, ?_⟩
    rw [hP, ← hs, hs0]
    congr 1
    ext j
    fin_cases j <;> simp
  · refine ⟨0, ?_⟩
    rw [hP, ← hs, hs0]
    congr 1
    ext j
    fin_cases j <;> simp
  · have h3U : ¬ 3 ∣ Nat.card (U : Subgroup (LinearGroup 4)) := by
      obtain ⟨n, hn⟩ := U.isPGroup'.exists_card_eq
      intro hd
      have hpow : 3 ∣ 2 ^ n := by simpa [hn] using hd
      have hc := (by decide : Nat.Coprime 3 2).pow_right n
      have hd1 : 3 ∣ 1 := hc.dvd_of_dvd_mul_left (by simpa using hpow)
      exact (by decide : ¬ 3 ∣ 1) hd1
    have hPU : P = (U : Subgroup (LinearGroup 4)) := by
      rw [hP, ← hs, hs0, hU]; simp
    exact (h3U (hPU ▸ h3)).elim


private noncomputable def blockCoordinates (c : Fin 5 → Fin 5) (k : Fin 5) :
    BlockSpace c k ≃ₗ[ZMod 2] Space (Nat.card (Block c k)) := by
  classical
  exact LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    ((Fintype.equivFin (Block c k)).trans (finCongr Nat.card_eq_fintype_card.symm)).symm
private theorem block_card_le (c : Fin 5 → Fin 5) (k : Fin 5) :
    Nat.card (Block c k) ≤ 5 := by
  simpa using Nat.card_le_card_of_injective (Subtype.val : Block c k → Fin 5) Subtype.val_injective
private theorem five_linearGroup_card_formula (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp
private theorem linear_not_solvable (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5) :
    ¬ Group.IsSolvable (LinearGroup n) := by
  let : Group.IsPerfect (LinearGroup n) := linearGroup_isPerfect n hn
  have : Nontrivial (LinearGroup n) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [five_linearGroup_card_formula]
    interval_cases n <;> decide
  exact Group.IsPerfect.not_isSolvable _
private theorem five_perfect_isPPerfect {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] : IsPPerfect 2 K := by
  intro N hN hp
  let := hN
  by_contra hne
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent

private lemma linear_solvable_le_two {n : ℕ} (hn : n ≤ 2) : Group.IsSolvable (LinearGroup n) := by
  interval_cases n
  · have hc : Nat.card (LinearGroup 0) = 1 := by rw [five_linearGroup_card_formula]; decide
    let : Subsingleton (LinearGroup 0) := by
      apply not_nontrivial_iff_subsingleton.mp
      intro h
      have hh := Finite.one_lt_card_iff_nontrivial.mpr h
      omega
    exact Group.isSolvable_of_comm (by intros; subsingleton)
  · have hc : Nat.card (LinearGroup 1) = 1 := by rw [five_linearGroup_card_formula]; decide
    let : Subsingleton (LinearGroup 1) := by
      apply not_nontrivial_iff_subsingleton.mp
      intro h
      have hh := Finite.one_lt_card_iff_nontrivial.mpr h
      omega
    exact Group.isSolvable_of_comm (by intros; subsingleton)
  · let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let hs : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      apply Group.isSolvable_of_ker_le_range
        (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      change Equiv.Perm.sign.ker ≤ (alternatingGroup (Fin 3)).subtype.range
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := linearTwoEquivSymmetricThree.toMonoidHom)
      linearTwoEquivSymmetricThree.injective

lemma flag_solvable_of_blocks_le_two (b : FiveBasis) (cuts : Set (Fin 4))
    (hblocks : ∀ k : Fin 5, Nat.card (Block (cutLabel cuts) k) ≤ 2) :
    Group.IsSolvable (flagStabilizer b cuts) := by
  let c := cutLabel cuts
  let : ∀ k : Fin 5, Group.IsSolvable (BinaryLinear.GL (BlockSpace c k)) := by
    intro k
    let e := linearGroupCongr (blockCoordinates c k)
    let : Group.IsSolvable (LinearGroup (Nat.card (Block c k))) :=
      linear_solvable_le_two (hblocks k)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable (∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) :=
    Group.isSolvable_finite_pi (fun k => BinaryLinear.GL (BlockSpace c k))
  let : Group.IsSolvable (∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) :=
    Group.isSolvable_finite_pi (fun k => BinaryLinear.GL (BlockSpace c k))
  let N := pCore 2 (flagStabilizer b cuts)
  let : N.Normal := inferInstance
  let : Group.IsNilpotent N := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable ((flagStabilizer b cuts) ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (flagDiagonalQuotientEquiv b cuts).toMonoidHom)
      (flagDiagonalQuotientEquiv b cuts).injective
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
private theorem linear_residual_top (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5) :
    primeToResidual 3 (LinearGroup n) = ⊤ := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := Atlas.psl_simple_high_rank n hn
  let : IsSimpleGroup (LinearGroup n) := (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  let : Group.IsPerfect (LinearGroup n) := linearGroup_isPerfect n hn
  have h3 : 3 ∣ Nat.card (LinearGroup n) := by
    rw [five_linearGroup_card_formula]
    interval_cases n <;> decide
  let : IsSimpleGroup ((LinearGroup n) ⧸ (⊥ : Subgroup (LinearGroup n))) := QuotientGroup.quotientBot.isSimpleGroup
  exact primeToResidual_eq_top_of_simple_quotient 3 2 (⊥ : Subgroup (LinearGroup n))
    (IsPGroup.of_subsingleton 2 _) five_perfect_isPPerfect
    (by simpa only [Nat.card_congr QuotientGroup.quotientBot.toEquiv] using h3)

lemma high_block_contra (b : FiveBasis) (cuts : Set (Fin 4))
    (hres : Group.IsSolvable (primeToResidual 3 (flagStabilizer b cuts)))
    (k : Fin 5) (hk : 3 ≤ Nat.card (Block (cutLabel cuts) k)) : False := by
  let c := cutLabel cuts
  let B := BlockSpace c k
  let : Finite (BinaryLinear.GL B) :=
    Finite.of_injective (fun g : BinaryLinear.GL B => (g : B → B)) DFunLike.coe_injective
  let f : flagStabilizer b cuts →* BinaryLinear.GL B :=
    (Pi.evalMonoidHom (fun k : Fin 5 => BinaryLinear.GL (BlockSpace c k)) k).comp
      (flagDiagonalAction b cuts)
  have heval : Function.Surjective
      (Pi.evalMonoidHom (fun k : Fin 5 => BinaryLinear.GL (BlockSpace c k)) k) := by
    intro a
    refine ⟨Function.update 1 k a, ?_⟩
    simp
  have hf : Function.Surjective f := heval.comp (flagDiagonalAction_surjective b cuts)
  have hm := Subgroup.map_primeToResidual_of_surjective 3 f hf
  let R := primeToResidual 3 (flagStabilizer b cuts)
  have hsmap : Group.IsSolvable (R.map f) := by
    let := hres
    exact Group.isSolvable_of_surjective (f := f.subgroupMap R)
      (f.subgroupMap_surjective R)
  have hsB : Group.IsSolvable (primeToResidual 3 (BinaryLinear.GL B)) := by
    rw [← hm]
    exact hsmap
  let e := linearGroupCongr (blockCoordinates c k)
  have hne : Nat.card (Block c k) ≤ 5 := block_card_le c k
  have htopLin := linear_residual_top (Nat.card (Block c k)) hk hne
  have htopB : primeToResidual 3 (BinaryLinear.GL B) = ⊤ := by
    apply top_unique
    intro x hx
    have hy : e x ∈ (primeToResidual 3 (BinaryLinear.GL B)).map e.toMonoidHom := by
      rw [Subgroup.map_primeToResidual_of_surjective 3 e.toMonoidHom e.surjective, htopLin]
      trivial
    obtain ⟨y, hyR, hye⟩ := Subgroup.mem_map.mp hy
    exact e.injective hye ▸ hyR
  let : Group.IsSolvable (⊤ : Subgroup (BinaryLinear.GL B)) := htopB ▸ hsB
  have hsB' : Group.IsSolvable (BinaryLinear.GL B) :=
    Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup (BinaryLinear.GL B)) ≃* BinaryLinear.GL B).toMonoidHom)
      Subgroup.topEquiv.surjective
  let : Group.IsSolvable (BinaryLinear.GL B) := hsB'
  have hsLin : Group.IsSolvable (LinearGroup (Nat.card (Block c k))) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact linear_not_solvable _ hk hne hsLin
lemma five_factorization_le_one_of_bound (P : Subgroup (LinearGroup 5))
    (_h3 : 3 ∣ Nat.card P)
    (hbound : ∀ X : Subgroup (LinearGroup 5), X ≤ P → IsPGroup 3 X → Nat.card X ≤ 3) :
    (Nat.card P).factorization 3 ≤ 1 := by
  by_contra hn
  have hfac : 2 ≤ (Nat.card P).factorization 3 := by omega
  have h9 : 9 ∣ Nat.card P := by
    have hpow := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3)
      (Nat.card_pos.ne' : Nat.card P ≠ 0)).mpr hfac
    norm_num at hpow ⊢
    exact hpow
  obtain ⟨Y, hY⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) h9
  let X := Y.map P.subtype
  have hXle : X ≤ P := by exact map_subtype_le Y
  have hXp : IsPGroup 3 X := (IsPGroup.of_card hY).map P.subtype
  have hXcard : Nat.card X = 9 := by
    rw [card_map_of_injective P.subtype_injective, hY]
    norm_num
  have hb := hbound X hXle hXp
  rw [hXcard] at hb
  omega

lemma five_exhaust (U : Sylow 2 (LinearGroup 5))
    (b : BinaryLinear.InvariantNodeActions.Basis 4)
    (hU : (U : Subgroup (LinearGroup 5)) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup 5)) (hUP : (U : Subgroup (LinearGroup 5)) ≤ P) :
    ∃ cuts : Set (Fin 4), P = cutStabilizer b cuts := by
  obtain ⟨c, cuts, hc⟩ := BinaryLinear.FiveFlagGeometry.isFlagParabolic_of_sylow_le U P hUP
  have hfull : cutStabilizer b Set.univ ≤ cutStabilizer c cuts := by
    calc
      cutStabilizer b Set.univ = (U : Subgroup (LinearGroup 5)) := hU.symm
      _ ≤ P := hUP
      _ = cutStabilizer c cuts := hc
  have halign := BinaryLinear.InvariantNodeActions.cutStabilizer_eq_of_fullFlag_le b c cuts hfull
  exact ⟨cuts, hc.trans halign⟩

private def blockCount (s : Finset (Fin 4)) (k : Fin 5) : ℕ :=
  (Finset.univ.filter fun i : Fin 5 => (s.filter fun j => j.val < i.val).card = k.val).card

private theorem blockCount_eq (s : Finset (Fin 4)) (k : Fin 5) :
    blockCount s k = Nat.card (Block (cutLabel (s : Set (Fin 4))) k) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold blockCount cutLabel
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [Fin.ext_iff]
  have he : s.filter (fun j => j.val < i.val) =
      Finset.univ.filter (fun j : Fin 4 => j ∈ (s : Set (Fin 4)) ∧ j.val < i.val) := by
    ext j
    simp
  rw [he]
  apply Iff.of_eq
  congr 3

private theorem finite_cut_classification_one :
    ∀ s : Finset (Fin 4),
      (∀ k : Fin 5, blockCount s k ≤ 2) →
      (∑ k : Fin 5, if blockCount s k = 2 then 1 else 0) = 1 →
      ∃ i : Fin 4, s = ({i} : Finset (Fin 4))ᶜ := by decide

theorem five (U : Sylow 2 (LinearGroup 5))
    (b : BinaryLinear.InvariantNodeActions.Basis 4)
    (hU : (U : Subgroup (LinearGroup 5)) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup 5)) (hUP : (U : Subgroup (LinearGroup 5)) ≤ P)
    (hproper : P ≠ ⊤)
    (hres : Group.IsSolvable (primeToResidual 3 P))
    (h3 : 3 ∣ Nat.card P)
    (hbound : ∀ X : Subgroup (LinearGroup 5), X ≤ P → IsPGroup 3 X → Nat.card X ≤ 3) :
    ∃ i : Fin 4, P = minimalParabolic b i := by
  classical
  have _ := hproper
  obtain ⟨cuts, hP⟩ := five_exhaust U b hU P hUP
  have hblocks : ∀ k : Fin 5, Nat.card (Block (cutLabel cuts) k) ≤ 2 := by
    intro k
    by_contra hk
    have hr : Group.IsSolvable (primeToResidual 3 (BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts)) := by
      change Group.IsSolvable (primeToResidual 3 (cutStabilizer b cuts))
      rw [← hP]
      exact hres
    exact high_block_contra b cuts (by simpa using hr) k (by omega)
  have hsP : Group.IsSolvable (BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts) := by
    change Group.IsSolvable (cutStabilizer b cuts)
    exact flag_solvable_of_blocks_le_two b cuts hblocks
  have hfac : (Nat.card P).factorization 3 ≤ 1 := five_factorization_le_one_of_bound P h3 hbound
  have hfacpos : (Nat.card P).factorization 3 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd (by decide) (Nat.card_pos.ne') h3).ne'
  have hfacone : (Nat.card P).factorization 3 = 1 := by omega
  let s : Finset (Fin 4) := Finset.univ.filter (fun i => i ∈ cuts)
  have hs : (s : Set (Fin 4)) = cuts := by ext i; simp [s]
  have hcount : ∀ k : Fin 5, blockCount s k = Nat.card (Block (cutLabel cuts) k) := by
    intro k
    rw [← hs]
    exact blockCount_eq s k
  have hsum : (∑ k : Fin 5, if blockCount s k = 2 then 1 else 0) = 1 := by
    have hthree := BinaryLinear.SmallParabolicLevi.TwoNodes.flag_three_part_eq_two_blocks b cuts hsP
    have hthree' : (Nat.card P).factorization 3 =
        ∑ k : Fin 5, if Nat.card (Block (cutLabel cuts) k) = 2 then 1 else 0 := by
      rw [hP]
      exact hthree
    calc
      (∑ k : Fin 5, if blockCount s k = 2 then 1 else 0) =
          ∑ k : Fin 5, if Nat.card (Block (cutLabel cuts) k) = 2 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcount k]
      _ = (Nat.card P).factorization 3 := hthree'.symm
      _ = 1 := hfacone
  obtain ⟨i, hi⟩ := finite_cut_classification_one s
    (by
      intro k
      rw [hcount k]
      exact hblocks k)
    hsum
  have hc : cuts = ({i}ᶜ : Set (Fin 4)) := by
    calc
      cuts = (s : Set (Fin 4)) := hs.symm
      _ = (({i} : Finset (Fin 4))ᶜ : Finset (Fin 4)) := congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) hi
      _ = ({i}ᶜ : Set (Fin 4)) := by ext j; simp
  refine ⟨i, ?_⟩
  rw [hP, hc]
  rfl



end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.BinaryHigher.FlagRecognition
