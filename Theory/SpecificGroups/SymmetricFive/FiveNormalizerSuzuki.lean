module

public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.TargetCores
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The actual Suzuki group of order twenty as a five-normalizer

A group of order twenty with trivial two-core acts faithfully on the five
cosets of a Sylow two-subgroup. Its normal Sylow five then identifies the
image with a five-normalizer in S₅. Sylow conjugacy gives the equivalence
for every specified Sylow five-subgroup. The concrete Sz(2) has the required
order and trivial two-core by its root and Weyl matrix calculations.

Source: the elementary local recognition used in Aschbacher–Smith J.4.4(3).
No permutation marking or abstract semidirect-product model is assumed.
-/

public section
noncomputable section
open Subgroup MulAction
namespace Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem normal_five {M:Type*} [Group M] [Finite M]
    (hcard:Nat.card M=20) (P:Sylow 5 M) : (P:Subgroup M).Normal := by
  have hc : Nat.card P=5 := by
    rw [P.card_eq_multiplicity,hcard]
    decide +kernel
  have hi : (P:Subgroup M).index=4 := by
    have h := (P:Subgroup M).card_mul_index
    rw [hc,hcard] at h
    omega
  have hn : Nat.card (Sylow 5 M)=1 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hb := Nat.le_of_dvd (by decide:0<4) hd
    have hm := card_sylow_modEq_one 5 M
    change Nat.card (Sylow 5 M)%5=1%5 at hm
    omega
  let : Subsingleton (Sylow 5 M) := (Nat.card_eq_one_iff_unique.mp hn).1
  exact P.normal_of_subsingleton

private theorem embeds {M:Type*} [Group M] [Finite M]
    (hc:Nat.card M=20) (hcore:pCore 2 M=⊥) :
    ∃ f:M→*D, Function.Injective f := by
  classical
  let S:Sylow 2 M := Classical.choice inferInstance
  have hS : Nat.card S=4 := by
    rw [S.card_eq_multiplicity,hc]
    decide +kernel
  have hi : (S:Subgroup M).index=5 := by
    have h := (S:Subgroup M).card_mul_index
    rw [hS,hc] at h
    omega
  let pts := M⧸(S:Subgroup M)
  let e:pts≃Fin 5 := (Finite.equivFin pts).trans (finCongr hi)
  let f:M→*D := (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom M pts)
  refine ⟨f,(MonoidHom.ker_eq_bot_iff f).mp ?_⟩
  have hk : f.ker=(S:Subgroup M).normalCore := by
    rw [MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom e).injective]
    exact (S:Subgroup M).normalCore_eq_ker.symm
  rw [hk]
  apply bot_unique
  rw [←hcore]
  exact le_sSup ⟨inferInstance,S.isPGroup'.to_le (S:Subgroup M).normalCore_le⟩

private theorem normalizer_model {M:Type*} [Group M] [Finite M]
    (hc:Nat.card M=20) (hcore:pCore 2 M=⊥) (P:Sylow 5 D) :
    Nonempty (M≃*normalizer ((P:Subgroup D):Set D)) := by
  classical
  obtain ⟨f,hf⟩ := embeds hc hcore
  let R:Sylow 5 M := Classical.choice inferInstance
  let : (R:Subgroup M).Normal := normal_five hc R
  have hcR : Nat.card R=5 := by
    rw [R.card_eq_multiplicity,hc]
    decide +kernel
  have hmap : Nat.card ((R:Subgroup M).map f)=5 :=
    (card_map_of_injective hf).trans hcR
  have hi : ((R:Subgroup M).map f).index=24 := by
    have h := ((R:Subgroup M).map f).card_mul_index
    rw [hmap] at h
    have hD:Nat.card D=120 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [hD] at h
    omega
  let R':Sylow 5 D := (R.isPGroup'.map f).toSylow (by rw [hi];decide)
  have hle : f.range≤normalizer ((R':Subgroup D):Set D) := by
    have h := (R:Subgroup M).le_normalizer_map f
    simpa only [R',IsPGroup.toSylow_coe,normalizer_eq_top,←MonoidHom.range_eq_map] using h
  have hrange : f.range=normalizer ((R':Subgroup D):Set D) := by
    apply eq_of_le_of_card_ge hle
    rw [card_normalizer,Nat.card_congr (MulEquiv.ofBijective f.rangeRestrict
      ⟨(fun x y h => hf (congrArg Subtype.val h)),MonoidHom.rangeRestrict_surjective f⟩).toEquiv.symm,hc]
  obtain ⟨g,hg⟩ := exists_smul_eq D R' P
  have hmapP : (R':Subgroup D).map (MulAut.conj g).toMonoidHom=(P:Subgroup D) := by
    have h := congrArg (fun X:Sylow 5 D=>(X:Subgroup D)) hg
    rw [Sylow.smul_def,Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def] at h
    exact h
  have hnorm : (normalizer ((R':Subgroup D):Set D)).map (MulAut.conj g).toMonoidHom=normalizer ((P:Subgroup D):Set D) := by
    rw [map_equiv_normalizer_eq,hmapP]
  let e:M≃*f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨(fun x y h => hf (congrArg Subtype.val h)),MonoidHom.rangeRestrict_surjective f⟩
  exact ⟨e.trans ((MulEquiv.subgroupCongr hrange).trans
    (((MulAut.conj g).subgroupMap (normalizer ((R':Subgroup D):Set D))).trans (MulEquiv.subgroupCongr hnorm)))⟩

theorem normalizer_equiv_suzuki (P:Sylow 5 D) : Nonempty ((normalizer ((P:Subgroup D):Set D))≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  obtain ⟨e⟩ := normalizer_model BenderSuzuki.MatrixGroups.suzukiZero_card
    ReeF4.Parabolics.Binary.suzuki_twoCore_eq_bot P
  exact ⟨e.symm⟩
/-- The order and trivial two-core recognize the literal binary Suzuki group. -/
theorem equiv_suzuki_of_card_twenty {M:Type*} [Group M] [Finite M]
    (hc:Nat.card M=20) (hcore:pCore 2 M=⊥) :
    Nonempty (M≃*BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  let P:Sylow 5 D:=Classical.choice inferInstance
  obtain ⟨e⟩:=normalizer_model hc hcore P
  obtain ⟨f⟩:=normalizer_equiv_suzuki P
  exact ⟨e.trans f⟩

end Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
