module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.TwoQuotient
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.BinaryFourQuotient
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.AlternatingModels
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The three Mathieu local obstructions for a deleted-five block

The octad quotient either retains a deleted block in A8 or kills the full
order-sixteen layer. In the latter case self-centralization kills the
block's two-core too, contradicting the binary-four local embedding theorem.
The sextet maps to S6 with solvable kernel. Its local perfect image retains
the A5 two-core quotient; restriction to A6 and the proper Sylow-overgroup
orders eight and twenty-four exclude it. The trio order has no factor five.

Every argument retains the original subgroup and full Sylow. Source:
Aschbacher–Smith A.3.14 and H.14.2–3, using the native local models of
GLS3 Table 5.3e and the deleted-block quotient dichotomy.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.DeletedM24
open ChapterC LinearFourCore PairOvergroups PairOvergroups.QuotientConstruction

private theorem local_perfect {G : Type*} [Group G] {B S : Subgroup G}
    (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem altSix_core : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pCore 2 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top with h|h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 6))) := h ▸ pCore_isPGroup
    have hp' := hp.of_equiv topEquiv
    obtain ⟨n,hn⟩ := hp'.exists_card_eq
    have hc : Nat.Coprime (2^n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
    rw [←hn,nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc

private theorem altSix_not_local_section (S : Sylow 2 (alternatingGroup (Fin 6)))
    (B : Subgroup (alternatingGroup (Fin 6)))
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hB : B ∈ localCComponents S) : False := by
  have hcard : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have h5 : 5 ∣ Nat.card B := (by decide : 5 ∣ 60).trans
    (hcard ▸ card_quotient_dvd_card (pCore 2 B))
  have hjoin : B ⊔ (S : Subgroup (alternatingGroup (Fin 6))) = ⊤ := by
    by_contra hn
    have hd := h5.trans (card_dvd_of_le
      (show B ≤ B ⊔ (S : Subgroup (alternatingGroup (Fin 6))) from le_sup_left))
    rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour S _ le_sup_right hn
      with h | h <;> rw [h] at hd <;> norm_num at hd
  change (B.subgroupOf (B ⊔ (S : Subgroup (alternatingGroup (Fin 6))))).IsCComponent at hB
  rw [hjoin] at hB
  have hsub : B.IsSubnormal := by
    have hh := hB.subnormal.trans' IsSubnormal.top
    simpa only [map_subgroupOf_eq_of_le le_top] using hh
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hsub.eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  · rw [h,card_bot] at h5
    norm_num at h5
  · let d : B ≃* alternatingGroup (Fin 6) := (MulEquiv.subgroupCongr h).trans topEquiv
    have hd := (Nat.card_congr (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).toEquiv)
    rw [altSix_core, Nat.card_congr QuotientGroup.quotientBot.toEquiv,
      nat_card_alternatingGroup] at hd
    rw [hcard] at hd
    norm_num at hd

private theorem symSix_not_local_section (S : Sylow 2 (Equiv.Perm (Fin 6)))
    (B : Subgroup (Equiv.Perm (Fin 6)))
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hB : B ∈ localCComponents S) : False := by
  let := local_perfect hB
  have hBA : B ≤ alternatingGroup (Fin 6) := by
    intro b hb
    rw [Equiv.Perm.mem_alternatingGroup]
    let f := Equiv.Perm.sign.comp B.subtype
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨b,hb⟩) 1)
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal (alternatingGroup (Fin 6))
  let d := subgroupOfEquivOfLe hBA
  apply altSix_not_local_section T (B.subgroupOf (alternatingGroup (Fin 6)))
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans e)
  rw [hT]
  exact local_restrict hB hBA

private theorem solvable_kernel_symmetric_six {G : Type*} [Group G] [Finite G]
    (q : G →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (S : Sylow 2 G) (B : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hl : B ∈ localCComponents S) : False := by
  let := local_perfect hl
  let d := hB.2.2.quotient_iso.some
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := d.isSimpleGroup
  let f := q.subgroupMap B
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.subgroupMap B).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap q.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : q.ker => (x : G)) he)))
  let e := (PerfectCoreTwoExtension.solvableKernelQuotientEquiv f
    (q.subgroupMap_surjective B)).symm.trans d
  exact symSix_not_local_section (S.mapSurjective hq) (B.map q) e
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
theorem seed_octad_not_local (S : Sylow 2 (octadStabilizer seedOctad))
    (B : Subgroup (octadStabilizer seedOctad)) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) : False := by
  classical
  let a : seedOctad.val ≃ Fin 8 := Fintype.equivFinOfCardEq (by
    rw [←Nat.card_eq_fintype_card,seed_card])
  let e := a.altCongrHom.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm
  let q := e.toMonoidHom.comp alternatingAction
  have hq : Function.Surjective q := e.surjective.comp alternatingAction_surjective
  have hk : q.ker = (action seedOctad).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    ext x
    change alternatingAction x = 1 ↔ action seedOctad x = 1
    simp only [Subtype.ext_iff,alternatingAction_coe,Subgroup.coe_one]
  have hp : IsPGroup 2 q.ker := by
    rw [hk,←seed_core_eq_kernel]
    exact pCore_isPGroup
  let f := q.subgroupMap B
  have hfp : IsPGroup 2 f.ker := by
    rw [show f = q.subgroupMap B from rfl,Subgroup.ker_subgroupMap]
    exact hp.comap_subtype
  rcases hB.layer_le_ker_or_ker_central f hfp with hu | hc
  · have hU : (blockU B).map B.subtype = q.ker := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨b,hb,rfl⟩
        exact congrArg Subtype.val (hu hb)
      · rw [card_map_of_injective B.subtype_injective,hB.blockU_card,hk,kernel_card]
    apply Chapter2.AlternatingTerminal.not_local_of_binary_four_quotient q hq hp B hB ?_ S hl
    rintro _ ⟨b,hb,rfl⟩
    rw [hk]
    apply seed_kernel_selfCentralizing
    rw [←hk,←hU]
    rintro _ ⟨u,hu,rfl⟩
    exact congrArg B.subtype (hB.2.1.core_centralizes_blockU hb u hu)
  · have himage : IsAlternatingBlock (B.map q) 5 :=
      hB.of_surjective_central_two_kernel f (q.subgroupMap_surjective B) hfp hc.2
    exact Chapter13.Section05.NormalBranch.DeletedFive.not_psl4Two_of_alternatingFive
      (B.map q) himage ((card_map_of_injective (B.map q).subtype_injective).trans himage.blockU_card)
      ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨MulEquiv.refl _⟩⟩

/-- The literal sextet quotient excludes a deleted-five block local at a full Sylow. -/
theorem sextet_not_local (S : Sylow 2 (sextetStabilizer standardSextet))
    (B : Subgroup (sextetStabilizer standardSextet)) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) : False := by
  let : Group.IsSolvable SextetCore.columnHom.ker := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    rw [SextetCore.columnHom_kernel_card] at hd
    have hh : p ∣ 2^6 * 3 := hd
    rcases hp.dvd_mul.mp hh with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  exact solvable_kernel_symmetric_six SextetCore.columnHom SextetCore.columnHom_surjective S B hB hl

/-- The actual trio affine quotient has no factor five in its order. -/
theorem trio_no_deleted (B : Subgroup (trioStabilizer standardTrio))
    (hB : IsAlternatingBlock B 5) : False := by
  let f := affineQuotient affineCoverage
  have hp := affineQuotient_kernel_isPGroup affineCoverage
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker,hn] at hc
  have hi : Nat.card f.range ∣ 1008 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [Nat.card_prod,Matrix.PSL3Two.card_SL] at hd
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
      show Nat.factorial 3 = 6 from rfl] using hd
  have h5 : 5 ∣ Nat.card (trioStabilizer standardTrio) := by
    have hq := Chapter13.Section05.NormalBranch.DeletedFive.alternatingFive_quotient_card B hB
    have hd : 5 ∣ Nat.card B := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),hq]
      exact dvd_mul_of_dvd_left (by decide) _
    exact hd.trans B.card_subgroup_dvd_card
  have hd : 5 ∣ 2^n * 1008 := (hc ▸ h5).trans (Nat.mul_dvd_mul_left _ hi)
  have hh := ((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left hd
  norm_num at hh

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.DeletedM24
