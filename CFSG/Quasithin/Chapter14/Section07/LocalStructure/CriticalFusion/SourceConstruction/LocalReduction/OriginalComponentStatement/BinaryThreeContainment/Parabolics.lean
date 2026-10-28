module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.Actions
public import Theory.SpecificGroups.PSL3Two.Parabolics.SolvableOvergroups
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Two solvable lifts when the binary component action is inner

The two parabolics through the actual component Sylow generate its PSL3(2)
quotient. Each original Sylow actor has an inner conjugator in the component
Sylow intersection. The point group centralizes the quotient, so the actual
parabolic lifts are both normalized by the full point-Sylow group. Their
solvability retains the component two-core, and their join is the component.
Source: Aschbacher--Smith 14.7.47, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
variable {G : Type*} [Group G] [Finite G]

private theorem lift_normalized
    (C : Subgroup G) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL)
    (J : Subgroup Matrix.PSL3Two.PSL) (x : G)
    (hx : ∀ y ∈ J, MulAut.congr e (normalQuotientAction C (pCore 2 C) x) y ∈ J) :
    x ∈ normalizer
      ((J.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C)))).map C.subtype : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let qE := e.toMonoidHom.comp q
  let D := (J.comap qE).map C.subtype
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨c,hc,rfl⟩,rfl⟩
    refine ⟨MulAut.conjNormal x c,?_,rfl⟩
    have hh := hx (e (q c)) hc
    change e (q (MulAut.conjNormal x c)) ∈ J
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply,q,
      normalQuotientAction_apply_mk] using hh
  · exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj x).injective).symm

/-- Inner Sylow action gives two solvable point-Sylow-invariant lifts generating C. -/
theorem inner_solvable_pair
    (A C : Subgroup G) [C.Normal] (S : Sylow 2 G)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) (hout : ¬ A ≤ C)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL)
    (hi : ∀ x ∈ (S : Subgroup G), normalQuotientAction C (pCore 2 C) x ∈
      MulAut.innerSubgroup (C ⧸ pCore 2 C)) :
    ∃ D E : Subgroup G, D ⊔ E = C ∧ Group.IsSolvable D ∧ Group.IsSolvable E ∧
      A ⊔ (S : Subgroup G) ≤ normalizer (D : Set G) ∧
      A ⊔ (S : Subgroup G) ≤ normalizer (E : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let qE := e.toMonoidHom.comp q
  have hq : Function.Surjective qE := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let R := P.mapSurjective (f := qE) hq
  obtain ⟨J,K,hJ,hK,hJK,hR,_,_,_⟩ := Matrix.PSL3Two.sylow_parabolics R
  have hRJ : (R : Subgroup Matrix.PSL3Two.PSL) ≤ J := hR ▸ inf_le_left
  have hRK : (R : Subgroup Matrix.PSL3Two.PSL) ≤ K := hR ▸ inf_le_right
  have hfix := outside_action_trivial A C S hp hc hn hout
    (e.trans Matrix.PSL3Two.equiv.symm)
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    let e' := e.trans Matrix.PSL3Two.equiv.symm
    apply bot_unique
    intro z hz
    have hh := (centerCongr e' ⟨z,hz⟩).property
    change e' z ∈ center Matrix.PSL3Two.SL at hh
    rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact e'.map_eq_one_iff.mp hh
  let lift (B : Subgroup Matrix.PSL3Two.PSL) := (B.comap qE).map C.subtype
  have hnorm (B : Subgroup Matrix.PSL3Two.PSL) (hRB : (R : Subgroup _) ≤ B) :
      A ⊔ (S : Subgroup G) ≤ normalizer (lift B : Set G) := by
    apply sup_le
    · intro x hx
      apply lift_normalized C e B x
      intro y hy
      rw [show normalQuotientAction C (pCore 2 C) x = 1 from hfix hx,map_one]
      exact hy
    · intro x hx
      obtain ⟨c,hcS,hce⟩ := normalQuotient_inner_sylow_lift C S hz x hx (hi x hx)
      have hcP : c ∈ (P : Subgroup C) := by rw [hP]; exact hcS
      have hcB : qE c ∈ B := hRB (mem_map_of_mem qE hcP)
      apply lift_normalized C e B x
      intro y hy
      rw [←hce,normalQuotientAction_inner,MulAut.congr_conj]
      exact B.mul_mem (B.mul_mem hcB hy) (B.inv_mem hcB)
  have hsolv (B : Subgroup Matrix.PSL3Two.PSL)
      (hRB : (R : Subgroup _) ≤ B) (hB : B ≠ ⊤) : Group.IsSolvable (lift B) := by
    let : Group.IsSolvable B := Matrix.PSL3Two.solvableSylowOvergroups R B hRB hB
    have hk : qE.ker = pCore 2 C := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let : Group.IsNilpotent qE.ker := hk ▸ pCore_isPGroup.isNilpotent
    let : Group.IsSolvable (B.comap qE) := isSolvable_comap_of_solvable_ker qE B
    exact Group.isSolvable_of_surjective (C.subtype.subgroupMap_surjective (B.comap qE))
  refine ⟨lift J,lift K,?_,hsolv J hRJ hJ.1,hsolv K hRK hK.1,
    hnorm J hRJ,hnorm K hRK⟩
  change (J.comap qE).map C.subtype ⊔ (K.comap qE).map C.subtype = C
  rw [←Subgroup.map_sup,comap_sup_eq qE J K hq,hJ.sup_eq_top_of_ne hK hJK,
    comap_top,←MonoidHom.range_eq_map,range_subtype]


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
