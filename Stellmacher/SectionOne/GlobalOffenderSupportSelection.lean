module
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# Selecting a factor fixing a non-Sylow-fixed vector

Under the faithful elementary abelian action hypotheses of Section 1, let
w be fixed by J(V,S) but not by S. If the fixed space of E(V,S) is fixed
by S, some raw one-seven factor fixes w.

The global factors generate normal E=E(V,S), with J(V,S)=S intersect E.
For each factor D, Q=S intersect D has order two, and C_V(D) has index
two in C_V(Q). If no factor fixes w, the vectors w and s acting on w lie
in the same nonidentity coset for every such index-two pair. Hence their
quotient lies in C_V(E). Coprime action by the join of the derived
order-three factors splits V as C_V(E) plus [V,E]. The latter is
S-invariant and the former is pointwise fixed by the stated hypothesis,
so that quotient lies in both complementary summands and is trivial.

This proves the choice of j with [w,E_j]=1 in Stellmacher (6.4), journal
p32 of refs/latex/stellmacher-n-group.tex, using the factor structure of
(1.7). All actions are restrictions of the supplied ambient action.
-/

open scoped IsMulCommutative
open Stellmacher.SectionOne.RankOneThreeGroupAssembly
namespace Stellmacher.SectionOne
universe u

/-- The actual global offender action splits into its fixed and commutator subgroups. -/
public theorem oneSeven_global_fixed_support_compl
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V] :
    IsCompl (FixedPoints.subgroup (oneSevenGenerated (G := G) (V := V)) V)
      (commutatorAction (oneSevenGenerated (G := G) (V := V)) V) := by
  let I := {D : Subgroup G // IsOneSevenFactor (V := V) D}
  let E := oneSevenGenerated (G := G) (V := V)
  let K (i : I) := (commutator i.val).map i.val.subtype
  let P : Subgroup G := ⨆ i, K i
  have hgen : E = ⨆ i : I, i.val := by
    apply le_antisymm
    · exact sSup_le fun D hD => le_iSup (fun i : I => i.val) ⟨D, hD⟩
    · exact iSup_le fun i => le_sSup i.property
  have hPthree : P ≤ pCore 3 G :=
    iSup_le fun i => oneSevenFactor_derived_le_threeCore i.val i.property
  have hPp : IsPGroup 3 P := (pCore_isPGroup (p := 3) (G := G)).of_injective
    (Subgroup.inclusion hPthree) (Subgroup.inclusion_injective hPthree)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card V) := by
    obtain ⟨a, ha⟩ := hPp.exists_card_eq
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [ha, hb]
    exact (show Nat.Coprime 3 2 by decide).pow a b
  have hPE : P ≤ E := by
    rw [hgen]
    exact iSup_le fun i => (Subgroup.map_subtype_le _).trans (le_iSup _ i)
  have hfix : FixedPoints.subgroup P V = FixedPoints.subgroup E V := by
    apply le_antisymm
    · intro v hv
      have hEfix : E ≤ fixingSubgroup G ({v} : Set V) := by
        rw [hgen]
        refine iSup_le fun i d hd => ?_
        rw [mem_fixingSubgroup_iff]
        intro w hw
        subst w
        apply oneSevenFactor_fixes_derived_fixedPoints i.val i.property d hd v
        intro k
        exact hv (⟨k, (le_iSup K i) k.property⟩ : P)
      intro e
      exact (mem_fixingSubgroup_iff (M := G)).mp (hEfix e.property) v rfl
    · intro v hv p
      exact hv (⟨p, hPE p.property⟩ : E)
  have hU : commutatorAction P V = commutatorAction E V := by
    rw [commutatorAction_eq_iSup_of_eq_iSup K rfl,
      commutatorAction_eq_iSup_of_eq_iSup (fun i : I => i.val) hgen]
    congr 1
    funext i
    exact (oneSevenFactor_full_commutator_eq_derived i.val i.property).symm
  rw [← hfix, ← hU]
  exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := P)
    (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
    hcop inferInstance

public theorem exists_oneSevenFactor_fixing_of_not_sylow_fixed
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hfix : FixedPoints.subgroup (oneE (V := V) (S : Subgroup G)) V ≤
      FixedPoints.subgroup S V)
    (w : V) (hwJ : w ∈ FixedPoints.subgroup (oneJ (V := V) (S : Subgroup G)) V)
    (hwS : w ∉ FixedPoints.subgroup S V) :
    ∃ D : Subgroup G, IsOneSevenFactor (V := V) D ∧
      w ∈ FixedPoints.subgroup D V := by
  classical
  by_contra hnone
  have hnfix (D : Subgroup G) (hD : IsOneSevenFactor (V := V) D) :
      w ∉ FixedPoints.subgroup D V := fun hw => hnone ⟨D, hD, hw⟩
  let E := oneSevenGenerated (G := G) (V := V)
  let F := oneSevenFactors (G := G) (V := V)
  let J := oneJ (V := V) (S : Subgroup G)
  let C := FixedPoints.subgroup E V
  let U := commutatorAction E V
  obtain ⟨hEnormal, hprod, _⟩ := oneSeven_global_product h S
  let _ : E.Normal := hEnormal
  obtain ⟨hJid, hEid⟩ := oneSeven_global_identification h S
  have hF (D : Subgroup G) (hD : D ∈ F) : IsOneSevenFactor (V := V) D :=
    (mem_oneSevenFactors_iff D).mp hD
  obtain ⟨_, _, _, hcoord⟩ := sl2_product_sylow_coordinates S E hEnormal F hprod
    (fun D hD => (hF D hD).1)
  have hCfix : C ≤ FixedPoints.subgroup S V := by
    have hle : oneE (V := V) (S : Subgroup G) ≤ E := hEid.le
    intro v hv
    apply hfix
    intro e
    exact hv (⟨e, hle e.property⟩ : E)
  have hnorm : (S : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := by
    change (S : Subgroup G) ≤ Subgroup.normalizer
      (oneJ (V := V) (S : Subgroup G) : Set G)
    rw [hJid]
    apply le_trans (le_inf (S : Subgroup G).le_normalizer
      (show (S : Subgroup G) ≤ Subgroup.normalizer (E : Set G) by
        rw [Subgroup.normalizer_eq_top]; exact le_top))
    exact Subgroup.inf_normalizer_le_normalizer_inf
  let _ : IsInvariant S V (FixedPoints.subgroup J V) :=
    fixedPoints_isInvariant_of_normalizing_actor S J hnorm
  let _ : IsInvariant S V U :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor S E
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hcompl : IsCompl C U := oneSeven_global_fixed_support_compl
  apply hwS
  intro s
  have hswJ : s • w ∈ FixedPoints.subgroup J V :=
    (IsInvariant.invariant (A := S) (H := FixedPoints.subgroup J V) s w).mp hwJ
  have hswNot (D : Subgroup G) (hD : IsOneSevenFactor (V := V) D) :
      s • w ∉ FixedPoints.subgroup D V := by
    intro hsw
    apply hnfix (D.conjBy (s : G)⁻¹) (hD.conjBy D (s : G)⁻¹)
    intro d
    obtain ⟨d0, hd0, hd⟩ := d.property
    have hds := hsw (⟨d0, hd0⟩ : D)
    change d0 • ((s : G) • w) = (s : G) • w at hds
    have he := congrArg (fun v : V => (s : G)⁻¹ • v) hds
    change (d : G) • w = w
    rw [← hd]
    change ((s : G)⁻¹ * d0 * ((s : G)⁻¹)⁻¹) • w = w
    simpa only [inv_inv, ← mul_smul, inv_mul_cancel, one_smul, mul_assoc] using he
  have hdeltaC : w⁻¹ * (s • w) ∈ C := by
    have hEfix : E ≤ fixingSubgroup G ({w⁻¹ * (s • w)} : Set V) := by
      apply sSup_le
      intro D hD
      let Q : Subgroup G := (S : Subgroup G) ⊓ D
      let A := FixedPoints.subgroup Q V
      let CD := FixedPoints.subgroup D V
      have hQJ : Q ≤ J := by
        change Q ≤ oneJ (V := V) (S : Subgroup G)
        rw [hJid]
        exact inf_le_inf_left _ (le_sSup hD)
      have hwA : w ∈ A := fun q => hwJ (⟨q, hQJ q.property⟩ : J)
      have hswA : s • w ∈ A := fun q => hswJ (⟨q, hQJ q.property⟩ : J)
      have hidx : (CD.subgroupOf A).index = 2 :=
        oneSevenFactor_involution_fixed_relIndex h.action_faithful D Q hD inf_le_right
        (hcoord D ((mem_oneSevenFactors_iff D).mpr hD))
      have hdelta : w⁻¹ * (s • w) ∈ CD := by
        have hh := (CD.subgroupOf A).mul_mem_iff_of_index_two hidx
          (a := (⟨w, hwA⟩ : A)⁻¹) (b := ⟨s • w, hswA⟩)
        apply hh.mpr
        change (w⁻¹ ∈ CD ↔ s • w ∈ CD)
        simp only [Subgroup.inv_mem_iff]
        exact iff_of_false (hnfix D hD) (hswNot D hD)
      intro d hd
      rw [mem_fixingSubgroup_iff]
      intro v hv
      subst v
      exact hdelta (⟨d, hd⟩ : D)
    intro e
    exact (mem_fixingSubgroup_iff (M := G)).mp (hEfix e.property) _ rfl
  have hdeltaU : w⁻¹ * (s • w) ∈ U := by
    let _ : CommGroup V := IsMulCommutative.instCommGroup
    have hwCU : w ∈ C ⊔ U := hcompl.sup_eq_top.symm ▸ Subgroup.mem_top w
    obtain ⟨c, hc, v, hv, rfl⟩ := Subgroup.mem_sup.mp hwCU
    have hcs : s • c = c := hCfix hc s
    have hsv : s • v ∈ U := (IsInvariant.invariant (A := S) (H := U) s v).mp hv
    have he : (c * v)⁻¹ * (s • (c * v)) = v⁻¹ * (s • v) := by
      rw [smul_mul', hcs]
      group
    rw [he]
    exact U.mul_mem (U.inv_mem hv) hsv
  exact (inv_mul_eq_one.mp (hcompl.disjoint.le_bot ⟨hdeltaC, hdeltaU⟩)).symm

end Stellmacher.SectionOne
