module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Flag
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.Fitting.TwoCorePreimage

/-!
# Radical containment from the actual quotient action

For a normal subgroup K with centerless radical quotient and a solvable
ambient quotient J/K, the kernel of the literal action on K/O∞(K) is
solvable. Indeed its intersection with K embeds in O∞(K), and its quotient
embeds in J/K. If the image of A has no normalized nontrivial two-subgroup,
every A-normalized two-subgroup of J lies in this kernel and hence in O∞(J).

The source application uses J = KT and A = L₁. Its quotient J/K is a
two-group because the original Sylow group supplements K. All subgroup
inclusions and quotient actions are retained; K is only relatively normal.
The prime-PSL₂ signalizer calculation remains an explicit model premise.
Source: Aschbacher--Smith, 11.4.1(3), printed p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {J : Type*} [Group J] [Finite J]

/-- The literal radical quotient is centerless, independently of recognition. -/
theorem radical_quotient_center_eq_bot (K : Type*) [Group K] [Finite K] :
    center (K ⧸ solvableRadical K) = ⊥ := by
  let : Group.IsSolvable (center (K ⧸ solvableRadical K)) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  apply bot_unique
  exact (le_solvableRadical _ inferInstance inferInstance).trans_eq
    solvableRadical_quotient_solvableRadical

/-- The kernel is solvable for the literal radical-quotient action. -/
theorem radical_action_kernel_le (K : Subgroup J) [K.Normal]
    (hZ : center (K ⧸ solvableRadical K) = ⊥) [Group.IsSolvable (J ⧸ K)] :
    (normalQuotientAction K (solvableRadical K)).ker ≤ solvableRadical J := by
  let α := normalQuotientAction K (solvableRadical K)
  let C := α.ker
  let q := (QuotientGroup.mk' K).comp C.subtype
  have hinner (x : q.ker) : (⟨(x.val : J),
      (QuotientGroup.eq_one_iff _).mp x.property⟩ : K) ∈ solvableRadical K := by
    let k : K := ⟨(x.val : J), (QuotientGroup.eq_one_iff _).mp x.property⟩
    apply (QuotientGroup.eq_one_iff k).mp
    apply conj_injective_of_center_eq_bot hZ
    rw [map_one]
    change MulAut.conj (QuotientGroup.mk' (solvableRadical K) k) = 1
    rw [← normalQuotientAction_inner K (solvableRadical K) k]
    exact x.val.property
  let j : q.ker →* solvableRadical K :=
    { toFun := fun x => ⟨⟨(x.val : J), (QuotientGroup.eq_one_iff _).mp x.property⟩,
        hinner x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun r : solvableRadical K => (r.val : J)) h))
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (f := j) hj
  have hC : Group.IsSolvable C := Group.isSolvable_of_ker_le_range q.ker.subtype q (by simp)
  exact le_solvableRadical C inferInstance hC

/-- A nontrivial perfect actor has nontrivial image under the literal action. -/
theorem radical_action_image_ne_bot (K A : Subgroup J) [K.Normal]
    [Group.IsSolvable (J ⧸ K)] [Group.IsPerfect A] (hA : A ≠ ⊥) :
    A.map (normalQuotientAction K (solvableRadical K)) ≠ ⊥ := by
  intro he
  have hAR := ((map_eq_bot_iff A).mp he).trans
    (radical_action_kernel_le K (radical_quotient_center_eq_bot K))
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hA
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hAR) (inclusion_injective hAR)
  exact Group.IsPerfect.not_isSolvable A inferInstance

/-- Vanishing of the actual normalized image puts a two-subgroup in the radical. -/
theorem two_subgroup_le_radical_of_signalizers (K A R : Subgroup J) [K.Normal]
    (hZ : center (K ⧸ solvableRadical K) = ⊥) [Group.IsSolvable (J ⧸ K)]
    (hR : IsPGroup 2 R) (hn : A ≤ normalizer (R : Set J))
    (hsig : ∀ U : Subgroup (MulAut (K ⧸ solvableRadical K)), IsPGroup 2 U →
      A.map (normalQuotientAction K (solvableRadical K)) ≤ normalizer (U : Set _) → U = ⊥) :
    R ≤ solvableRadical J := by
  let α := normalQuotientAction K (solvableRadical K)
  have he : R.map α = ⊥ := hsig _ (hR.map α)
    ((map_mono hn).trans (R.le_normalizer_map α))
  exact ((map_eq_bot_iff R).mp he).trans (radical_action_kernel_le K hZ)

variable {G : Type*} [Group G] [Finite G]

/-- Source application on KT, with its genuine normal component and Sylow quotient. -/
theorem local_core_le_radical_of_signalizers (T : Sylow 2 G) (A K : Subgroup G)
    (hAK : A ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    let J := K ⊔ (T : Subgroup G)
    let B := K.subgroupOf J
    let _ : B.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le K.le_normalizer hTK)
    center (B ⧸ solvableRadical B) = ⊥ →
    (∀ U : Subgroup (MulAut (B ⧸ solvableRadical B)), IsPGroup 2 U →
      (A.subgroupOf J).map (normalQuotientAction B (solvableRadical B)) ≤
        normalizer (U : Set _) → U = ⊥) →
    (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (solvableRadical J).map J.subtype := by
  dsimp only
  intro hZ hsig
  let J := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf J
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hTK)
  have hquot : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype (by
      rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right), subgroupOf_self])
  let : Group.IsNilpotent (J ⧸ B) := hquot.isNilpotent
  let R := (A ⊔ (T : Subgroup G)).pCoreIn 2
  have hRJ : R ≤ J := (pCoreIn_le 2 _).trans (sup_le_sup_right hAK _)
  have hn : A ≤ normalizer (R : Set G) :=
    le_sup_left.trans ((A ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hn' : A.subgroupOf J ≤ normalizer (R.subgroupOf J : Set J) := by
    intro a ha r
    exact hn ha r
  have hh := two_subgroup_le_radical_of_signalizers B (A.subgroupOf J)
    (R.subgroupOf J) hZ (isPGroup_pCoreIn 2 _).comap_subtype hn' hsig
  simpa only [map_subgroupOf_eq_of_le hRJ] using map_mono (f := J.subtype) hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
