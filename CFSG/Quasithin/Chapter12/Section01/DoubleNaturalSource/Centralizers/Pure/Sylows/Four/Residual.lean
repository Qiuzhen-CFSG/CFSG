module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Identification
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions

/-!
# The literal residual and its local MS clauses

The action of L_w=O²(C_L(w)) maps onto the pure stabilizer with a two-group
kernel. Passing to the actual two-core quotients identifies L_w/O₂(L_w)
with PSL_(n−1)(2). The marked T₁ is Sylow in L_wT₁. Characteristic two
passes from C_M(w), and the involution centralizer supplies SQTK. Relative
component normality and the proper Sylow give the product and MS2(a).

No ambient Sylow conclusion or MS classification is used. `MSPair` supplies
MS3 from the contrary ambient enlargement, and applies the exact binary
C.1.34 input. Source: Aschbacher--Smith 12.1.4 and H.9.1(3), printed
pp.790,389--390. Final assembly: `qt-d-double-natural-pure-fusion`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
theorem pureResidual_quotient_projective
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    Nonempty ((B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) := by
  let u : S.setup.natural := ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩
  let X := B.pointResidual w
  let f : X →* S.setup.stabilizer (Additive.ofMul w) :=
    (S.pureLocalAction w).comp (inclusion
      (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)))
  have hf : Function.Surjective f := by
    intro a
    have ha : a.val ∈ S.setup.residual (Additive.ofMul w) :=
      (S.setup.pure_stabilizer_eq_residual u hw).1 ▸ a.property
    rw [← S.pointResidual_image w] at ha
    obtain ⟨l,hl,he⟩ := ha
    exact ⟨⟨l,mem_map_of_mem _ hl⟩,Subtype.ext he⟩
  have hk : IsPGroup 2 f.ker := by
    let j : X →* L := inclusion ((B.pointResidual_le w).trans inf_le_left)
    have hj : f.ker ≤ (pCore 2 L).comap j := by
      intro x hx
      change j x ∈ pCore 2 L
      rw [← B.componentToActionQuotient_ker]
      exact congrArg Subtype.val (show f x = 1 from hx)
    exact (pCore_isPGroup.comap_of_injective j
      (inclusion_injective ((B.pointResidual_le w).trans inf_le_left))).to_le hj
  obtain ⟨e⟩ := S.setup.pure_quotient_projective u hw
  exact ⟨(f.pCoreQuotientEquiv hf hk).trans e⟩

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem doubleNatural_pure_residual_join_clauses_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      let X := B.pointResidual w
      let R := B.pointSylow w
      IsSQTK KnownSimple.IsKnownSimple (X ⊔ R : Subgroup G) ∧
        generalizedFitting (X ⊔ R : Subgroup G) = pCore 2 (X ⊔ R : Subgroup G) ∧
        (X.subgroupOf (X ⊔ R)).IsCComponent ∧ (X.subgroupOf (X ⊔ R)).Normal ∧
        Chapter1.IsSylowIn 2 R (X ⊔ R) ∧ MSOddIndex X R ∧
        (∀ g ∈ X ⊔ R, ∃ x ∈ X, ∃ r ∈ R, x*r=g) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix X R
  let C := B.localPointCentralizer w
  let J := X ⊔ R
  have hXC : X ≤ C := le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)
  have hRC : R ≤ C := inf_le_inf D.sylow_normalizes_component le_rfl
  have hJC : J ≤ C := sup_le hXC hRC
  have hs : Chapter1.IsSylowIn 2 R C :=
    D.doubleNatural_relative_pure_sylow_of_many h hmany B S w hw hp hfix
  obtain ⟨P,hP⟩ := hs
  have hRJ : Chapter1.IsSylowIn 2 R J := (show Chapter1.IsSylowIn 2 R C from ⟨P,hP⟩).restrict le_sup_right hJC
  have hc : HasCharacteristicTwo C := by
    have hh := D.doubleNatural_pure_local_characteristicTwo_of_many h hmany B w hw
    exact hh.of_equiv ((MulEquiv.subgroupCongr
      (inf_subgroupOf_right (normalizer (L : Set G)) (B.pointCentralizer w))).symm.trans
      (subgroupOfEquivOfLe (H := C) inf_le_right))
  have hPC : (P : Subgroup C) ≤ J.subgroupOf C := by
    intro p hp
    apply (show R ≤ J from le_sup_right)
    rw [← hP]
    exact mem_map_of_mem C.subtype hp
  have hf : generalizedFitting J = pCore 2 J :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hJC)).mp
        (centralizer_pCore_le_of_sylow_le P (J.subgroupOf C) hPC hc))
  have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
    (fun he => hw (Subtype.ext he))
  have hJH : J ≤ B.pointCentralizer w := hJC.trans inf_le_right
  have hsq := (h.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hw2)).subgroup
    (J.subgroupOf (B.pointCentralizer w))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp hsq
  have hnormal : (X.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (hJC.trans (B.localPointCentralizer_normalizes_residual w))
  have hcomponent : (X.subgroupOf J).IsCComponent :=
    (S.pureResidual_local_component w hw hp).subgroupOf_of_le le_sup_left hJC
  have hproper : R < J := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro he
    have hpX : IsPGroup 2 X := (Chapter1.isSylowIn_iff.mp hRJ).1.to_le (by
      rw [he]
      exact le_sup_left)
    exact Chapter1.mem_L_not_isSolvable
      (D.doubleNatural_pure_local_family_of_many h hmany B S w hw hp hfix).1
      (by let := hpX.isNilpotent; infer_instance)
  refine ⟨hsqJ,hf,hcomponent,hnormal,hRJ,sylow_msOddIndex hRJ hproper,?_⟩
  let := hnormal
  intro g hg
  have hmem : (⟨g,hg⟩ : J) ∈ X.subgroupOf J ⊔ R.subgroupOf J := by
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    trivial
  obtain ⟨x,hx,r,hr,he⟩ := mem_sup_of_normal_left.mp hmem
  exact ⟨x,hx,r,hr,congrArg Subtype.val he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
