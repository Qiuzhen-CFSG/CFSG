module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointJoinResidual
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.MiddleResidual

/-!
# The actual binary-five source join is not the middle 1|3|1 flag

The original Φ(Q) inclusion makes the literal quotient core q(Q) abelian.
The actual restricted Sylow join has B as its two-residual. Transporting
that identity into any binary-five model contradicts the explicit middle
flag's nonabelian residual moving core. Adjacent flags remain possible.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original Φ(Q) kernel inclusion makes the actual image commutator
core abelian, while allowing that core itself to remain nontrivial. -/
theorem binary_three_source_binary_image_core_abelian
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n=4 ∨ n=5) (hm : ClassicalGroup.IsPSL K n 2) :
    let C := centralizer ({z} : Set G)
    let B := (c.L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))
    ⁅LinearThree.commutatorCore B,LinearThree.commutatorCore B⁆ = ⊥ := by
  let C := centralizer ({z} : Set G)
  let A := c.L.subgroupOf C
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := A.map q
  let Q := LinearThree.commutatorCore c.L
  let Q₀ := LinearThree.commutatorCore A
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hmapQ : Q₀.map C.subtype = Q := by
    simp only [Q₀,Q,A,LinearThree.commutatorCore,map_commutator,
      map_pCoreIn_of_injective 2 _ _ C.subtype_injective,map_subgroupOf_eq_of_le hLC]
  have hphi := binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
  have hroot : _root_.commutator Q = frattini Q :=
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.2.1
  have hderived : ⁅Q,Q⁆ ≤ C.pCoreIn 2 := by
    change (frattini Q).map Q.subtype ≤ C.pCoreIn 2 at hphi
    rw [←hroot] at hphi
    simpa only [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hphi
  have hcore : ⁅Q₀,Q₀⁆ ≤ pCore 2 C := by
    apply (map_le_map_iff_of_injective C.subtype_injective).mp
    change ⁅Q,Q⁆ ≤ (pCore 2 C).map C.subtype at hderived
    simpa only [map_commutator,hmapQ] using hderived
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hQimage : Q₀.map q = LinearThree.commutatorCore B := by
    simp only [Q₀,B,LinearThree.commutatorCore,map_commutator,map_pCoreIn_of_ker_isPGroup q hq]
  have hkill : (⁅Q₀,Q₀⁆).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hcore
  simpa only [map_commutator,hQimage] using hkill

/-- The full source supplies the actual restricted Sylow; its join with B
cannot be the 1|3|1 flag in any binary-five coordinates. -/
theorem binary_three_source_five_join_not_middle
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 5 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
    ∃ T : Sylow 2 K, (T : Subgroup K) = (S : Subgroup (C ⧸ pCore 2 C)).subgroupOf K ∧
      ∀ (a : K ≃* BinaryLinear.OuterCyclic.LinearGroup 5) (v : BinaryLinear.InvariantNodeActions.Basis 4),
        (B.subgroupOf K).map a.toMonoidHom ⊔
          (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) ≠
        BinaryLinear.InvariantNodeActions.cutStabilizer v ({0,3} : Set (Fin 4)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let D := B.subgroupOf K
  obtain ⟨_,T,hT,hres⟩ := binary_three_point_join_residual d c.L b z hLS P hP K hBK
  have hzero : ⁅LinearThree.commutatorCore B,LinearThree.commutatorCore B⁆ = ⊥ :=
    binary_three_source_binary_image_core_abelian
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inr rfl) hm
  have hDmap : D.map K.subtype = B := map_subgroupOf_eq_of_le hBK
  have hzeroD : ⁅⁅D.pCoreIn 2,D⁆,⁅D.pCoreIn 2,D⁆⁆ = ⊥ := by
    apply map_injective K.subtype_injective
    simpa only [map_commutator,map_pCoreIn_of_injective 2 D _ K.subtype_injective,
      hDmap,Subgroup.map_bot,LinearThree.commutatorCore] using hzero
  refine ⟨T,hT,?_⟩
  intro a v hflag
  let J₀ := D ⊔ (T : Subgroup K)
  let E := D.map a.toMonoidHom
  have hJ : J₀.map a.toMonoidHom = BinaryLinear.InvariantNodeActions.cutStabilizer v ({0,3} : Set (Fin 4)) := by
    rw [Subgroup.map_sup]
    exact hflag
  have hresmap :
      (pResidual 2 (BinaryLinear.InvariantNodeActions.cutStabilizer v ({0,3} : Set (Fin 4)))).map
        (BinaryLinear.InvariantNodeActions.cutStabilizer v ({0,3} : Set (Fin 4))).subtype = E := by
    have hh := congrArg (Subgroup.map a.toMonoidHom) hres
    rw [map_embedded_pResidual,hJ] at hh
    exact hh
  have hzeroE : ⁅⁅E.pCoreIn 2,E⁆,⁅E.pCoreIn 2,E⁆⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map a.toMonoidHom) hzeroD
    simpa only [map_commutator,map_pCoreIn_of_injective 2 D a.toMonoidHom a.injective,Subgroup.map_bot] using hh
  have hn := BinaryLinear.SevenFlagCore.middle_flag_residual_moving_core_nonabelian v
  dsimp only at hn
  rw [hresmap] at hn
  exact hn hzeroE

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
