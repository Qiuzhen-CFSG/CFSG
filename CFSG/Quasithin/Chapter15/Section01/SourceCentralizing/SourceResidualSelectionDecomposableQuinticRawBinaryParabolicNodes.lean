module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryParabolicCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryInnerPlacement
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinarySourceParabolics

/-! Literal full preimages of the native binary nodes have characteristic
two, actual S3 core quotients, and no A3-product two-residual. Every node
uses one fixed quotient marking and basis, and the original full preimages
generate the entire component. The import-all edge reuses only the
record-free residual-exponent obstruction. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.RawBinaryParabolic
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
open BinaryLinear.OrderedResidualConjugators
variable {G : Type*} [Group G] [Finite G]
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

omit [Finite G] in
private theorem lift_eq (L : Subgroup G) {m : ℕ}
    (e : (L ⧸ pCore 2 L) ≃* SL(m+1,ZMod 2)) (A : Subgroup (LinearGroup (m+1))) :
    EquivariantLift.lift L (coreFlagMap L e) A =
      (A.comap (coreFlagMap L e)).map L.subtype := by
  let q := coreFlagMap L e
  let P := A.comap q
  let D := P.map L.subtype
  have hD : D.subgroupOf L = P := comap_map_eq_self_of_injective L.subtype_injective _
  have him : (D.subgroupOf L).map q = A := by
    rw [hD]
    exact map_comap_eq_self (by rw [q.range_eq_top_of_surjective (coreFlagMap_surjective L e)]; exact le_top)
  have he := EquivariantLift.lift_map_subgroupOf L q D (map_subtype_le _)
    (by rw [hD]; exact ker_le_comap _ _)
  rwa [him] at he

omit [Finite G] in
private theorem lift_cover (L : Subgroup G) {m : ℕ}
    (e : (L ⧸ pCore 2 L) ≃* SL(m+1,ZMod 2)) (A : Subgroup (LinearGroup (m+1))) :
    ∃ f : EquivariantLift.lift L (coreFlagMap L e) A →* A,
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let q := coreFlagMap L e
  let D := EquivariantLift.lift L q A
  let P := D.subgroupOf L
  have him : P.map q = A := coreFlagMap_lift_image L e A
  let t : P ≃* D := subgroupOfEquivOfLe (EquivariantLift.lift_le L q A)
  let f : D →* A := ((MulEquiv.subgroupCongr him).toMonoidHom.comp
    (q.subgroupMap P)).comp t.symm.toMonoidHom
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr him).surjective.comp
    ((q.subgroupMap_surjective P).comp t.symm.surjective)
  refine ⟨f,hf,?_⟩
  have hk : f.ker = (q.ker.subgroupOf P).comap t.symm.toMonoidHom := by
    ext x
    change (⟨q (t.symm x : L),_⟩ : A) = 1 ↔ q (t.symm x : L) = 1
    exact Subtype.ext_iff
  rw [hk,show q.ker = pCore 2 L from coreFlagMap_ker L e]
  exact pCore_isPGroup.comap_subtype.comap_of_injective _ t.symm.injective

private theorem lift_fitting (L : Subgroup G) {m : ℕ}
    (e : (L ⧸ pCore 2 L) ≃* SL(m+1,ZMod 2)) (hf : generalizedFitting L = pCore 2 L)
    (A : Subgroup (LinearGroup (m+1))) :
    generalizedFitting (EquivariantLift.lift L (coreFlagMap L e) A) =
      pCore 2 (EquivariantLift.lift L (coreFlagMap L e) A) := by
  let P := A.comap (coreFlagMap L e)
  let t := (P.equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr (lift_eq L e A).symm)
  have hcore : pCore 2 L ≤ P := by
    rw [←coreFlagMap_ker L e]
    exact ker_le_comap _ _
  have hP := generalizedFitting_eq_pCore_of_normalized_by_pCore P hf (hcore.trans P.le_normalizer)
  rw [←map_generalizedFitting_equiv t,←pCore_map_iso 2 t,hP]

/-- Each marked native node has the intrinsic source-parabolic data, with
the entire original two-core retained. -/
theorem node_data (L : Subgroup G) (Q : Sylow 2 L)
    (hf : generalizedFitting L = pCore 2 L) {m : ℕ} (hm : 3 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* SL(m+1,ZMod 2)) (b : Basis m)
    (hb : (Q : Subgroup L).map (coreFlagMap L e) = cutStabilizer b Set.univ) (i : Fin m) :
    let P := EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b i)
    generalizedFitting P = pCore 2 P ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      ¬CaseIComponentData.IsAThreeProduct P := by
  let P := EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b i)
  let U := Q.mapSurjective (coreFlagMap_surjective L e)
  obtain ⟨f,hfs,hfk⟩ := lift_cover L e (minimalParabolic b i)
  obtain ⟨eqN⟩ := BinaryLinear.InvariantNodeActions.node_quotient U b hb i
  refine ⟨lift_fitting L e hf _,⟨(f.pCoreQuotientEquiv hfs hfk).trans eqN⟩,?_⟩
  by_cases he : i.val=0 ∨ i.val=m-1
  · obtain ⟨_,h16⟩ := BinaryLinear.InvariantNodeActions.endpoint_node_data hm U b hb i he
    have h9 : ¬9 ∣ Nat.card P := by
      have hc : Nat.card P = Nat.card f.ker * Nat.card (minimalParabolic b i) := by
        rw [←f.ker.card_mul_index,index_ker,f.range_eq_top_of_surjective hfs,card_top]
      obtain ⟨r,hr⟩ := hfk.exists_card_eq
      rw [hc,hr]
      intro hd
      exact node_card_not_nine b i (((by decide : Nat.Coprime 9 2).pow_right r).dvd_of_dvd_mul_left hd)
    have hle : Nat.card (pResidual 2 (minimalParabolic b i)) ≤ Nat.card (pResidual 2 P) := by
      rw [←map_pResidual_of_surjective 2 f hfs]
      exact Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective _)
    intro hA
    have h12 := CaseIComponentData.aThreeProduct_residual_card_le P h9 hA
    omega
  · exact CaseIComponentData.not_aThreeProduct_of_residual_image P f hfs
      (interior_node_residual_not_exponent_six b i (by omega) (by omega))

omit [Finite G] in
/-- All literal node preimages generate L, including the original two-core. -/
theorem nodes_generate (L : Subgroup G) {m : ℕ} (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* SL(m+1,ZMod 2)) (b : Basis m) :
    (⨆ i : Fin m, EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b i)) = L := by
  let N := fun i : Fin m => EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b i)
  let D := ⨆ i : Fin m, N i
  let q := coreFlagMap L e
  have hDL : D ≤ L := iSup_le (fun i => EquivariantLift.lift_le L q _)
  have him : (D.subgroupOf L).map q = ⊤ := by
    apply top_unique
    rw [←iSup_minimalParabolic_eq_top hm b]
    apply iSup_le
    intro i
    rw [←coreFlagMap_lift_image L e (minimalParabolic b i)]
    exact map_mono (subgroupOf_mono L (le_iSup N i))
  have hk : q.ker ≤ D.subgroupOf L := by
    let i : Fin m := ⟨0,hm⟩
    have hzero : ((q.ker.map L.subtype).subgroupOf L).map q = ⊥ := by
      rw [show (q.ker.map L.subtype).subgroupOf L = q.ker from
        comap_map_eq_self_of_injective L.subtype_injective _]
      exact (map_eq_bot_iff q.ker).mpr le_rfl
    have hkn : q.ker.map L.subtype ≤ N i :=
      EquivariantLift.le_lift L q (map_subtype_le _) (by rw [hzero]; exact bot_le)
    intro x hx
    exact (le_iSup N i) (hkn (mem_map_of_mem L.subtype hx))
  have he := EquivariantLift.lift_map_subgroupOf L q D hDL hk
  rw [him,EquivariantLift.lift_top] at he
  exact he.symm

end CFSG.Quasithin.Chapter15.Section01.RawBinaryParabolic
