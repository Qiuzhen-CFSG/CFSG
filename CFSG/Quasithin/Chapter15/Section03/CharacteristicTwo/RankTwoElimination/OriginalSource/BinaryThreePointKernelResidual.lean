module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiKernel
public import Theory.Representation.PSL3Two.SingerRestriction
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The literal binary point-kernel residual

The original Frattini layer lies in the point kernel and is fully moved by
L. A Singer element is fixed-point-free on both marked pair sections above
it. Restricting its displacement to actual subgroup images proves that
Q intersect O₂(C) is fully moved by L. Full Sylow placement then identifies
this intersection with [O₂(C),L]. No unique-head or ambient invariance
assumption is used.

Source: the marked MS93(4.5) sections, printed p.895, and the original
point/full-Sylow setup of Aschbacher--Smith 15.3.58.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem section_subgroup_movement
    {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {L D E T : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    (hs : HasSectionModel L D E a σ)
    (t : L) (hf : ∀ v, σ (a t) v = v → v = 0)
    (hTD : T ≤ D) (hLT : L ≤ normalizer T) : T = ⁅T,L⁆ ⊔ (T ⊓ E) := by
  obtain ⟨hED,hLD,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf D))
  have hk : p.ker = E.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let U := (T.subgroupOf D).map p
  let α : U →* U := {
    toFun v := ⟨Multiplicative.ofAdd (σ (a t) v.val.toAdd), by
      obtain ⟨x,hx,hv⟩ := v.property
      let y := D.normalizerMonoidHom (inclusion hLD t) x
      have hyT : (y : G) ∈ T := (mem_normalizer_iff.mp (hLT t.property) x).mp hx
      refine ⟨y,hyT,?_⟩
      apply Multiplicative.toAdd.injective
      have hh := he t x y rfl
      change (p y).toAdd = σ (a t) (p x).toAdd at hh
      rw [hh,hv]
      rfl⟩
    map_one' := Subtype.ext (by change Multiplicative.ofAdd (σ (a t) 0) = 1; rw [map_zero]; rfl)
    map_mul' x y := Subtype.ext (by exact congrArg Multiplicative.ofAdd (map_add (σ (a t)) _ _)) }
  have hfree : MonoidHom.FixedPointFree α := by
    intro v hv
    apply Subtype.ext
    exact Multiplicative.toAdd.injective (hf v.val.toAdd (congrArg (fun x : U => x.val.toAdd) hv))
  have hTL : ⁅T,L⁆ ≤ T := le_normalizer_iff_commutator_le_left.mp hLT
  apply le_antisymm ?_ (sup_le hTL inf_le_left)
  intro x hx
  let xD : D := ⟨x,hTD hx⟩
  let xU : U := ⟨p xD,mem_map_of_mem p hx⟩
  obtain ⟨y,hy⟩ := hfree.commutatorMap_surjective xU
  obtain ⟨z,hz,hzy⟩ := y.property
  let zt := D.normalizerMonoidHom (inclusion hLD t) z
  have hzt : (zt : G) ∈ T := (mem_normalizer_iff.mp (hLT t.property) z).mp hz
  have heq : p z / p zt = p xD := by
    have hh := congrArg (fun v : U => v.val.toAdd) hy
    have hez := he t z zt rfl
    change (p zt).toAdd = σ (a t) (p z).toAdd at hez
    apply Multiplicative.toAdd.injective
    change (p z).toAdd - (p zt).toAdd = (p xD).toAdd
    rw [hez,hzy]
    exact hh
  let w := z / zt
  have hw : (w : G) ∈ ⁅T,L⁆ := by
    have hwc : (w : G) = ⁅(z : G),(t : G)⁆ := by
      change (z : G) / ((t : G) * (z : G) * (t : G)⁻¹) = ⁅(z : G),(t : G)⁆
      simp only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv]
      group
    rw [hwc]
    exact commutator_mem_commutator hz t.property
  have hwT : (w : G) ∈ T := hTL hw
  have hxw : (xD / w : D) ∈ p.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_div,show p w = p xD from (map_div p z zt).trans heq,div_self']
  rw [hk] at hxw
  have hxe : x / (w : G) ∈ T ⊓ E := ⟨T.div_mem hx hwT,hxw⟩
  have hh := (⁅T,L⁆ ⊔ (T ⊓ E)).mul_mem (mem_sup_right hxe) (mem_sup_left hw)
  simpa only [div_mul_cancel] using hh

open BinaryLinearThree Matrix.PSL3Two.OuterInvolutionSinger Representation.BinaryOffender

private theorem natural_singer_free (v : Vector) (hv : W singer v = v) : v = 0 := by
  have hm := (mem_fixedSpace_zpowers_iff W singer v).mpr hv
  rw [SingerRestriction.natural_fixedSpace_singer] at hm
  exact hm

private theorem dual_singer_free (v : Module.Dual (ZMod 2) Vector)
    (hv : W.dual singer v = v) : v = 0 := by
  have hd := fixedCodim_add_finrank W.dual (zpowers singer)
  rw [SingerDisplacement.fixedCodim_singer_dual] at hd
  have hdim : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Vector) = 3 := by
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  rw [hdim] at hd
  have hb : fixedSpace W.dual (zpowers singer) = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hm := (mem_fixedSpace_zpowers_iff W.dual singer v).mpr hv
  rw [hb] at hm
  exact hm

/-- The full original binary source identifies the actual point-kernel commutator with Q intersect N. -/
theorem binary_three_source_binary_kernel_residual
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
    let N := (centralizer ({z} : Set G)).pCoreIn 2
    let Q := LinearThree.commutatorCore c.L
    let R := Q ⊓ N
    ⁅N,c.L⁆ = R ∧ ⁅R,c.L⁆ = R := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let J := c.L ⊔ d.S
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let R := Q ⊓ N
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hLN : c.L ≤ normalizer N := hLC.trans hCN
  have hLQ : c.L ≤ normalizer Q := c.L.le_normalizer.trans
    (normalizer_le_normalizer_commutatorCore c.L)
  have hLR : c.L ≤ normalizer R :=
    (le_inf hLQ hLN).trans inf_normalizer_le_normalizer_inf
  have hPhiN : Phi ≤ N := binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
  have hPhiR : Phi ≤ R := le_inf (map_subtype_le (frattini Q)) hPhiN
  have hroot : _root_.commutator Q = frattini Q :=
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.2.1
  have hPhi : Phi = ⁅Q,Q⁆ := by
    dsimp only [Phi,frattiniIn]
    rw [←hroot,_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  have hPhiMove : ⁅Phi,c.L⁆ = Phi := by
    rw [hPhi]
    exact binary_three_large_distance_original_derived_full_commutation
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  obtain ⟨a,_,hd,ht⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  obtain ⟨s,hs⟩ := (a.surjective.comp (QuotientGroup.mk'_surjective _)) singer
  change linearThreeActor a s = singer at hs
  let : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) := Module.finite_of_finite (ZMod 2)
  have hnatural : ∀ v, (W.prod W) (linearThreeActor a s) v = v → v = 0 := by
    intro v hv
    rw [hs] at hv
    exact Prod.ext (natural_singer_free v.1 (congrArg Prod.fst hv))
      (natural_singer_free v.2 (congrArg Prod.snd hv))
  have hdual : ∀ v, (W.dual.prod W.dual) (linearThreeActor a s) v = v → v = 0 := by
    intro v hv
    rw [hs] at hv
    exact Prod.ext (dual_singer_free v.1 (congrArg Prod.fst hv))
      (dual_singer_free v.2 (congrArg Prod.snd hv))
  have hRD : R ⊓ D = ⁅R ⊓ D,c.L⁆ ⊔ ((R ⊓ D) ⊓ Phi) :=
    section_subgroup_movement hd s hdual inf_le_right
      ((le_inf hLR hd.2.1).trans inf_normalizer_le_normalizer_inf)
  have hR : R = ⁅R,c.L⁆ ⊔ (R ⊓ D) := section_subgroup_movement ht s hnatural inf_le_left hLR
  have hPhiMoved : Phi ≤ ⁅R,c.L⁆ := hPhiMove.symm.le.trans (commutator_mono hPhiR le_rfl)
  have hRDle : R ⊓ D ≤ ⁅R,c.L⁆ := by
    rw [hRD]
    exact sup_le (commutator_mono inf_le_left le_rfl) (inf_le_right.trans hPhiMoved)
  have hRMove : ⁅R,c.L⁆ = R := le_antisymm
    (le_normalizer_iff_commutator_le_left.mp hLR) (hR.le.trans (sup_le le_rfl hRDle))
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hNJ : N ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 C) (hNS.trans le_sup_right) (hLS.trans hCN)
  have hJL : J ≤ normalizer c.L :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hNLQ : ⁅N,c.L⁆ ≤ Q := (commutator_mono hNJ le_rfl).trans
    (overgroup_core_commutator_eq d c (le_sup_right.trans hJL)).le
  have hNL : ⁅N,c.L⁆ = R := le_antisymm
    (le_inf hNLQ (le_normalizer_iff_commutator_le_left.mp hLN))
    (hRMove.symm.le.trans (commutator_mono inf_le_right le_rfl))
  exact ⟨hNL,hRMove⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
