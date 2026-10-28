module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingCore
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Core
public import Theory.Representation.BinaryAlternatingFiveExtension.Borel

/-!
# The literal point centralizer in a paired alternating-five block

A central point of the source Sylow subgroup splits into its module and
block-centralizer coordinates. The Baumann action and the actual inner
Sylow exchange force its nonzero module coordinate to be (1,1,1,1,0).
Its centralizer in the original block is therefore the inverse image of
the stabilizer of the fifth point. The noncommuting source conjugator
identifies the whole two-core with the module, so the natural extension
splitting theorem supplies the actual A₄ Borel model.

Source: Aschbacher--Smith, C.5.6 and the proof of 14.6.9,
printed pp.1025--1026 (refs/quasithin.pdf).
-/

public section
open Subgroup BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

private theorem marked_fixed_line (v : core (Fin 5))
    (h0 : coreRepresentation (Fin 5) (ChapterB.Offenders.pairSwap 5 0) v = v)
    (h1 : coreRepresentation (Fin 5) (ChapterB.Offenders.pairSwap 5 1) v = v)
    (he : coreRepresentation (Fin 5) pairExchange v = v) :
    v = 0 ∨ v = AlternatingFiveBorel.fixedVector := by
  have h01 := congrArg (fun w : core (Fin 5) => w.val 0) h0
  have h23 := congrArg (fun w : core (Fin 5) => w.val 2) h1
  have h02 := congrArg (fun w : core (Fin 5) => w.val 0) he
  change v.val 1 = v.val 0 at h01
  change v.val 3 = v.val 2 at h23
  change v.val 2 = v.val 0 at h02
  have hz : v.val 4 = 0 := by
    have hv := v.property
    change (∑ i : Fin 5, v.val i) = 0 at hv
    simpa [Fin.sum_univ_succ,h01,h23,h02,←add_assoc,show ∀ a : ZMod 2, a+a=0 from by decide +kernel] using hv
  have ha : v.val 0 = 0 ∨ v.val 0 = 1 :=
    (by decide +kernel : ∀ a : ZMod 2, a = 0 ∨ a = 1) _
  rcases ha with ha | ha
  · left
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [h01,h23,h02,hz,ha]
  · right
    apply Subtype.ext
    rw [AlternatingFiveBorel.fixedVector_coordinates]
    funext i
    fin_cases i <;> simp [h01,h23,h02,hz,ha]

private theorem marked_fixed_stabilizer (a : FivePerm) :
    coreRepresentation (Fin 5) a AlternatingFiveBorel.fixedVector =
      AlternatingFiveBorel.fixedVector ↔ a 4 = 4 := by
  rw [Subtype.ext_iff]
  change representation (Fin 5) a AlternatingFiveBorel.fixedVector.val =
    AlternatingFiveBorel.fixedVector.val ↔ _
  rw [AlternatingFiveBorel.fixedVector_coordinates]
  have hh : ∀ a : FivePerm,
      representation (Fin 5) a ![1,1,1,1,0] = ![1,1,1,1,0] ↔ a 4 = 4 := by
    simp only [funext_iff,representation_apply]
    decide +kernel
  exact hh a

/-- The actual central point has the standard nonzero fixed-line coordinate
in either original alternating-five block, and its centralizer is literally
the point-stabilizer inverse image under the original block action. -/
theorem AlternatingPairSetup.central_point_marking
    (h : AlternatingPairSetup R K L) (z : G)
    (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (hout : ¬ K ≤ centralizer ({z} : Set G)) :
    ∃ v : sourceModule K,
      h.coordinates v = Multiplicative.ofAdd AlternatingFiveBorel.fixedVector ∧
      K ⊓ centralizer ({z} : Set G) =
        K ⊓ centralizer ({(v : G)} : Set G) ∧
      ∀ k : K, (k : G) ∈ centralizer ({z} : Set G) ↔
        h.action (inclusion le_sup_left k) 4 = 4 := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let C := S ⊓ centralizer (K : Set G)
  have hUS : U ≤ S := h.module_le
  have hSR : S ≤ R := inf_le_left
  have hzU : z ∈ centralizer (U : Set G) := (centralizer_le (hUS.trans hSR)) hzR
  have hzQ : z ∈ (K ⊔ S).pCoreIn 2 := h.core ▸ ⟨hzS,hzU⟩
  have hd := (BlockAnalysis.AlternatingSetup.source_product_direct R K h.block).1
  have hCU : C ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hzs : z ∈ U ⊔ C := h.product ▸ hzQ
  change z ∈ (↑(U ⊔ C) : Set G) at hzs
  rw [coe_mul_of_right_le_normalizer_left U C
    (hCU.trans (Subgroup.centralizer_le_normalizer _))] at hzs
  obtain ⟨v,hv,d,hdC,hz⟩ := hzs
  change v * d = z at hz
  have hSU : S ≤ normalizer (U : Set G) :=
    h.normalizes.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hSC : S ≤ normalizer (C : Set G) :=
    (le_inf S.le_normalizer
      (h.normalizes.trans (normalizer_le_normalizer_centralizer K))).trans
        inf_normalizer_le_normalizer_inf
  have hvS : v ∈ centralizer (S : Set G) := by
    intro s hs
    have he : (s*v*s⁻¹)*(s*d*s⁻¹) = v*d := by
      calc
        _ = s*(v*d)*s⁻¹ := by group
        _ = v*d := by rw [hz,hzR s (hSR hs),mul_inv_cancel_right,←hz]
    have hh : ((⟨s*v*s⁻¹,(hSU hs v).mp hv⟩,⟨s*d*s⁻¹,(hSC hs d).mp hdC⟩) : U × C) =
        (⟨v,hv⟩,⟨d,hdC⟩) := mul_injective_of_disjoint hd he
    have he' := congrArg (fun p : U × C => (p.1 : G)) hh
    exact mul_inv_eq_iff_eq_mul.mp he'
  have hvRK : v ∈ centralizer (R ⊓ K : Set G) := by
    intro k hk
    have he : k * (v*d) = (v*d)*k := by rw [hz]; exact hzR k hk.1
    have hdcomm := hdC.2 k hk.2
    apply mul_right_cancel (b := d)
    calc
      k*v*d = k*(v*d) := mul_assoc _ _ _
      _ = (v*d)*k := he
      _ = v*k*d := by rw [mul_assoc,←hdcomm,←mul_assoc]
  let vU : U := ⟨v,hv⟩
  have hfix (s : ↥(K ⊔ S)) (hs : s.val ∈ centralizer ({v} : Set G)) :
      coreRepresentation (Fin 5) (h.action s) (h.coordinates vU).toAdd =
        (h.coordinates vU).toAdd := by
    have he := h.equivariant s vU
    rw [(mem_centralizer_singleton_iff.mp hs),mul_inv_cancel_right] at he
    have he' : h.coordinates.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (h.action s) (h.coordinates vU).toAdd)) = vU :=
      Subtype.ext he
    exact congrArg Multiplicative.toAdd
      ((h.coordinates.apply_symm_apply _).symm.trans (congrArg h.coordinates he'))
  have hD (a : FivePerm) (ha : a ∈ ChapterB.Offenders.D 5) :
      coreRepresentation (Fin 5) a (h.coordinates vU).toAdd = (h.coordinates vU).toAdd := by
    rw [←h.baumann_image] at ha
    obtain ⟨s,hs,he⟩ := ha
    rw [←he]
    exact hfix s (mem_centralizer_singleton_iff.mpr (hvS s hs))
  have he : coreRepresentation (Fin 5) pairExchange (h.coordinates vU).toAdd =
      (h.coordinates vU).toAdd := by
    obtain ⟨s,hs,he⟩ := h.pairExchange_mem
    rw [←he]
    exact hfix s (mem_centralizer_singleton_iff.mpr (hvRK s hs))
  have hn : v ≠ 1 := by
    intro hv1
    have hzC : z ∈ centralizer (K : Set G) := by
      have he : d = z := by simpa only [hv1,one_mul] using hz
      exact he ▸ hdC.2
    exact hout (fun k hk => mem_centralizer_singleton_iff.mpr (hzC k hk))
  have hmark : (h.coordinates vU).toAdd = AlternatingFiveBorel.fixedVector := by
    rcases marked_fixed_line _
      (hD _ (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide)))
      (hD _ (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 1 (by decide))) he with he | he
    · have hv1 : vU = 1 := h.coordinates.injective
        ((congrArg Multiplicative.ofAdd he).trans h.coordinates.map_one.symm)
      exact (hn (congrArg Subtype.val hv1)).elim
    · exact he
  have hequiv (k : K) : (k : G) ∈ centralizer ({z} : Set G) ↔
      (k : G) ∈ centralizer ({v} : Set G) := by
    simp only [mem_centralizer_singleton_iff,←hz]
    have hdcomm := hdC.2 k k.property
    constructor
    · intro hk
      apply mul_right_cancel (b := d)
      calc
        (k:G)*v*d = (k:G)*(v*d) := mul_assoc _ _ _
        _ = (v*d)*k := hk
        _ = v*k*d := by rw [mul_assoc,←hdcomm,←mul_assoc]
    · intro hk
      calc
        (k:G)*(v*d) = ((k:G)*v)*d := (mul_assoc _ _ _).symm
        _ = (v*k)*d := by rw [hk]
        _ = (v*d)*k := by rw [mul_assoc,hdcomm,←mul_assoc]
  refine ⟨vU,congrArg Multiplicative.ofAdd hmark,?_,?_⟩
  · ext k
    constructor <;> rintro ⟨hk,hc⟩
    · exact ⟨hk,(hequiv ⟨k,hk⟩).mp hc⟩
    · exact ⟨hk,(hequiv ⟨k,hk⟩).mpr hc⟩
  · intro k
    rw [hequiv]
    constructor
    · intro hk
      exact (marked_fixed_stabilizer _).mp (by simpa only [hmark] using hfix (inclusion le_sup_left k) hk)
    · intro hk
      have he := h.equivariant (inclusion le_sup_left k) vU
      rw [hmark,(marked_fixed_stabilizer _).mpr hk] at he
      have hh : h.coordinates.symm (Multiplicative.ofAdd AlternatingFiveBorel.fixedVector) = vU := by
        apply h.coordinates.injective
        exact (h.coordinates.apply_symm_apply _).trans (congrArg Multiplicative.ofAdd hmark).symm
      rw [hh] at he
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he.symm)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup BinaryPermutation
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.central_point_borel
    (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (z : G) (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (hout : ¬ K ≤ centralizer ({z} : Set G)) :
    Nonempty ((K ⊓ centralizer ({z} : Set G) : Subgroup G) ≃*
      AlternatingFiveExtension.BorelModel) := by
  let q : K →* alternatingGroup (Fin 5) :=
    { toFun := fun k => ⟨h.action (inclusion le_sup_left k),by
        rw [←h.block_image]
        exact mem_map_of_mem h.action k.property⟩
      map_one' := Subtype.ext (h.action.map_one)
      map_mul' := fun k l => Subtype.ext (by
        exact h.action.map_mul (inclusion le_sup_left k) (inclusion le_sup_left l)) }
  have hq : Function.Surjective q := by
    intro a
    have ha : a.val ∈ (K.subgroupOf (K ⊔ ChapterB.baumann R)).map h.action :=
      h.block_image.symm ▸ a.property
    obtain ⟨k,hk,he⟩ := ha
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hcore := h.block_core_eq_module x hx hnc
  have hker : q.ker = blockU K := by
    ext k
    rw [←hcore,←h.block.2.1.centralizer_blockU]
    constructor
    · intro hk u hu
      have hk' : inclusion le_sup_left k ∈ h.action.ker :=
        congrArg Subtype.val hk
      rw [h.action_kernel] at hk'
      exact Subtype.ext (hk' u (mem_map_of_mem K.subtype hu))
    · intro hk
      apply Subtype.ext
      change inclusion le_sup_left k ∈ h.action.ker
      rw [h.action_kernel]
      rintro u ⟨v,hv,rfl⟩
      exact congrArg Subtype.val (hk v hv)
  let eu : q.ker ≃* sourceModule K := (MulEquiv.subgroupCongr hker).trans
    ((blockU K).equivMapOfInjective K.subtype K.subtype_injective)
  let e := eu.trans h.coordinates
  have he (k : K) (v : q.ker) : e (MulAut.conjNormal k v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q k).val (e v).toAdd) := by
    apply h.coordinates.symm.injective
    change h.coordinates.symm (h.coordinates (eu (MulAut.conjNormal k v))) =
      h.coordinates.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (h.action (inclusion le_sup_left k)) (h.coordinates (eu v)).toAdd))
    rw [h.coordinates.symm_apply_apply]
    apply Subtype.ext
    exact (h.equivariant (inclusion le_sup_left k) (eu v)).symm
  obtain ⟨_,_,_,hmark⟩ := h.central_point_marking z hzS hzR hout
  let B := (MulAction.stabilizer (alternatingGroup (Fin 5)) (4 : Fin 5)).comap q
  have hB : B = (centralizer ({z} : Set G)).subgroupOf K := by
    ext k
    exact (hmark k).symm
  obtain ⟨eb⟩ := AlternatingFiveExtension.borel_equiv q hq e he 4
  let ef : (centralizer ({z} : Set G)).subgroupOf K ≃*
      (K ⊓ centralizer ({z} : Set G) : Subgroup G) :=
    { toFun := fun k => ⟨k,⟨k.val.property,k.property⟩⟩
      invFun := fun k => ⟨⟨k,k.property.1⟩,k.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact ⟨ef.symm.trans ((MulEquiv.subgroupCongr hB.symm).trans eb)⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
