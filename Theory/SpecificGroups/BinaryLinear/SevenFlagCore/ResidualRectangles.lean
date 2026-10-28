module
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.ExactQuotientFlags
import all Theory.SpecificGroups.BinaryLinear.SevenFlagCore
import all Theory.SpecificGroups.BinaryLinear.SevenFlagCore.PerfectDerived
public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption.Elementary
public import Theory.SpecificGroups.BinaryLinear.RadicalCardinality
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Exact moving-core rectangles in the surviving binary flags

The residual of an adjacent flag omits its singleton scalar. Its moving
two-core is exactly the full rectangle adjoining the three-dimensional
block. Cubic root commutators prove the reverse inclusion, retaining the
literal residual and its intrinsic two-core. The endpoint calculation is
the one-row version. No orientation relative to an external PSL3 marking
is inferred from these coordinate statements.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement Classical
namespace BinaryLinear.SevenFlagCore
open OuterCyclic InvariantNodeActions SmallParabolicLevi CubicPairNormalizers.CoreAbsorption
variable {m : ℕ}

private noncomputable def flagResidual (c : Fin (m+1) → Fin (m+1)) : Subgroup (LinearGroup (m+1)) :=
  (pResidual 2 (triangularGroup c)).map (triangularGroup c).subtype

private theorem rectangle_root_matrix (r s : Fin (m+1)) (hrs : r≠s) (i j : Fin (m+1)) :
    matrix (root r s hrs 1) i j = (if i=j then 1 else 0)+(if i=r ∧ j=s then 1 else 0) := by
  rw [matrix_apply]
  by_cases hir : i=r <;> by_cases hjs : j=s <;>
    simp [standardBasis,root_apply,Pi.single_apply,hir,hjs,eq_comm]

private theorem rectangle_root_mem_flag (c : Fin (m+1) → Fin (m+1))
    (r s : Fin (m+1)) (hrs : r≠s) (hc : c r ≤ c s) : root r s hrs 1 ∈ triangularGroup c := by
  intro i j hji
  rw [rectangle_root_matrix]
  have hne : i≠j := fun he => by subst i; exact lt_irrefl _ hji
  have hn : ¬(i=r ∧ j=s) := by rintro ⟨rfl,rfl⟩; exact not_lt_of_ge hc hji
  simp [hne,hn]

private theorem rectangle_root_mem_flag_core (c : Fin (m+1) → Fin (m+1)) (hmono : Monotone c)
    (r s : Fin (m+1)) (hrs : r≠s) (hc : c r < c s) :
    root r s hrs 1 ∈ (triangularGroup c).pCoreIn 2 := by
  let g : triangularGroup c := ⟨root r s hrs 1,rectangle_root_mem_flag c r s hrs hc.le⟩
  refine ⟨g,?_,rfl⟩
  rw [←ker_diagonalAction_eq_twoCore c hmono]
  change diagonalAction c g=1
  funext k
  apply LinearEquiv.toLinearMap_injective
  have hb : blockMatrix c k g.val=1 := by
    ext i j
    change matrix (root r s hrs 1) i.val j.val = _
    rw [rectangle_root_matrix]
    have hn : ¬(i.val=r ∧ j.val=s) := by
      rintro ⟨hi,hj⟩
      have he := i.property.trans j.property.symm
      rw [hi,hj] at he
      exact (ne_of_lt hc) he
    simp [hn,Matrix.one_apply,Subtype.ext_iff]
  change Matrix.toLin' (blockMatrix c k g.val)=LinearMap.id
  rw [hb,Matrix.toLin'_one]

private theorem rectangle_cubic_mem_residual (c : Fin (m+1) → Fin (m+1))
    (r s : Fin (m+1)) (hrs : r≠s) (hc : c r=c s) : cubic r s hrs ∈ flagResidual c := by
  let g : triangularGroup c := ⟨cubic r s hrs,(triangularGroup c).mul_mem
    (rectangle_root_mem_flag c r s hrs hc.le) (rectangle_root_mem_flag c s r hrs.symm hc.symm.le)⟩
  refine ⟨g,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (show g^3=1 from Subtype.ext (cubic_cube r s hrs)))

private theorem rectangle_root_mem_residual (c : Fin (m+1) → Fin (m+1))
    (r s : Fin (m+1)) (hrs : r≠s) (hc : c r < c s)
    (hp : (∃ k,k≠r ∧ c k=c r) ∨ (∃ k,k≠s ∧ c k=c s)) :
    root r s hrs 1 ∈ flagResidual c := by
  apply root_mem_residual (fun i => (c i).val) (triangularGroup c)
    (fun i j hij hijc => rectangle_root_mem_flag c i j hij hijc) r s hrs hc
  rcases hp with ⟨k,hkr,hk⟩ | ⟨k,hks,hk⟩
  · exact Or.inl ⟨k,hkr,congrArg Fin.val hk⟩
  · exact Or.inr ⟨k,hks,congrArg Fin.val hk⟩

private theorem rectangle_root_mem_moving (c : Fin (m+1) → Fin (m+1)) (hmono : Monotone c)
    (r s : Fin (m+1)) (hrs : r≠s) (hc : c r < c s)
    (hp : (∃ k,k≠r ∧ c k=c r) ∨ (∃ k,k≠s ∧ c k=c s)) :
    root r s hrs 1 ∈ ⁅(flagResidual c).pCoreIn 2,flagResidual c⁆ := by
  have hR : flagResidual c ≤ triangularGroup c := map_subtype_le _
  rcases hp with ⟨k,hkr,hk⟩ | ⟨k,hks,hk⟩
  · have hks : k≠s := fun he => (ne_of_lt hc) (by simpa [he] using hk.symm)
    have hx : root k s hks 1 ∈ (flagResidual c).pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 hR ⟨rectangle_root_mem_residual c k s hks (by rwa [hk])
        (Or.inl ⟨r,hkr.symm,hk.symm⟩),rectangle_root_mem_flag_core c hmono k s hks (by rwa [hk])⟩
    rw [←root_row_commutator r k s hkr.symm hrs hks,commutator_comm]
    exact commutator_mem_commutator (rectangle_cubic_mem_residual c r k hkr.symm hk.symm) hx
  · have hrk : r≠k := fun he => (ne_of_lt hc) (by simpa [he] using hk)
    have hx : root r k hrk 1 ∈ (flagResidual c).pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 hR ⟨rectangle_root_mem_residual c r k hrk (by rwa [hk])
        (Or.inr ⟨s,hks.symm,hk.symm⟩),rectangle_root_mem_flag_core c hmono r k hrk (by rwa [hk])⟩
    rw [←root_column_commutator r k s hrk hrs hks]
    exact commutator_mem_commutator hx (rectangle_cubic_mem_residual c k s hks hk)

private theorem radical_difference (k : Fin m) (g : LinearGroup (m+1))
    (hg : g ∈ BinaryLinear.radical (cutSpace standardBasis k)) (i j : Fin (m+1))
    (hout : k.val < i.val ∨ j.val ≤ k.val) :
    (matrix g-1) i j=0 := by
  rcases hout with hi | hj
  · have hh := (mem_standard_cutSpace k _).mp (hg.2 (standardBasis j)) i hi
    rw [Matrix.sub_apply,matrix_apply,Matrix.one_apply]
    simpa only [Pi.sub_apply,standardBasis,Pi.basisFun_apply,Pi.single_apply,eq_comm] using hh
  · have hh := congrFun (hg.1 (standardBasis j) ((basis_mem_cutSpace standardBasis k j).mpr hj)) i
    change matrix g i j-(1 : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2)) i j=0
    rw [matrix_apply,hh]
    simp [standardBasis,Pi.single_apply,Matrix.one_apply]

private theorem mem_radical_of_difference (k : Fin m) (g : LinearGroup (m+1))
    (hg : ∀ i j : Fin (m+1), k.val < i.val ∨ j.val ≤ k.val → (matrix g-1) i j=0) :
    g ∈ BinaryLinear.radical (cutSpace standardBasis k) := by
  have hfix (j : Fin (m+1)) (hj : j.val ≤ k.val) : g (standardBasis j)=standardBasis j := by
    ext i
    have hh : matrix g i j=(1 : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2)) i j :=
      sub_eq_zero.mp (hg i j (Or.inr hj))
    rw [matrix_apply,Matrix.one_apply] at hh
    simpa only [standardBasis,Pi.basisFun_apply,Pi.single_apply,eq_comm] using hh
  refine ⟨?_,?_⟩
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨j,hj,rfl⟩ := hv; exact hfix j hj
    | zero => exact map_zero g
    | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
    | smul a x hx ih => simp only [map_smul,ih]
  · intro v
    apply (mem_standard_cutSpace k _).mpr
    intro i hi
    change g v i-v i=0
    have hr : ∀ j, matrix g i j=(1 : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2)) i j :=
      fun j => sub_eq_zero.mp (hg i j (Or.inl hi))
    have he : (matrix g).mulVec v=g v := by
      rw [matrix,←slEquivLinear_apply,MulEquiv.apply_symm_apply]
    rw [←he]
    have hm : (matrix g).mulVec v i=(1 : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2)).mulVec v i := by
      simp only [Matrix.mulVec,dotProduct,hr]
    rw [hm,Matrix.one_mulVec,sub_self]

private theorem radical_le_moving (hm : m=3 ∨ m=4)
    (c : Fin (m+1) → Fin (m+1)) (hmono : Monotone c) (k : Fin m)
    (hcross : ∀ i j : Fin (m+1), i.val ≤ k.val → k.val < j.val → c i < c j)
    (hpartner : ∀ i j : Fin (m+1), i.val ≤ k.val → k.val < j.val →
      (∃ t,t≠i ∧ c t=c i) ∨ (∃ t,t≠j ∧ c t=c j)) :
    BinaryLinear.radical (cutSpace standardBasis k) ≤ ⁅(flagResidual c).pCoreIn 2,flagResidual c⁆ := by
  intro g hg
  have hdiag (i : Fin (m+1)) : entries g i i=1 := by
    have hh := radical_difference k g hg i i (by omega)
    simp only [Matrix.sub_apply,Matrix.one_apply,ite_true] at hh
    rw [sub_eq_zero] at hh
    simpa only [matrix_apply,standardBasis,Pi.basisFun_apply,entries] using hh
  have hzero (i j : Fin (m+1)) (hji : j < i) : entries g i j=0 := by
    have hh := radical_difference k g hg i j (by change j.val < i.val at hji; omega)
    have hij : i≠j := ne_of_gt hji
    change matrix g i j-(1 : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2)) i j=0 at hh
    simpa only [Matrix.one_apply,if_neg hij,sub_zero,matrix_apply,standardBasis,Pi.basisFun_apply,entries] using hh
  have hroot (i j : Fin (m+1)) (hij : i < j) :
      root i j (ne_of_lt hij) (entries g i j) ∈ ⁅(flagResidual c).pCoreIn 2,flagResidual c⁆ := by
    by_cases hcrossij : i.val ≤ k.val ∧ k.val < j.val
    · have hmem := rectangle_root_mem_moving c hmono i j (ne_of_lt hij)
        (hcross i j hcrossij.1 hcrossij.2) (hpartner i j hcrossij.1 hcrossij.2)
      have ha : entries g i j=0 ∨ entries g i j=1 := by exact (by decide : ∀a:ZMod 2,a=0∨a=1) _
      rcases ha with ha | ha
      · rw [ha,root_zero]; exact one_mem _
      · rwa [ha]
    · have hh := radical_difference k g hg i j (by omega)
      have hi : i≠j := ne_of_lt hij
      have he : entries g i j=0 := by
        change matrix g i j-(1 : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2)) i j=0 at hh
        simpa only [Matrix.one_apply,if_neg hi,sub_zero,matrix_apply,standardBasis,Pi.basisFun_apply,entries] using hh
      rw [he,root_zero]
      exact one_mem _
  rcases hm with rfl | rfl
  · exact upper_four_mem _ g hzero hdiag hroot
  · exact upper_five_mem _ g hzero hdiag hroot

private def endpointLabel (last : Bool) : Fin 4 → Fin 4 :=
  if last then ![0,0,0,1] else ![0,1,1,1]
private def endpointCut (last : Bool) : Fin 3 := if last then 2 else 0
private def adjacentCut (last : Bool) : Fin 4 := if last then 2 else 1

private theorem residual_core_difference (c : Fin (m+1) → Fin (m+1)) (hmono : Monotone c)
    (g : LinearGroup (m+1)) (hg : g ∈ (flagResidual c).pCoreIn 2) : Strict c (matrix g-1) := by
  have hc : (flagResidual c).pCoreIn 2 ≤ (triangularGroup c).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_subtype_le _) (le_normalizer_embedded_pResidual 2 _)
  obtain ⟨x,hx,he⟩ := hc hg
  have hk : x ∈ (diagonalAction c).ker := (ker_diagonalAction_eq_twoCore c hmono).symm ▸ hx
  rw [←he]
  exact strict_difference c x hk

private theorem residual_moving_le_core (c : Fin (m+1) → Fin (m+1)) :
    ⁅(flagResidual c).pCoreIn 2,flagResidual c⁆ ≤ (flagResidual c).pCoreIn 2 := by
  rw [commutator_comm]
  apply le_normalizer_iff_commutator_le_right.mp
  exact normalizer_le_normalizer_characteristic_image (flagResidual c) (pCore 2 (flagResidual c)) |>
    le_trans (flagResidual c).le_normalizer

private theorem endpoint_moving_eq_radical (last : Bool) :
    ⁅(flagResidual (endpointLabel last)).pCoreIn 2,flagResidual (endpointLabel last)⁆ =
      BinaryLinear.radical (cutSpace standardBasis (endpointCut last)) := by
  apply le_antisymm
  · intro g hg
    have hs := residual_core_difference (endpointLabel last) (by cases last <;> decide) g
      (residual_moving_le_core _ hg)
    apply mem_radical_of_difference
    intro i j hout
    apply hs
    revert hout
    cases last <;> revert i j <;> decide
  · apply radical_le_moving (Or.inl rfl) _ (by cases last <;> decide)
    · intro i j hi hj
      revert hi hj
      cases last <;> revert i j <;> decide
    · intro i j hi hj
      revert hi hj
      cases last <;> revert i j <;> decide

private theorem adjacent_residual_scalar (last : Bool) (g : LinearGroup 5)
    (hg : g ∈ flagResidual (adjacentLabel last)) : matrix g (scalarRow last) (scalarCol last)=0 := by
  obtain ⟨x,hx,rfl⟩ := hg
  have hp : IsPGroup 2 (Multiplicative (ZMod 2)) :=
    IsPGroup.of_card (n := 1) (by simp)
  have hh := pResidual_le_ker_of_isPGroup 2 (scalarHom last) hp hx
  exact congrArg Multiplicative.toAdd hh

private theorem adjacent_moving_eq_radical (last : Bool) :
    ⁅(flagResidual (adjacentLabel last)).pCoreIn 2,flagResidual (adjacentLabel last)⁆ =
      BinaryLinear.radical (cutSpace standardBasis (adjacentCut last)) := by
  apply le_antisymm
  · intro g hg
    have hc := residual_moving_le_core _ hg
    have hs := residual_core_difference (adjacentLabel last) (by cases last <;> decide) g hc
    have hz := adjacent_residual_scalar last g ((flagResidual _).pCoreIn_le 2 hc)
    apply mem_radical_of_difference
    intro i j hout
    have hh : adjacentLabel last j ≤ adjacentLabel last i ∨ (i=scalarRow last ∧ j=scalarCol last) := by
      revert hout
      cases last <;> revert i j <;> decide
    rcases hh with hh | ⟨rfl,rfl⟩
    · exact hs _ _ hh
    · rw [Matrix.sub_apply,hz]
      cases last <;> decide
  · apply radical_le_moving (Or.inr rfl) _ (by cases last <;> decide)
    · intro i j hi hj
      revert hi hj
      cases last <;> revert i j <;> decide
    · intro i j hi hj
      revert hi hj
      cases last <;> revert i j <;> decide

private theorem radical_card_exact {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (W : Submodule (ZMod 2) V) :
    Nat.card (BinaryLinear.radical W)=
      2^(Module.finrank (ZMod 2) W*(Module.finrank (ZMod 2) V-Module.finrank (ZMod 2) W)) := by
  have hz (w : W) : W.mkQ (w : V)=0 := Submodule.Quotient.mk_eq_zero W |>.mpr w.property
  let sh (f : (V ⧸ W) →ₗ[ZMod 2] W) : BinaryLinear.GL V :=
    { toFun := fun v => v+(f (W.mkQ v) : V)
      invFun := fun v => v-(f (W.mkQ v) : V)
      left_inv := by intro v; simp [map_add,hz]
      right_inv := by intro v; simp [map_sub,hz]
      map_add' := by intro v w; simp [map_add,add_add_add_comm]
      map_smul' := by intro a v; simp [map_smul,smul_add] }
  have hsh (f : (V ⧸ W) →ₗ[ZMod 2] W) : sh f ∈ BinaryLinear.radical W := by
    refine ⟨?_,?_⟩
    · intro v hv
      change v+(f (W.mkQ v) : V)=v
      rw [hz ⟨v,hv⟩,map_zero,Submodule.coe_zero,add_zero]
    · intro v
      change v+(f (W.mkQ v) : V)-v ∈ W
      rw [add_sub_cancel_left]
      exact (f _).property
  let f : ((V ⧸ W) →ₗ[ZMod 2] W) → BinaryLinear.radical W := fun a => ⟨sh a,hsh a⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := W.mkQ_surjective v
      apply Subtype.ext
      have hh := congrArg (fun g : BinaryLinear.radical W => g.val w) he
      exact add_left_cancel hh
    · intro g
      let d : (V ⧸ W) →ₗ[ZMod 2] W := W.liftQ
        ((g.val.toLinearMap-LinearMap.id).codRestrict W g.property.2) (by
          intro w hw
          apply Subtype.ext
          change g.val w-w=0
          exact sub_eq_zero.mpr (g.property.1 w hw))
      refine ⟨d,?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change v+(g.val v-v)=g.val v
      abel
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Module.natCard_eq_pow_finrank (K := ZMod 2),
    Module.finrank_linearMap,Nat.card_zmod]
  have hd := W.finrank_quotient_add_finrank
  have he : Module.finrank (ZMod 2) (V ⧸ W)=
      Module.finrank (ZMod 2) V-Module.finrank (ZMod 2) W := by omega
  rw [he,Nat.mul_comm]

private theorem flag_coordinate_residual_moving
    (b : Basis m) (cuts : Set (Fin m)) :
    (⁅(((pResidual 2 (cutStabilizer b cuts)).map (cutStabilizer b cuts).subtype)).pCoreIn 2,
      (pResidual 2 (cutStabilizer b cuts)).map (cutStabilizer b cuts).subtype⁆).map
      (MulAut.conj b.equivFun).toMonoidHom =
    ⁅(flagResidual (cutLabel cuts)).pCoreIn 2,flagResidual (cutLabel cuts)⁆ := by
  have hb : b.map b.equivFun=standardBasis := by
    ext i j
    simp [standardBasis,Module.Basis.equivFun_self,Pi.basisFun_apply,Pi.single_apply,eq_comm]
  rw [map_commutator,map_pCoreIn_of_injective 2 _ _ (MulAut.conj b.equivFun).injective,
    map_embedded_pResidual,cutStabilizer_map_conj,hb,←triangularGroup_cutLabel]
  rfl

private theorem flag_coordinate_radical (b : Basis m) (k : Fin m) :
    (BinaryLinear.radical (cutSpace b k)).map (MulAut.conj b.equivFun).toMonoidHom =
      BinaryLinear.radical (cutSpace standardBasis k) := by
  have hb : b.map b.equivFun=standardBasis := by
    ext i j
    simp [standardBasis,Module.Basis.equivFun_self,Pi.basisFun_apply,Pi.single_apply,eq_comm]
  rw [radical_map_conj,←cutSpace_map,hb]

/-- The endpoint residual moving core is the literal one-by-three or
three-by-one radical in the same supplied basis, and has order8. -/
theorem endpoint_residual_moving_rectangle (b : Basis 3) (last : Bool) :
    let k : Fin 3 := if last then 2 else 0
    let P := cutStabilizer b ({k} : Set (Fin 3))
    let R := (pResidual 2 P).map P.subtype
    ⁅R.pCoreIn 2,R⁆=BinaryLinear.radical (cutSpace b k) ∧ Nat.card (⁅R.pCoreIn 2,R⁆ : Subgroup (LinearGroup 4))=8 := by
  let k := endpointCut last
  let P := cutStabilizer b ({k} : Set (Fin 3))
  let R := (pResidual 2 P).map P.subtype
  have hl : cutLabel ({k} : Set (Fin 3))=endpointLabel last := by
    ext i
    cases last <;> fin_cases i <;> simp [k,endpointCut,endpointLabel,cutLabel,
      show (Finset.univ : Finset (Fin 3))={0,1,2} from by decide,
      Finset.filter_insert,Finset.filter_singleton]
  have he : ⁅R.pCoreIn 2,R⁆=BinaryLinear.radical (cutSpace b k) := by
    apply map_injective (f := (MulAut.conj b.equivFun).toMonoidHom) (MulAut.conj b.equivFun).injective
    rw [flag_coordinate_residual_moving,flag_coordinate_radical,hl]
    exact endpoint_moving_eq_radical last
  refine ⟨he,?_⟩
  change Nat.card (⁅R.pCoreIn 2,R⁆ : Subgroup (LinearGroup 4))=8
  rw [he,radical_card_exact,cutSpace_finrank]
  cases last <;> norm_num [k,endpointCut,Space]

/-- The adjacent-flag residual moving core is the literal two-by-three or
three-by-two radical. The singleton scalar is absent; its order is64. -/
theorem adjacent_residual_moving_rectangle (b : Basis 4) (last : Bool) :
    let cuts : Set (Fin 4) := if last then {2,3} else {0,1}
    let k : Fin 4 := if last then 2 else 1
    let P := cutStabilizer b cuts
    let R := (pResidual 2 P).map P.subtype
    ⁅R.pCoreIn 2,R⁆=BinaryLinear.radical (cutSpace b k) ∧ Nat.card (⁅R.pCoreIn 2,R⁆ : Subgroup (LinearGroup 5))=64 := by
  let cuts : Set (Fin 4) := if last then {2,3} else {0,1}
  let k := adjacentCut last
  let P := cutStabilizer b cuts
  let R := (pResidual 2 P).map P.subtype
  have hl : cutLabel cuts=adjacentLabel last := by
    cases last
    · exact cut_pair_first
    · exact cut_pair_last
  have he : ⁅R.pCoreIn 2,R⁆=BinaryLinear.radical (cutSpace b k) := by
    apply map_injective (f := (MulAut.conj b.equivFun).toMonoidHom) (MulAut.conj b.equivFun).injective
    rw [flag_coordinate_residual_moving,flag_coordinate_radical,hl]
    exact adjacent_moving_eq_radical last
  refine ⟨he,?_⟩
  change Nat.card (⁅R.pCoreIn 2,R⁆ : Subgroup (LinearGroup 5))=64
  rw [he,radical_card_exact,cutSpace_finrank]
  cases last <;> norm_num [k,adjacentCut,Space]

end BinaryLinear.SevenFlagCore
