module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.PairAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Residual
public import Theory.GroupTheory.CentralCoverCenteredModules
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
import all Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.Bridge
/-!
# Full two-core movement in the second J₄ centralizer residual

Two words of odd orders dividing seven and eleven fix the marked star pair.
Their induced automorphisms of M₂₂ are inner, so they lift to the perfect
residual of the original centralizer. Eleven small XOR certificates express
every elementary-kernel basis vector as a sum of their displacements. The
certified star action transports these identities to actual commutators.
Thus the full kernel belongs to the residual and is fully moved. Its
M₂₂ quotient identifies that kernel with the residual's entire two-core.

The identity transfers to the full native centralizer and lifts through
any specified odd central cover. The covering kernel and the original
solvable residual are retained throughout.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623. The literal kernel, star labels and conjugation conventions
are the imported ATLAS J4G1-max1W1 certificates. The two words and eleven
XOR identities below are checked by Lean's kernel; no external calculation
is trusted. The private bridge is imported only to identify its quotient
projection with the public actual conjugation map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
set_option backward.isDefEq.respectTransparency true
open scoped Pointwise IsMulCommutative commutatorElement
namespace Janko4.InvolutionCentralizers.Second.CoreMovement
open Cardinality.KernelCount Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open LocalStructure.SylowCore LocalStructure.SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup
private def sx : StarGroup := ⟨rightX, by
  have h : starX ∈ StarGroup := subset_closure (Set.mem_insert _ _)
  exact StarGroup.inv_mem h⟩
private def sy : StarGroup := ⟨rightY, by
  have h : starY ∈ StarGroup := subset_closure (Set.mem_insert_of_mem _ rfl)
  exact StarGroup.inv_mem h⟩
private def actor (i : Fin 2) : StarGroup :=
  ![(sy*sx*sy*sy*sy)^2, sx*sy*sx*sy*sy*sx*sy*sx*sy] i
private theorem actor_pair (i : Fin 2) : actor i ∈ starPairStabilizer := by
  apply MulAction.mem_stabilizer_finset'.mpr
  have h : ∀ i : Fin 2, ∀ j ∈ starPair, (actor i).val j ∈ starPair := by decide +kernel
  exact h i
private def prime (i : Fin 2) : ℕ := ![7,11] i
private theorem actor_pow (i : Fin 2) : actor i ^ prime i = 1 := by
  apply Subtype.ext
  have h : ∀ i : Fin 2, (actor i).val ^ prime i = 1 := by decide +kernel
  exact h i
private def row (i : Fin 22) : ℕ :=
  Nat.xor (2^(i.val % 11)) (starMask (actor ⟨i.val / 11,by omega⟩) (2^(i.val % 11)))
private def witness : Fin 11 → List (Fin 22) :=
  ![[1,4,5,7,8,9,17,18], [1,7,8,18], [2,3,4,8,17], [2,4,8,17],
    [7,8,18], [3,4,8,17], [1,6,7,8,18], [4,7,8,18],
    [2,3,4,5,7,8,18], [2,4,8,9,17], [1,3,5,7,8,17]]
private theorem certificate (i : Fin 11) :
    ((witness i).map row).foldr Nat.xor 0 = 2^i.val := by
  have h : ∀ i : Fin 11, ((witness i).map row).foldr Nat.xor 0 = 2^i.val := by decide +kernel
  exact h i

open Sporadic.Mathieu
private theorem m22_perfect : Group.IsPerfect M22 :=
  Group.IsPerfect.ofSurjective (f := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (center M22TripleCover)))
    (M22TripleCover.centralQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
private theorem aut_residual :
    solvableResidual (MulAut M22) = MulAut.innerSubgroup M22 := by
  let := m22_perfect
  let : Group.IsPerfect (MulAut.innerSubgroup M22) := Group.IsPerfect.range MulAut.conj
  let : Group.IsNilpotent (MulAut.Outer M22) :=
    (IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
      (by simpa only [pow_one] using
        M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)).isNilpotent
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)
private theorem actor_lift (i : Fin 2) :
    ∃ g : localCentralizer, g ∈ solvableResidual localCentralizer ∧
      starHom g.val = actor i := by
  let u : starPairStabilizer := ⟨actor i,actor_pair i⟩
  let e := starPairEquivAutM22
  let q := QuotientGroup.mk' (MulAut.innerSubgroup M22)
  have hpow : q (e u) ^ prime i = 1 := by
    rw [←map_pow,←map_pow]
    have hu : u ^ prime i = 1 := Subtype.ext (actor_pow i)
    rw [hu,map_one,map_one]
  have hd : orderOf (q (e u)) ∣ 2 :=
    (_root_.orderOf_dvd_natCard _).trans M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two
  have hc : Nat.Coprime (prime i) 2 := by
    have h : ∀ i : Fin 2, Nat.Coprime (prime i) 2 := by decide
    exact h i
  have hmem : e u ∈ solvableResidual (MulAut M22) := by
    rw [aut_residual]
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hpow) hd))
  have hmap := map_solvableResidual_eq e.toMonoidHom e.surjective
  obtain ⟨v,hv,hev⟩ := hmap.symm ▸ hmem
  have hvu : v = u := e.injective hev
  subst v
  have ht := map_solvableResidual_eq toStarPair toStarPair_surjective
  obtain ⟨g,hg,he⟩ := ht.symm ▸ hv
  exact ⟨g,hg,congrArg (fun w : starPairStabilizer => (w : StarGroup)) he⟩

private def eval (m : ℕ) : localCentralizer :=
  ⟨coordinates matrixA_mul_self matrixB_pow_four (fun i => m.testBit i.val),
    max1Kernel_le_localCentralizer (coordinates _ _ _).property⟩
private theorem eval_mem (m : ℕ) : eval m ∈ kernel :=
  (coordinates matrixA_mul_self matrixB_pow_four (fun i => m.testBit i.val)).property
private theorem eval_zero : eval 0 = 1 := by
  apply Subtype.ext
  simp [eval,coordinates_val,binaryProduct_zero]
private theorem eval_xor (m n : ℕ) : eval (Nat.xor m n) = eval m * eval n := by
  apply Subtype.ext
  change ((coordinates matrixA_mul_self matrixB_pow_four (fun i => (m ^^^ n).testBit i.val)) : Local) = _
  simp only [Nat.testBit_xor]
  exact congrArg max1Kernel.subtype (coordinates_mul _ _ (fun i => m.testBit i.val)
    (fun i => n.testBit i.val)).symm
private theorem eval_basis (i : Fin 11) :
    (eval (2^i.val) : Local) = basis matrixA_mul_self matrixB_pow_four i := by
  simp only [eval, coordinates_val, Nat.testBit_two_pow]
  convert binaryProduct_single (basis matrixA_mul_self matrixB_pow_four) i using 2
  funext j
  simp only [Fin.ext_iff,eq_comm]
private theorem eval_action (g : localCentralizer) (m : ℕ) (hm : m < 2048) :
    eval (starMask (starHom g.val) m) = g * eval m * g⁻¹ := by
  have h := maskEquiv_starMask matrixA_mul_self matrixB_pow_four g.val ⟨m,hm⟩
  have he : starProjection matrixA_mul_self matrixB_pow_four g.val = starHom g.val := rfl
  rw [he] at h
  apply Subtype.ext
  exact congrArg max1Kernel.subtype h
private theorem row_mem (i : Fin 22) :
    eval (row i) ∈ ⁅kernel,solvableResidual localCentralizer⁆ := by
  obtain ⟨g,hg,he⟩ := actor_lift ⟨i.val / 11,by omega⟩
  have hm : 2^(i.val % 11) < 2048 := by
    exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.mod_lt _ (by decide))).trans_eq (by decide)
  have hi : (eval (2^(i.val % 11)))⁻¹ = eval (2^(i.val % 11)) := by
    let := kernel_elementary
    exact inv_eq_of_mul_eq_one_right (by
      have h := elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (eval (2^(i.val % 11))) (eval_mem _)
      simpa only [pow_two] using h)
  rw [row,eval_xor,←he,eval_action g _ hm]
  have hc : eval (2^(i.val % 11)) * (g * eval (2^(i.val % 11)) * g⁻¹) =
      (g * eval (2^(i.val % 11)) * g⁻¹) * eval (2^(i.val % 11)) := by
    let := kernel_elementary
    exact congrArg kernel.subtype (mul_comm
      (⟨_,eval_mem _⟩ : kernel)
      ⟨_,(inferInstance : kernel.Normal).conj_mem _ (eval_mem _) g⟩)
  rw [hc,commutator_comm kernel]
  simpa only [commutatorElement_def,hi] using
    (commutator_mem_commutator hg (eval_mem (2^(i.val % 11))))
private theorem eval_fold_mem (U : Subgroup localCentralizer) (l : List ℕ)
    (h : ∀ m ∈ l, eval m ∈ U) : eval (l.foldr Nat.xor 0) ∈ U := by
  induction l with
  | nil => simpa only [List.foldr_nil,eval_zero] using U.one_mem
  | cons m l ih =>
    rw [List.foldr_cons,eval_xor]
    exact U.mul_mem (h m (by simp)) (ih (fun n hn => h n (by simp [hn])))

/-- The second native centralizer residual moves all eleven kernel coordinates. -/
theorem kernel_fully_moved : ⁅kernel,solvableResidual localCentralizer⁆ = kernel := by
  apply le_antisymm (commutator_le_left _ _)
  let U := ⁅kernel,solvableResidual localCentralizer⁆
  have hb (i : Fin 11) : eval (2^i.val) ∈ U := by
    rw [←certificate i]
    apply eval_fold_mem
    intro m hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
    exact row_mem j
  intro n hn
  have hlocal : (n : Local) ∈ U.map localCentralizer.subtype := by
    obtain ⟨v,hv⟩ := (mem_localKernel_iff_binaryProduct _ _ n.val).mp hn
    rw [←hv]
    apply binaryProduct_mem
    intro i
    rw [←eval_basis i]
    exact mem_map_of_mem localCentralizer.subtype (hb i)
  obtain ⟨u,hu,he⟩ := hlocal
  exact (Subtype.ext he : u = n) ▸ hu


private theorem residual_local_core_fully_moved :
    ⁅pCore 2 (solvableResidual localCentralizer),
      (⊤ : Subgroup (solvableResidual localCentralizer))⁆ =
        pCore 2 (solvableResidual localCentralizer) := by
  let P := solvableResidual localCentralizer
  have hNP : kernel ≤ P := by
    rw [←kernel_fully_moved]
    exact commutator_le_right _ _
  let e := (MulEquiv.subgroupCongr aut_residual).trans
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).symm
  let d := (MulEquiv.subgroupCongr
    (map_solvableResidual_eq toAutM22 toAutM22_surjective)).trans e
  let f : P →* M22 := d.toMonoidHom.comp (toAutM22.subgroupMap P)
  have hf : Function.Surjective f := d.surjective.comp (toAutM22.subgroupMap_surjective P)
  have hk : f.ker = kernel.subgroupOf P := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,ker_subgroupMap,toAutM22_ker]
  have hkill : pCore 2 P ≤ f.ker := by
    let := m22_isSimpleGroup
    let := m22_perfect
    have hn : ((pCore 2 P).map f).Normal :=
      (inferInstance : (pCore 2 P).Normal).map f hf
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · have hp : IsPGroup 2 M22 := by
        have ht' : IsPGroup 2 (⊤ : Subgroup M22) := ht ▸ pCore_isPGroup.map f
        exact ht'.of_equiv topEquiv
      let : Group.IsNilpotent M22 := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable M22 inferInstance).elim
  have hmap : (pCore 2 P).map P.subtype = kernel := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hk ▸ hkill hx : x ∈ kernel.subgroupOf P)
    · intro x hx
      have hle : kernel.subgroupOf P ≤ pCore 2 P :=
        le_sSup ⟨inferInstance,kernel_isTwoGroup.comap_subtype⟩
      exact ⟨⟨x,hNP hx⟩,hle hx,rfl⟩
  apply (map_injective P.subtype_injective)
  rw [map_commutator,hmap,←MonoidHom.range_eq_map,range_subtype]
  exact kernel_fully_moved
end Janko4.InvolutionCentralizers.Second.CoreMovement

namespace Janko4.InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB
open Subgroup Theory.GroupTheory
/-- The perfect residual of the second native centralizer moves its full two-core. -/
theorem residual_core_fully_moved :
    ⁅pCore 2 (solvableResidual ambientCentralizer),
      (⊤ : Subgroup (solvableResidual ambientCentralizer))⁆ =
        pCore 2 (solvableResidual ambientCentralizer) := by
  let e := (ambientEquivLocal.subgroupMap (solvableResidual ambientCentralizer)).trans
    (MulEquiv.subgroupCongr (map_solvableResidual_eq ambientEquivLocal.toMonoidHom
      ambientEquivLocal.surjective))
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [map_commutator,pCore_map_iso 2 e,map_top_of_surjective e.toMonoidHom e.surjective]
  exact CoreMovement.residual_local_core_fully_moved
private theorem core_movement_of_odd_central_cover
    {X Y : Type*} [Group X] [Finite X] [Group Y]
    (q : X →* Y) (hq : Function.Surjective q) (hc : q.ker ≤ center X)
    (ho : Nat.Coprime 2 (Nat.card q.ker))
    (hm : ⁅pCore 2 Y,(⊤ : Subgroup Y)⁆ = pCore 2 Y) :
    ⁅pCore 2 X,(⊤ : Subgroup X)⁆ = pCore 2 X := by
  let R := ⁅pCore 2 X,(⊤ : Subgroup X)⁆
  have hR : R ≤ pCore 2 X := commutator_le_left _ _
  have hcore := q.map_pCore_of_central_kernel_centered hq hc (p := 2)
  have hmap : R.map q = (pCore 2 X).map q := by
    rw [show R = ⁅pCore 2 X,⊤⁆ from rfl,map_commutator,
      map_top_of_surjective q hq,hcore,hm]
  have hi := injective_comp_subtype_of_coprime_ker q ho (pCore 2 X) pCore_isPGroup
  apply le_antisymm hR
  intro x hx
  obtain ⟨r,hr,he⟩ := hmap.symm ▸ mem_map_of_mem q hx
  have heq : (⟨r,hR hr⟩ : pCore 2 X) = ⟨x,hx⟩ := hi he
  have heq' : r = x := congrArg (pCore 2 X).subtype heq
  exact heq' ▸ hr

/-- Full two-core movement lifts through every specified odd central cover
of the second involution centralizer, without dropping the covering kernel. -/
theorem residual_cover_core_fully_moved
    {X : Type*} [Group X] [Finite X]
    (q : X →* ambientCentralizer) (hq : Function.Surjective q) (hc : q.ker ≤ center X)
    (ho : Nat.Coprime 2 (Nat.card q.ker)) :
    ⁅pCore 2 (solvableResidual X),(⊤ : Subgroup (solvableResidual X))⁆ =
      pCore 2 (solvableResidual X) := by
  let P := solvableResidual X
  let e := MulEquiv.subgroupCongr (map_solvableResidual_eq q hq)
  let g : P →* solvableResidual ambientCentralizer := e.toMonoidHom.comp (q.subgroupMap P)
  have hg : Function.Surjective g := e.surjective.comp (q.subgroupMap_surjective _)
  have hk : g.ker = q.ker.subgroupOf P := by
    rw [show g = e.toMonoidHom.comp (q.subgroupMap P) from rfl,
      MonoidHom.ker_comp_of_injective _ _ e.injective,ker_subgroupMap]
  have hgc : g.ker ≤ center P := by
    intro x hx
    have hqx : (x : X) ∈ q.ker := by
      change x ∈ q.ker.subgroupOf P
      rwa [←hk]
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hc hqx) y))
  have hgo : Nat.Coprime 2 (Nat.card g.ker) := by
    rw [hk]
    exact ho.of_dvd_right (card_dvd_of_injective (P.subtype.subgroupComap q.ker)
      (fun x y hh => Subtype.ext (Subtype.ext
        (congrArg (fun z : q.ker => (z : X)) hh))))
  exact core_movement_of_odd_central_cover g hg hgc hgo residual_core_fully_moved

end Janko4.InvolutionCentralizers.Second
