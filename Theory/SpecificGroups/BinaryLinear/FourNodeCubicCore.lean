module

public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SylowPointSelection
public import Theory.GroupAction.NoncentralTwoChiefLength.Native

/-!
# Two cubic core layers in every binary four-dimensional minimal parabolic

Four explicit incident root coordinates lie in the actual residual's
intrinsic two-core. Their sixteen conjugates of the marked cubic are
pairwise distinct. Thus the original core centralizer index is at least
sixteen, giving two noncentral binary cubic layers without a supplied
core identification or a parabolic recognition callback.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions

private def pairs : Fin 3 → Fin 4 → Fin 4 × Fin 4 :=
  ![![(0,2),(1,2),(0,3),(1,3)],![(0,1),(0,2),(1,3),(2,3)],![(0,2),(0,3),(1,2),(1,3)]]
private theorem pair_ne (i : Fin 3) (j : Fin 4) : (pairs i j).1≠(pairs i j).2 := by
  revert i j
  decide
private noncomputable def r (i : Fin 3) (j : Fin 4) : LinearGroup 4 :=
  CubicPairNormalizers.CoreAbsorption.root (pairs i j).1 (pairs i j).2 (pair_ne i j) 1
private noncomputable def rawWord (i : Fin 3) (p : Fin 4 → Bool) : LinearGroup 4 :=
  (if p 0 then r i 0 else 1)*(if p 1 then r i 1 else 1)*
    (if p 2 then r i 2 else 1)*(if p 3 then r i 3 else 1)
private noncomputable def rawC (i : Fin 3) : LinearGroup 4 :=
  CubicPairNormalizers.CoreAbsorption.cubic i.castSucc i.succ (by simp [Fin.ext_iff])
set_option maxRecDepth 8192 in
private theorem raw_separation : ∀ (i : Fin 3) (p q : Fin 4 → Bool),
    (∀ (j k : Fin 4), (rawWord i p * rawC i * (rawWord i p)⁻¹) (Pi.single j 1) k =
      (rawWord i q * rawC i * (rawWord i q)⁻¹) (Pi.single j 1) k) → p=q := by
  decide +kernel

private theorem root_transvection {m : ℕ} (b : Basis m)
    (r s : Fin (m+1)) (hrs : r ≠ s) :
    root b r s hrs = transvection (b r) (b.coord s) (by simp [hrs]) := by
  apply b.ext'
  intro j
  rw [root_basis]
  change (if j = s then b j + b r else b j) = b j + b.coord s (b j) • b r
  by_cases hj : j = s <;> simp [hj,Module.Basis.coord_apply]

private theorem root_in_radical {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m+1)) (hrs : r ≠ s) (hr : r.val ≤ i.val) (hs : i.val < s.val) :
    root b r s hrs ∈ radical (cutSpace b i) := by
  have hcoord : ∀ v ∈ cutSpace b i, b.coord s v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j,hj,rfl⟩ := hv
      have hjs : j ≠ s := by intro he; subst j; exact (Nat.not_le_of_gt hs) hj
      simp [Module.Basis.coord_apply,hjs]
    | zero => exact map_zero _
    | add v w hv hw ihv ihw => simp only [map_add,ihv,ihw,add_zero]
    | smul c v hv ih => simp only [map_smul,ih,smul_zero]
  rw [root_transvection]
  constructor
  · intro v hv
    change v + b.coord s v • b r = v
    rw [hcoord v hv,zero_smul,add_zero]
  · intro v
    change v + b.coord s v • b r - v ∈ cutSpace b i
    rw [add_sub_cancel_left]
    exact (cutSpace b i).smul_mem _ ((basis_mem_cutSpace b i r).mpr hr)

private theorem root_mem_core (b : Basis 3) (i : Fin 3) (j : Fin 4) :
    root b (pairs i j).1 (pairs i j).2 (pair_ne i j)∈(nodeResidual b i).pCoreIn 2 := by
  let r := (pairs i j).1
  let s := (pairs i j).2
  have hinc_all : ∀ (i : Fin 3) (j : Fin 4), Incident i (pairs i j).1 (pairs i j).2 := by
    unfold Incident
    decide
  have hcut_all : ∀ (i : Fin 3) (j : Fin 4), ∃ k : Fin 3,
      k≠i ∧ (pairs i j).1.val≤k.val ∧ k.val<(pairs i j).2.val := by decide
  have hinc : Incident i r s := hinc_all i j
  obtain ⟨k,hki,hr,hs⟩ := hcut_all i j
  let J := nodeResidual b i
  let V := cutSpace b k
  have hJP : J≤parabolic V := by
    intro g hg
    have hh := map_subtype_le (pResidual 2 (minimalParabolic b i)) hg
    exact (mem_cutStabilizer b _ _).mp hh k hki
  have hn : J≤normalizer ((J ⊓ radical V : Subgroup (LinearGroup 4)) : Set _) :=
    (le_inf J.le_normalizer (hJP.trans (parabolic_le_normalizer V))).trans inf_normalizer_le_normalizer_inf
  have hc : J ⊓ radical V≤J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((radical_two V).to_le inf_le_right) inf_le_left hn
  exact hc ⟨incident_root_mem_nodeResidual b i r s (pair_ne i j) hinc,
    root_in_radical b k r s (pair_ne i j) hr hs⟩

private def markedWord (b : Basis 3) (i : Fin 3) (p : Fin 4 → Bool) : LinearGroup 4 :=
  MulAut.conj b.equivFun.symm (rawWord i p)

private theorem markedWord_mem (b : Basis 3) (i : Fin 3) (p : Fin 4 → Bool) :
    markedWord b i p∈(nodeResidual b i).pCoreIn 2 := by
  have hfactor (j : Fin 4) :
      MulAut.conj b.equivFun.symm (if p j then r i j else 1) ∈ (nodeResidual b i).pCoreIn 2 := by
    split_ifs
    · exact root_mem_core b i j
    · rw [map_one]
      exact one_mem _
  unfold markedWord rawWord
  simp only [map_mul]
  exact mul_mem (mul_mem (mul_mem (hfactor 0) (hfactor 1)) (hfactor 2)) (hfactor 3)

private theorem marked_cubic (b : Basis 3) (i : Fin 3) :
    MulAut.conj b.equivFun.symm (rawC i)=cubic b i.castSucc i.succ (by simp [Fin.ext_iff]) := by
  simp only [rawC,CubicPairNormalizers.CoreAbsorption.cubic,map_mul,cubic,root]

/-- The actual marked cubic of every binary four-space node moves at
least two binary chief layers in the literal node residual's two-core. -/
theorem four_node_cubic_core_length (b : Basis 3) (i : Fin 3) :
    let c := cubic b i.castSucc i.succ (by simp [Fin.ext_iff])
    orderOf c=3 ∧ c∈nodeResidual b i ∧
      2≤conjugationCubicLength (zpowers c) ((nodeResidual b i).pCoreIn 2) := by
  let : Finite (LinearGroup 4) := Finite.of_injective
    (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  let c := cubic b i.castSucc i.succ (by simp [Fin.ext_iff])
  let Q := (nodeResidual b i).pCoreIn 2
  have hsep : Function.Injective (fun p : Fin 4 → Bool => markedWord b i p*c*(markedWord b i p)⁻¹) := by
    intro p q he
    have he' : rawWord i p*rawC i*(rawWord i p)⁻¹=rawWord i q*rawC i*(rawWord i q)⁻¹ := by
      apply (MulAut.conj b.equivFun.symm).injective
      simpa only [map_mul,map_inv,marked_cubic,markedWord,c] using he
    exact raw_separation i p q (fun j k => congrArg (fun g : LinearGroup 4 => g (Pi.single j 1) k) he')
  have hc1 : c≠1 := by
    intro he
    have hconst : ∀ p : Fin 4 → Bool, markedWord b i p*c*(markedWord b i p)⁻¹=1 := by simp [he]
    have hh := hsep ((hconst (fun _=>false)).trans (hconst (fun _=>true)).symm)
    have hh0 := congrFun hh 0
    contradiction
  let f : (Fin 4 → Bool) → conjugacyOrbit Q c := fun p =>
    ⟨markedWord b i p*c*(markedWord b i p)⁻¹,⟨⟨markedWord b i p,markedWord_mem b i p⟩,rfl⟩⟩
  have hf : Function.Injective f := fun p q he => hsep (congrArg Subtype.val he)
  have hc : 16≤(centralizer ({c} : Set (LinearGroup 4))).relIndex Q := by
    have hh := Nat.card_le_card_of_injective f hf
    have hdom : Nat.card (Fin 4 → Bool)=16 := by simp [Nat.card_eq_fintype_card]
    rw [hdom,Nat.card_coe_set_eq,conjugacyOrbit_ncard_eq_relIndex] at hh
    exact hh
  refine ⟨orderOf_eq_prime (cubic_cube b i.castSucc i.succ _) hc1,cubic_mem_nodeResidual b i,?_⟩
  change 2≤Nat.log 4 ((centralizer (zpowers c : Set (LinearGroup 4))).relIndex Q)
  rw [zpowers_eq_closure,centralizer_closure]
  exact (by decide : 2≤Nat.log 4 16).trans (Nat.log_mono_right hc)

end BinaryLinear.OrderedResidualConjugators
