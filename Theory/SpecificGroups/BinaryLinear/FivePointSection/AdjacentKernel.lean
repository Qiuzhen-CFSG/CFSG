module
public import Theory.SpecificGroups.BinaryLinear.FivePointSection.MiddleKernel
public import Theory.SpecificGroups.BinaryLinear.FivePointSection.AdjacentOrbit
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Flags
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality
/-!
# Normal sixteen-groups in adjacent-end binary five-space flags

For the 1+1+3 flag, the two tail rows carry the same GL₃(2) action. A
nonzero second row can be normalized; conjugation by the first root then
produces a translation in the first row. The checked seventeen-point orbit
contradicts kernel order sixteen. The second row therefore vanishes, and
equality of orders identifies the kernel with the full point radical.
Its endpoint normalizer cannot normalize the original two-residual.

Conjugation treats arbitrary bases. Actual inverse transpose followed by a
flag isomorphism treats the dual 3+1+1 flag. All normalizer and residual
maps are transported by the same ambient automorphism.
Source: the mixed point-section calculation in Aschbacher--Smith,12.9.6,
printed pp.861--862, applied in NaturalSource/LocalControl/Movement.
-/

section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.FivePointSection.AdjacentKernel
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups SmallParabolicLevi.TwoNodes
open MiddleKernel
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
noncomputable abbrev P := flagStabilizer standardBasis {0,1}
set_option backward.isDefEq.respectTransparency false in
theorem core_matrix {g : LinearGroup 5} (hg : g ∈ P.pCoreIn 2)
    (i j : Fin 5) (hij : j = 0 ∨ 2 ≤ i.val ∨ (i = 1 ∧ j = 1)) :
    matrix g i j = if i = j then 1 else 0 := by
  have hc : cutLabel ({0,1} : Set (Fin 4)) = ![0,1,2,2,2] := by
    ext k
    fin_cases k <;> simp [cutLabel, show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide, Finset.filter_insert, Finset.filter_singleton]
  have hh : ∀ r s : Fin 5, cutLabel ({0,1} : Set (Fin 4)) s ≤ cutLabel ({0,1} : Set (Fin 4)) r →
      matrix g r s = if r = s then 1 else 0 := by
    unfold P at hg
    rw [← triangularGroup_cutLabel] at hg
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hg
    rw [← ker_diagonalAction_eq_twoCore _ (cutLabel_monotone _)] at hx
    intro r s hrs
    rcases hrs.eq_or_lt with he | he
    · have hb := blockMatrix_eq_one_of_mem_ker _ x hx (cutLabel ({0,1} : Set (Fin 4)) r)
      have hm := congrArg (fun M => M ⟨r,rfl⟩ ⟨s,he⟩) hb
      simpa [blockMatrix, Matrix.one_apply] using hm
    · have hz := x.property he
      change matrix x.val r s = _
      rw [hz,if_neg]
      intro heq
      subst s
      exact (lt_irrefl _ he)
  apply hh
  rw [hc]
  revert hij
  fin_cases i <;> fin_cases j <;> decide


def tailIndex (i : Fin 3) : Fin 5 := ⟨i.val+2,by omega⟩
theorem tailIndex_injective : Function.Injective tailIndex := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  change i.val+2 = j.val+2 at hh
  omega
noncomputable def entries (g : LinearGroup 5) : AdjacentOrbit.Pair :=
  (fun i => matrix g 0 (tailIndex i),fun i => matrix g 1 (tailIndex i))

private theorem root_mem (i j : Fin 5) (hij : i ≠ j)
    (hcut : ∀ k ∈ ({0,1} : Set (Fin 4)), j.val ≤ k.val → i.val ≤ k.val) :
    root i j hij ∈ P := by
  rw [mem_standard_flagStabilizer_iff,matrix_root]
  intro k hk r s hkr hsk
  have hrs : r ≠ s := by intro he; subst s; omega
  have he : i ≠ r ∨ j ≠ s := by
    by_contra hh
    push Not at hh
    obtain ⟨rfl,rfl⟩ := hh
    have := hcut k hk hsk
    omega
  rcases he with he | he <;> simp [Matrix.add_apply,hrs,he]

noncomputable def actor (a : Fin 6) : LinearGroup 5 :=
  root (tailIndex (KernelOrbit.indices a).1) (tailIndex (KernelOrbit.indices a).2)
    (tailIndex_injective.ne (by revert a; decide))
 theorem actor_mem (a : Fin 6) : actor a ∈ P := by
  apply root_mem
  intro k hk hsk
  have hk1 : k.val ≤ 1 := by rcases hk with rfl | hk; decide; have := Set.mem_singleton_iff.mp hk; subst k; decide
  change (KernelOrbit.indices a).2.val+2 ≤ k.val at hsk
  omega
private theorem matrix_mul (x y : LinearGroup 5) : matrix (x*y) = matrix x * matrix y :=
  matrixHom.map_mul x y
 theorem entries_conj (a : Fin 6) (x : LinearGroup 5) :
    entries (actor a * x * (actor a)⁻¹) = AdjacentOrbit.act a (entries x) := by
  have hm : matrix (actor a * x * (actor a)⁻¹) =
      (1 + Matrix.single (tailIndex (KernelOrbit.indices a).1) (tailIndex (KernelOrbit.indices a).2) 1) *
        matrix x *
      (1 + Matrix.single (tailIndex (KernelOrbit.indices a).1) (tailIndex (KernelOrbit.indices a).2) 1) := by
    rw [actor,root_inv,matrix_mul,matrix_mul,matrix_root]
  apply Prod.ext <;> funext k
  all_goals
    simp only [entries,AdjacentOrbit.act,hm]
    fin_cases a <;> fin_cases k <;>
      simp [KernelOrbit.indices,tailIndex,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single_apply,Matrix.one_apply] <;> ring

 theorem core_form {g : LinearGroup 5} (hg : g ∈ P.pCoreIn 2) :
    matrix g = !![1,matrix g 0 1,matrix g 0 2,matrix g 0 3,matrix g 0 4;
      0,1,matrix g 1 2,matrix g 1 3,matrix g 1 4;
      0,0,1,0,0;0,0,0,1,0;0,0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact core_matrix hg _ _ (by decide)

noncomputable def alpha : LinearGroup 5 := root 0 1 (by decide)
noncomputable def gamma : LinearGroup 5 := root 0 2 (by decide)
 theorem alpha_mem : alpha ∈ P := by
  apply root_mem
  intro k _ _
  exact Nat.zero_le _
 theorem shear_identity {x : LinearGroup 5} (hx : x ∈ P.pCoreIn 2)
    (hv : (entries x).2 = ![1,0,0]) : alpha*x*alpha⁻¹ = gamma*x := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  change matrix x 1 2 = 1 at h0
  change matrix x 1 3 = 0 at h1
  change matrix x 1 4 = 0 at h2
  apply (slEquivLinear 5).symm.injective
  apply Subtype.ext
  change matrix (alpha*x*alpha⁻¹) = matrix (gamma*x)
  rw [alpha,gamma,root_inv,matrix_mul,matrix_mul,matrix_mul,matrix_root,matrix_root,core_form hx,h0,h1,h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single_apply,Matrix.one_apply]
  all_goals ring_nf
  all_goals exact add_eq_right.mpr (by decide)

 theorem entries_gamma {x : LinearGroup 5} (hx : x ∈ P.pCoreIn 2) :
    entries (gamma*x) = AdjacentOrbit.toggle (entries x) := by
  have hm : matrix (gamma*x) = (1 + Matrix.single 0 2 1) *
      !![1,matrix x 0 1,matrix x 0 2,matrix x 0 3,matrix x 0 4;
      0,1,matrix x 1 2,matrix x 1 3,matrix x 1 4;
      0,0,1,0,0;0,0,0,1,0;0,0,0,0,1] := by
    rw [gamma,matrix_mul,matrix_root]
    exact congrArg (fun M => (1 + Matrix.single 0 2 1)*M) (core_form hx)
  apply Prod.ext <;> funext i
  all_goals
    simp only [entries,AdjacentOrbit.toggle,hm]
    fin_cases i <;> simp [tailIndex,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single_apply,Matrix.one_apply]

 theorem second_row_zero (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16) (hQP : Q ≤ P)
    (hn : P ≤ normalizer (Q : Set (LinearGroup 5))) (x : Q) :
    (entries x.val).2 = 0 := by
  by_contra hne
  have hcore : Q ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes hQ hQP hn
  have hs : ∀ a y, y ∈ Set.range (fun q : Q => entries q.val) →
      AdjacentOrbit.act a y ∈ Set.range (fun q : Q => entries q.val) := by
    rintro a y ⟨q,rfl⟩
    exact ⟨⟨_,((hn (actor_mem a)) q.val).mp q.property⟩,entries_conj a q.val⟩
  obtain ⟨y,⟨z,rfl⟩,hz⟩ := AdjacentOrbit.normalized_member _ hs _ ⟨x,rfl⟩ hne
  have ht : gamma ∈ Q := by
    have hh := ((hn alpha_mem) z.val).mp z.property
    rw [shear_identity (hcore z.property) hz] at hh
    simpa using Q.mul_mem hh (Q.inv_mem z.property)
  have hs' : ∀ y ∈ Set.range (fun q : Q => entries q.val),
      AdjacentOrbit.toggle y ∈ Set.range (fun q : Q => entries q.val) := by
    rintro y ⟨q,rfl⟩
    exact ⟨⟨gamma*q.val,Q.mul_mem ht q.property⟩,entries_gamma (hcore q.property)⟩
  have hbound := AdjacentOrbit.large_image (fun q : Q => entries q.val) hs hs' z hz
  omega

 theorem kernel_eq_line (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16) (hQP : Q ≤ P)
    (hn : P ≤ normalizer (Q : Set (LinearGroup 5))) : Q = radical (flagSpace standardBasis 0) := by
  have hcore : Q ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes hQ hQP hn
  have hle : Q ≤ radical (flagSpace standardBasis 0) := by
    intro x hx
    apply radical_of_matrix
    intro r s hrs
    by_cases hh : s = 0 ∨ 2 ≤ r.val ∨ (r = 1 ∧ s = 1)
    · exact core_matrix (hcore hx) r s hh
    · push Not at hh
      have hr : r = 1 := by
        rcases hrs with hrs | hrs
        · exact (hh.1 (Fin.ext (by omega))).elim
        · apply Fin.ext; omega
      subst r
      have hs1 : s ≠ 1 := hh.2.2 rfl
      have hs : 2 ≤ s.val := by
        have h0 := hh.1
        have := s.isLt
        omega
      let j : Fin 3 := ⟨s.val-2,by omega⟩
      have hj : tailIndex j = s := Fin.ext (by dsimp [tailIndex,j]; omega)
      have hz := congrFun (second_row_zero Q hQ hc hQP hn ⟨x,hx⟩) j
      change matrix x 1 (tailIndex j) = 0 at hz
      rw [hj] at hz
      simpa only [if_neg (Ne.symm hs1)] using hz
  apply eq_of_le_of_card_ge hle
  rw [endpoint_card 0 (Or.inl rfl),hc]

 theorem no_standard_kernel (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16) (hQP : Q ≤ P)
    (hn : P ≤ normalizer (Q : Set (LinearGroup 5)))
    (hP : Nat.card P = 21504) :
    ¬ normalizer (Q : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 P).map P.subtype : Set (LinearGroup 5)) := by
  intro hres
  have he := kernel_eq_line Q hQ hc hQP hn
  rw [he,normalizer_radical (flagSpace_ne_bot standardBasis 0)] at hres
  apply endpoint_not_normalizes_residual standardBasis 0 (Or.inl rfl) P hP
    (flagStabilizer_antitone standardBasis (by simp))
  simpa only [flagStabilizer_singleton] using hres

 theorem no_kernel_of_equiv (J : Subgroup (LinearGroup 5)) (Q : Subgroup (LinearGroup 5))
    (a : MulAut (LinearGroup 5)) (hJ : J.map a.toMonoidHom = P)
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16) (hQJ : Q ≤ J)
    (hn : J ≤ normalizer (Q : Set (LinearGroup 5))) (hcard : Nat.card J = 21504) :
    ¬ normalizer (Q : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 J).map J.subtype : Set (LinearGroup 5)) := by
  intro hres
  have hn' : P ≤ normalizer (Q.map a.toMonoidHom : Set (LinearGroup 5)) := by
    rw [←hJ,←map_equiv_normalizer_eq]
    exact map_mono hn
  have hres' : normalizer (Q.map a.toMonoidHom : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 P).map P.subtype : Set (LinearGroup 5)) := by
    have hh := map_mono (f := a.toMonoidHom) hres
    rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq,map_embedded_pResidual,hJ] at hh
    exact hh
  exact no_standard_kernel (Q.map a.toMonoidHom) (hQ.map _)
    ((card_map_of_injective a.injective).trans hc)
    (hJ ▸ map_mono hQJ) hn'
    (by rw [← hJ,card_map_of_injective a.injective]; exact hcard) hres'

 public theorem no_first_kernel (b : FiveBasis) (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16)
    (hQP : Q ≤ flagStabilizer b {0,1})
    (hn : flagStabilizer b {0,1} ≤ normalizer (Q : Set (LinearGroup 5)))
    (hP : Nat.card (flagStabilizer b {0,1}) = 21504) :
    ¬ normalizer (Q : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 (flagStabilizer b {0,1})).map
        (flagStabilizer b {0,1}).subtype : Set (LinearGroup 5)) := by
  let a := MulAut.conj b.equivFun
  have hb : b.map b.equivFun = standardBasis := by
    ext i j
    simp [standardBasis,Module.Basis.equivFun_self,Pi.basisFun_apply,Pi.single_apply,eq_comm]
  have hp : (flagStabilizer b {0,1}).map a.toMonoidHom = P := by
    rw [flagStabilizer_map_conj,hb]
  exact no_kernel_of_equiv _ Q a hp hQ hc hQP hn hP

private theorem flagSpace_mono (b : FiveBasis) {i j : Fin 4} (hij : i ≤ j) :
    flagSpace b i ≤ flagSpace b j := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro k hk
  change k.val ≤ i.val at hk
  change k.val ≤ j.val
  exact hk.trans hij

 theorem last_to_first (b : FiveBasis) :
    ∃ a : MulAut (LinearGroup 5), (flagStabilizer b {2,3}).map a.toMonoidHom = P := by
  open InvariantNodeActions in
  have hAB : flagOrthogonal (flagSpace b 3) ≤ flagOrthogonal (flagSpace b 2) := by
    intro v hv
    apply (mem_flagOrthogonal _ _).mpr
    intro w hw
    exact (mem_flagOrthogonal _ _).mp hv w (flagSpace_mono b (by decide : (2 : Fin 4) ≤ 3) hw)
  let A := InvariantNodeActions.flagOrthogonal (flagSpace b 3)
  let B := InvariantNodeActions.flagOrthogonal (flagSpace b 2)
  obtain ⟨g,hgA,hgB⟩ := FourParabolicAction.exists_linearEquiv_map_flag A B
    (flagSpace standardBasis 0) (flagSpace standardBasis 1) hAB
    (flagSpace_mono standardBasis (by decide))
    (by dsimp [A]; rw [InvariantNodeActions.flagOrthogonal_finrank,finrank_flagSpace,finrank_flagSpace]; rfl)
    (by dsimp [B]; rw [InvariantNodeActions.flagOrthogonal_finrank,finrank_flagSpace,finrank_flagSpace]; rfl)
  let a := (graphLinear 5).trans (MulAut.conj g)
  have hm (W : Submodule (ZMod 2) (Space 5)) :
      (parabolic W).map a.toMonoidHom =
        parabolic ((InvariantNodeActions.flagOrthogonal W).map g.toLinearMap) := by
    change (parabolic W).map ((MulAut.conj g).toMonoidHom.comp (graphLinear 5).toMonoidHom) = _
    rw [←map_map,InvariantNodeActions.graph_map_parabolic,InvariantNodeActions.inner_map_parabolic]
  refine ⟨a,?_⟩
  have hp : flagStabilizer b {2,3} = parabolic (flagSpace b 2) ⊓ parabolic (flagSpace b 3) := by
    simp only [flagStabilizer, iInf_insert, iInf_singleton]
  rw [hp,Subgroup.map_inf _ _ _ a.injective,hm,hm,hgA,hgB]
  simp only [P,flagStabilizer,iInf_insert,iInf_singleton,inf_comm]

 public theorem no_last_kernel (b : FiveBasis) (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16)
    (hQP : Q ≤ flagStabilizer b {2,3})
    (hn : flagStabilizer b {2,3} ≤ normalizer (Q : Set (LinearGroup 5)))
    (hP : Nat.card (flagStabilizer b {2,3}) = 21504) :
    ¬ normalizer (Q : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 (flagStabilizer b {2,3})).map
        (flagStabilizer b {2,3}).subtype : Set (LinearGroup 5)) := by
  obtain ⟨a,ha⟩ := last_to_first b
  exact no_kernel_of_equiv _ Q a ha hQ hc hQP hn hP
end BinaryLinear.FivePointSection.AdjacentKernel
