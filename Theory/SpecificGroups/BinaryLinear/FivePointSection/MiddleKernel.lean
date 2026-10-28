module
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.Endpoints
public import Theory.SpecificGroups.BinaryLinear.LineRadical
public import Theory.SpecificGroups.BinaryLinear.PointParabolicSection
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.BinaryLinear.FivePointSection.KernelOrbit
/-!
# Normal sixteen-groups in the binary five-space transvection flag

In the standard 1+3+1 flag, the two-core has one row, one column and a
central corner coordinate. Conjugation by its GL₃(2) block and the checked
row-column orbit bound force every element of a normal sixteen-group onto
one axis. A subgroup contained in the union of two subgroups is contained
in one, so equality of orders identifies an endpoint radical.

Its normalizer is the endpoint parabolic. That parabolic cannot normalize
the original two-residual: a normal subgroup with a factor seven in a
group with GL₄(2) two-core quotient must have a factor nine, whereas the
original flag has order 21504. Basis conjugation preserves the literal
kernel and residual, so the final exclusion applies to any marking.

Source: Aschbacher--Smith, 12.9.6, printed pp.861--862. The actual mixed
point-section application is NaturalSource/LocalControl/MixedKernel.
-/

section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.FivePointSection.MiddleKernel
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups SmallParabolicLevi.TwoNodes
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

noncomputable abbrev P := flagStabilizer standardBasis {0,3}

set_option backward.isDefEq.respectTransparency false in
theorem core_matrix {g : LinearGroup 5} (hg : g ∈ P.pCoreIn 2)
    (i j : Fin 5) (hij : j = 0 ∨ i = 4 ∨ (i ≠ 0 ∧ j ≠ 4)) :
    matrix g i j = if i = j then 1 else 0 := by
  have hc : cutLabel ({0,3} : Set (Fin 4)) = ![0,1,1,1,2] := by
    ext k
    fin_cases k <;> simp [cutLabel, show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide, Finset.filter_insert, Finset.filter_singleton]
  have hh : ∀ r s : Fin 5, cutLabel ({0,3} : Set (Fin 4)) s ≤ cutLabel ({0,3} : Set (Fin 4)) r →
      matrix g r s = if r = s then 1 else 0 := by
    unfold P at hg
    rw [← triangularGroup_cutLabel] at hg
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hg
    rw [← ker_diagonalAction_eq_twoCore _ (cutLabel_monotone _)] at hx
    intro r s hrs
    rcases hrs.eq_or_lt with he | he
    · have hb := blockMatrix_eq_one_of_mem_ker _ x hx (cutLabel ({0,3} : Set (Fin 4)) r)
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

noncomputable def entries (g : LinearGroup 5) : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  (fun i => matrix g 0 ⟨i.val+1,by omega⟩,
   fun i => matrix g ⟨i.val+1,by omega⟩ 4)

public noncomputable def root (i j : Fin 5) (hij : i ≠ j) : LinearGroup 5 :=
  slEquivLinear 5 (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2))

public theorem matrix_root (i j : Fin 5) (hij : i ≠ j) :
    matrix (root i j hij) = 1 + Matrix.single i j 1 := by
  simp [matrix,root,Matrix.SpecialLinearGroup.transvection_coe]

public theorem root_inv (i j : Fin 5) (hij : i ≠ j) : (root i j hij)⁻¹ = root i j hij := by
  apply (slEquivLinear 5).symm.injective
  simp [root, Matrix.SpecialLinearGroup.transvection_inv]

 theorem root_mem (i j : Fin 3) (hij : i ≠ j) :
    root ⟨i.val+1,by omega⟩ ⟨j.val+1,by omega⟩ (by intro he; apply hij; exact Fin.ext (by simpa using congrArg Fin.val he)) ∈ P := by
  rw [mem_standard_flagStabilizer_iff, matrix_root]
  intro k hk r s hkr hsk
  rcases hk with rfl | hk
  · simp only [Fin.val_zero,Nat.le_zero] at hsk
    have hs : s = 0 := Fin.ext hsk
    have hrs : r ≠ s := by intro he; subst s; omega
    have hjs : (⟨j.val+1,by omega⟩ : Fin 5) ≠ s := by intro he; have heq := congrArg Fin.val he; change j.val+1 = s.val at heq; omega
    simp [Matrix.add_apply,hrs,hjs]
  · have he : k = 3 := Set.mem_singleton_iff.mp hk
    subst k
    have hr : r = 4 := Fin.ext (by change 3 < r.val at hkr; omega)
    have hrs : r ≠ s := by intro he; subst s; change r.val ≤ 3 at hsk; omega
    have hir : (⟨i.val+1,by omega⟩ : Fin 5) ≠ r := by intro he; have heq := congrArg Fin.val he; change i.val+1 = r.val at heq; rw [hr] at heq; change i.val+1 = 4 at heq; omega
    simp [Matrix.add_apply,hrs,hir]

def middle (i : Fin 3) : Fin 5 := ⟨i.val+1,by omega⟩

theorem middle_injective : Function.Injective middle := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  change i.val+1 = j.val+1 at hh
  omega

noncomputable def actor (a : Fin 6) : LinearGroup 5 :=
  root (middle (KernelOrbit.indices a).1) (middle (KernelOrbit.indices a).2)
    (middle_injective.ne (by revert a; decide))

theorem actor_mem (a : Fin 6) : actor a ∈ P := root_mem _ _ (by revert a; decide)

private theorem matrix_mul (x y : LinearGroup 5) : matrix (x*y) = matrix x * matrix y :=
  matrixHom.map_mul x y

theorem entries_conj (a : Fin 6) (x : LinearGroup 5) :
    entries (actor a * x * (actor a)⁻¹) = KernelOrbit.act a (entries x) := by
  have hm : matrix (actor a * x * (actor a)⁻¹) =
      (1 + Matrix.single (middle (KernelOrbit.indices a).1) (middle (KernelOrbit.indices a).2) 1) *
        matrix x *
      (1 + Matrix.single (middle (KernelOrbit.indices a).1) (middle (KernelOrbit.indices a).2) 1) := by
    rw [actor,root_inv,matrix_mul,matrix_mul,matrix_root]
  apply Prod.ext <;> funext k
  all_goals
    simp only [entries,KernelOrbit.act,hm]
    fin_cases a <;> fin_cases k <;>
      simp [KernelOrbit.indices,middle,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single_apply,Matrix.one_apply] <;> ring

 theorem entries_axis (Q : Subgroup (LinearGroup 5))
    (hc : Nat.card Q = 16) (hn : P ≤ normalizer (Q : Set (LinearGroup 5)))
    (x : Q) : (entries x).1 = 0 ∨ (entries x).2 = 0 := by
  by_contra hh
  push Not at hh
  have hs : ∀ a y, y ∈ Set.range (fun q : Q => entries q.val) →
      KernelOrbit.act a y ∈ Set.range (fun q : Q => entries q.val) := by
    rintro a y ⟨q,rfl⟩
    exact ⟨⟨_,((hn (actor_mem a)) q.val).mp q.property⟩,entries_conj a q.val⟩
  have hbound := KernelOrbit.large_image (fun q : Q => entries q.val) hs x hh.1 hh.2
  omega

public theorem radical_of_matrix (g : LinearGroup 5) (k : Fin 4)
    (hm : ∀ r s : Fin 5, s.val ≤ k.val ∨ k.val < r.val →
      matrix g r s = if r = s then 1 else 0) : g ∈ radical (flagSpace standardBasis k) := by
  have he (v : Space 5) (r : Fin 5)
      (hv : v ∈ flagSpace standardBasis k ∨ k.val < r.val) : g v r = v r := by
    rw [← matrix_mulVec]
    change ∑ s, matrix g r s * v s = v r
    calc
      _ = ∑ s : Fin 5, (if r = s then 1 else 0) * v s := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s.val ≤ k.val
        · rw [hm r s (Or.inl hs)]
        · rcases hv with hv | hr
          · rw [(mem_standard_flagSpace_iff k v).mp hv s (by omega)]
            simp
          · rw [hm r s (Or.inr hr)]
      _ = v r := by simp
  constructor
  · intro v hv
    funext r
    exact he v r (Or.inl hv)
  · intro v
    apply (mem_standard_flagSpace_iff k _).mpr
    intro r hr
    change g v r - v r = 0
    rw [he v r (Or.inr hr),sub_self]

 theorem axis_radical {g : LinearGroup 5} (hg : g ∈ P.pCoreIn 2) :
    ((entries g).1 = 0 → g ∈ radical (flagSpace standardBasis 3)) ∧
    ((entries g).2 = 0 → g ∈ radical (flagSpace standardBasis 0)) := by
  constructor
  · intro ha
    apply radical_of_matrix
    intro r s hrs
    by_cases hh : s = 0 ∨ r = 4 ∨ (r ≠ 0 ∧ s ≠ 4)
    · exact core_matrix hg r s hh
    · push Not at hh
      have hr : r = 0 := by
        by_contra hr0
        have hs4 := hh.2.2 hr0
        subst s
        rcases hrs with hrs | hrs <;> omega
      subst r
      have hs : s.val < 4 := by rcases hrs with hrs | hrs <;> omega
      let j : Fin 3 := ⟨s.val-1,by have := s.isLt; omega⟩
      have hj : (⟨j.val+1,by omega⟩ : Fin 5) = s := Fin.ext (by dsimp [j]; have := hh.1; have := s.isLt; omega)
      have he := congrFun ha j
      change matrix g 0 ⟨j.val+1,by omega⟩ = 0 at he
      rw [hj] at he
      simpa only [if_neg (Ne.symm hh.1)] using he
  · intro hb
    apply radical_of_matrix
    intro r s hrs
    by_cases hh : s = 0 ∨ r = 4 ∨ (r ≠ 0 ∧ s ≠ 4)
    · exact core_matrix hg r s hh
    · push Not at hh
      have hs : s = 4 := by
        apply hh.2.2
        intro hr
        subst r
        rcases hrs with hrs | hrs
        · exact hh.1 (Fin.ext (by omega))
        · omega
      subst s
      have hr : 0 < r.val := by rcases hrs with hrs | hrs <;> omega
      let j : Fin 3 := ⟨r.val-1,by have := r.isLt; have h4 := hh.2.1; omega⟩
      have hj : (⟨j.val+1,by omega⟩ : Fin 5) = r := Fin.ext (by dsimp [j]; omega)
      have he := congrFun hb j
      change matrix g ⟨j.val+1,by omega⟩ 4 = 0 at he
      rw [hj] at he
      simpa only [if_neg hh.2.1] using he

private theorem subgroup_le_or_le {A B C : Subgroup (LinearGroup 5)}
    (h : ∀ x ∈ A, x ∈ B ∨ x ∈ C) : A ≤ B ∨ A ≤ C := by
  by_cases hb : A ≤ B
  · exact Or.inl hb
  · right
    obtain ⟨x,hx,hxb⟩ := SetLike.not_le_iff_exists.mp hb
    have hxc := (h x hx).resolve_left hxb
    intro y hy
    rcases h y hy with hyb | hyc
    · rcases h (x*y) (A.mul_mem hx hy) with hxyb | hxyc
      · exact (hxb (by simpa using B.mul_mem hxyb (B.inv_mem hyb))).elim
      · simpa using C.mul_mem (C.inv_mem hxc) hxyc
    · exact hyc

 theorem kernel_le_endpoint (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16) (hQP : Q ≤ P)
    (hn : P ≤ normalizer (Q : Set (LinearGroup 5))) :
    Q ≤ radical (flagSpace standardBasis 0) ∨ Q ≤ radical (flagSpace standardBasis 3) := by
  have hcore : Q ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes hQ hQP hn
  apply subgroup_le_or_le
  intro x hx
  rcases entries_axis Q hc hn ⟨x,hx⟩ with ha | hb
  · exact Or.inr ((axis_radical (hcore hx)).1 ha)
  · exact Or.inl ((axis_radical (hcore hx)).2 hb)

 public theorem endpoint_card (k : Fin 4) (hk : k = 0 ∨ k = 3) :
    Nat.card (radical (flagSpace standardBasis k)) = 16 := by
  rcases hk with rfl | rfl
  · rw [flagSpace_zero,LineRadical.card _ (standardBasis.ne_zero 0)]
    norm_num [Space]
  · rw [flagSpace_last]
    have hf : standardBasis.coord 4 ≠ 0 := by
      intro he
      have hh := LinearMap.congr_fun he (standardBasis 4)
      simp [Module.Basis.coord_apply] at hh
    obtain ⟨v,hv,he⟩ := graph_hyperplaneRadical (Or.inr rfl) (standardBasis.coord 4) hf
    have hc := card_map_of_injective (f := (graphLinear 5).toMonoidHom) (K := hyperplaneRadical 5 (standardBasis.coord 4)) (graphLinear 5).injective
    rw [he] at hc
    change Nat.card (hyperplaneRadical 5 (standardBasis.coord 4)) = 16
    rw [← hc]
    change Nat.card (radical (Submodule.span (ZMod 2) {v})) = 16
    exact (LineRadical.card v hv).trans (by norm_num [Space])

 theorem kernel_eq_endpoint (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16) (hQP : Q ≤ P)
    (hn : P ≤ normalizer (Q : Set (LinearGroup 5))) :
    Q = radical (flagSpace standardBasis 0) ∨ Q = radical (flagSpace standardBasis 3) := by
  rcases kernel_le_endpoint Q hQ hc hQP hn with hle | hle
  · exact Or.inl (eq_of_le_of_card_ge hle (by rw [endpoint_card 0 (Or.inl rfl),hc]))
  · exact Or.inr (eq_of_le_of_card_ge hle (by rw [endpoint_card 3 (Or.inr rfl),hc]))
end BinaryLinear.FivePointSection.MiddleKernel
section
open Subgroup
namespace BinaryLinear.FivePointSection
open OuterCyclic FiveFlagGeometry
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

public theorem normal_seven_forces_nine {D : Type*} [Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* LinearGroup 4)
    (R : Subgroup D) [R.Normal] (h7 : 7 ∣ Nat.card R) : 9 ∣ Nat.card R := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 4 (by decide)
  let : IsSimpleGroup (LinearGroup 4) := (projectiveEquivLinear (by decide : 0<4)).symm.isSimpleGroup
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : (R.map q).Normal := Subgroup.Normal.map inferInstance q hq
  rcases (inferInstance : (R.map q).Normal).eq_bot_or_eq_top with he | he
  · have hR : R ≤ pCore 2 D := by
      rw [← hqk, ← Subgroup.map_eq_bot_iff]
      exact he
    obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le hR).exists_card_eq
    rw [hk] at h7
    have hh := (by decide : Nat.Prime 7).dvd_of_dvd_pow h7
    norm_num at hh
  · have hc : Nat.card (LinearGroup 4) = 20160 := by
      rw [← Nat.card_congr (matrixEquivLinear 4).toEquiv,Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    have hd := card_dvd_of_surjective (q.comp R.subtype)
      (MonoidHom.range_eq_top.mp (by rw [MonoidHom.range_comp,range_subtype]; exact he))
    rw [hc] at hd
    exact (by decide : 9 ∣ 20160).trans hd

 public theorem seven_dvd_residual (J : Subgroup (LinearGroup 5)) (hc : Nat.card J = 21504) :
    7 ∣ Nat.card ((pResidual 2 J).map J.subtype) := by
  rw [card_map_of_injective J.subtype_injective]
  have h7 : 7 ∣ Nat.card J := hc ▸ (by decide : 7 ∣ 21504)
  obtain ⟨k,hk⟩ := (isPGroup_quotient_pResidual (G := J) 2).exists_card_eq
  rw [← (pResidual 2 J).card_mul_index,index_eq_card,hk] at h7
  exact ((by decide : Nat.Coprime 7 2).pow_right k).dvd_of_dvd_mul_right h7

 public theorem endpoint_not_normalizes_residual (b : FiveBasis) (k : Fin 4)
    (hk : k = 0 ∨ k = 3) (J : Subgroup (LinearGroup 5))
    (hc : Nat.card J = 21504) (hJ : J ≤ flagStabilizer b {k}) :
    ¬ flagStabilizer b {k} ≤ normalizer ((pResidual 2 J).map J.subtype : Set (LinearGroup 5)) := by
  intro hn
  let P := flagStabilizer b {k}
  let R := (pResidual 2 J).map J.subtype
  have hRP : R ≤ P := (map_subtype_le _).trans hJ
  let : (R.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hRP).mpr hn
  have he : Nonempty ((P ⧸ pCore 2 P) ≃* LinearGroup 4) := by
    rcases hk with rfl | rfl
    · exact ⟨(MaximalOvergroups.lineQuotientEquiv b).trans (projectiveEquivLinear (by decide : 0<4))⟩
    · exact ⟨(MaximalOvergroups.hyperplaneQuotientEquiv b).trans (projectiveEquivLinear (by decide : 0<4))⟩
  obtain ⟨e⟩ := he
  have hr : Nat.card (R.subgroupOf P) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRP).toEquiv
  have h9 := normal_seven_forces_nine e (R.subgroupOf P) (hr ▸ seven_dvd_residual J hc)
  rw [hr] at h9
  have hd := h9.trans (card_dvd_of_le (show R ≤ J from map_subtype_le _))
  rw [hc] at hd
  norm_num at hd
end BinaryLinear.FivePointSection

namespace BinaryLinear.FivePointSection.MiddleKernel
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups
 theorem no_standard_kernel (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16) (hQP : Q ≤ P)
    (hn : P ≤ normalizer (Q : Set (LinearGroup 5)))
    (hP : Nat.card P = 21504) :
    ¬ normalizer (Q : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 P).map P.subtype : Set (LinearGroup 5)) := by
  intro hres
  rcases kernel_eq_endpoint Q hQ hc hQP hn with he | he
  · rw [he,normalizer_radical (flagSpace_ne_bot standardBasis 0)] at hres
    apply endpoint_not_normalizes_residual standardBasis 0 (Or.inl rfl) P hP
      (flagStabilizer_antitone standardBasis (by simp))
    simpa only [flagStabilizer_singleton] using hres
  · rw [he,normalizer_radical (flagSpace_ne_bot standardBasis 3)] at hres
    apply endpoint_not_normalizes_residual standardBasis 3 (Or.inr rfl) P hP
      (flagStabilizer_antitone standardBasis (by simp))
    simpa only [flagStabilizer_singleton] using hres

 public theorem no_middle_kernel (b : FiveBasis) (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 16)
    (hQP : Q ≤ flagStabilizer b {0,3})
    (hn : flagStabilizer b {0,3} ≤ normalizer (Q : Set (LinearGroup 5)))
    (hP : Nat.card (flagStabilizer b {0,3}) = 21504) :
    ¬ normalizer (Q : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 (flagStabilizer b {0,3})).map
        (flagStabilizer b {0,3}).subtype : Set (LinearGroup 5)) := by
  intro hres
  let a := MulAut.conj b.equivFun
  have hb : b.map b.equivFun = standardBasis := by
    ext i j
    simp [standardBasis,Module.Basis.equivFun_self,Pi.basisFun_apply,Pi.single_apply,eq_comm]
  have hp : (flagStabilizer b {0,3}).map a.toMonoidHom = P := by
    rw [flagStabilizer_map_conj,hb]
  have hn' : P ≤ normalizer (Q.map a.toMonoidHom : Set (LinearGroup 5)) := by
    rw [←hp,←map_equiv_normalizer_eq]
    exact map_mono hn
  have hres' : normalizer (Q.map a.toMonoidHom : Set (LinearGroup 5)) ≤
      normalizer ((pResidual 2 P).map P.subtype : Set (LinearGroup 5)) := by
    have hh := map_mono (f := a.toMonoidHom) hres
    rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq,map_embedded_pResidual,hp] at hh
    exact hh
  exact no_standard_kernel (Q.map a.toMonoidHom) (hQ.map _) 
    ((card_map_of_injective a.injective).trans hc)
    (hp ▸ map_mono hQP) hn'
    (by rw [← hp,card_map_of_injective a.injective]; exact hP) hres'
end BinaryLinear.FivePointSection.MiddleKernel
