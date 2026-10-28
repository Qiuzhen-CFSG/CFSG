module
public import Theory.SpecificGroups.BinaryLinear.FivePointSection.MiddleKernel
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.OuterInvariantFlags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.PerfectImage
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneResidual

/-!
# The binary-five normalizer obstruction at a nonsingular point

An elementary subgroup of order 64 normalized by a full Sylow subgroup,
with seven dividing its normalizer, has no outer normalizing automorphism.
After Sylow conjugacy, a proposed outer actor preserves a symmetric flag.
The only nonsolvable proper choice is the 1+3+1 flag. Its normal elementary
subgroups have order at most 16: the row and column cannot both be nonzero,
as a short GL3 word then gives a noncommuting conjugate.

The matrix coordinates below adapt the private calculations in
`BinaryLinear.FivePointSection.MiddleKernel`; their public boundary is
preserved. The finite certificate checks only 64 row/column pairs.
`LinearFiveComponent` applies the obstruction to the literal component
central quotient and the full original point action.
Source: Aschbacher--Smith 12.1.1, printed p.788; Theorem C, pp.32--33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular.LinearFive
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups BinaryLinear.InvariantNodeActions
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
open BinaryLinear.FivePointSection BinaryLinear.FivePointSection.MiddleKernel
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private noncomputable abbrev P := flagStabilizer standardBasis {0,3}

set_option backward.isDefEq.respectTransparency false in
private theorem core_matrix {g : LinearGroup 5} (hg : g ∈ P.pCoreIn 2)
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

private noncomputable def entries (g : LinearGroup 5) : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  (fun i => matrix g 0 ⟨i.val+1,by omega⟩,
   fun i => matrix g ⟨i.val+1,by omega⟩ 4)

private theorem root_mem (i j : Fin 3) (hij : i ≠ j) :
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

private def middle (i : Fin 3) : Fin 5 := ⟨i.val+1,by omega⟩

private theorem middle_injective : Function.Injective middle := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  change i.val+1 = j.val+1 at hh
  omega

private noncomputable def actor (a : Fin 6) : LinearGroup 5 :=
  root (middle (KernelOrbit.indices a).1) (middle (KernelOrbit.indices a).2)
    (middle_injective.ne (by revert a; decide))

private theorem actor_mem (a : Fin 6) : actor a ∈ P := root_mem _ _ (by revert a; decide)

private theorem matrix_mul (x y : LinearGroup 5) : matrix (x*y) = matrix x * matrix y :=
  matrixHom.map_mul x y

private theorem entries_conj (a : Fin 6) (x : LinearGroup 5) :
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


private def pairing (x y : BinaryLinear.FivePointSection.KernelOrbit.Pair) : ZMod 2 :=
  dotProduct x.1 y.2 + dotProduct y.1 x.2

private theorem axis_certificate (x : BinaryLinear.FivePointSection.KernelOrbit.Pair)
    (h : ∀ a b : Fin 6, pairing x
      (BinaryLinear.FivePointSection.KernelOrbit.act a
        (BinaryLinear.FivePointSection.KernelOrbit.act b x)) = 0) :
    x.1 = 0 ∨ x.2 = 0 := by
  revert x
  decide +kernel

private theorem core_shape {x : LinearGroup 5} (hx : x ∈ P.pCoreIn 2) :
    matrix x = !![1,matrix x 0 1,matrix x 0 2,matrix x 0 3,matrix x 0 4;
      0,1,0,0,matrix x 1 4; 0,0,1,0,matrix x 2 4;
      0,0,0,1,matrix x 3 4; 0,0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact core_matrix hx _ _ (by decide)

private theorem pairing_eq_zero {x y : LinearGroup 5}
    (hx : x ∈ P.pCoreIn 2) (hy : y ∈ P.pCoreIn 2) (h : x*y = y*x) :
    pairing (entries x) (entries y) = 0 := by
  have hh := congrArg (fun g => matrix g 0 4) h
  rw [matrix_mul,matrix_mul,core_shape hx,core_shape hy] at hh
  simp [Matrix.mul_apply,Fin.sum_univ_succ] at hh
  change matrix x 0 1 * matrix y 1 4 +
    (matrix x 0 2 * matrix y 2 4 + (matrix x 0 3 * matrix y 3 4 + 0)) +
    (matrix y 0 1 * matrix x 1 4 +
      (matrix y 0 2 * matrix x 2 4 + (matrix y 0 3 * matrix x 3 4 + 0))) = 0
  linear_combination (norm := ring_nf) hh
  simp only [show (2 : ZMod 2) = 0 from rfl,mul_zero,add_zero]

/-- The original 1+3+1 parabolic has no normal elementary subgroup larger than sixteen. -/
theorem middle_normal_elementary_card (E : Subgroup (LinearGroup 5))
    [IsElementaryAbelian 2 E] (hEP : E ≤ flagStabilizer standardBasis {0,3})
    (hPE : flagStabilizer standardBasis {0,3} ≤ normalizer (E : Set (LinearGroup 5))) : Nat.card E ≤ 16 := by
  have hcore : E ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 E) hEP hPE
  have haxis (x : E) : (entries x.val).1 = 0 ∨ (entries x.val).2 = 0 := by
    apply axis_certificate
    intro a b
    let g := actor a * actor b
    have hg : g ∈ P := P.mul_mem (actor_mem a) (actor_mem b)
    have hy : g*x.val*g⁻¹ ∈ E := (mem_normalizer_iff.mp (hPE hg) x.val).mp x.property
    have hh := pairing_eq_zero (hcore x.property) (hcore hy)
      (congrArg Subtype.val (mul_comm x (⟨_,hy⟩ : E)))
    have he : entries (g*x.val*g⁻¹) =
        BinaryLinear.FivePointSection.KernelOrbit.act a
          (BinaryLinear.FivePointSection.KernelOrbit.act b (entries x.val)) := by
      rw [show g*x.val*g⁻¹ = actor a * (actor b*x.val*(actor b)⁻¹) * (actor a)⁻¹ by
        dsimp [g]; group,entries_conj,entries_conj]
    rwa [he] at hh
  let f : E → {p : BinaryLinear.FivePointSection.KernelOrbit.Pair // p.1 = 0 ∨ p.2 = 0} × ZMod 2 :=
    fun x => (⟨entries x.val,haxis x⟩,matrix x.val 0 4)
  have hf : Function.Injective f := by
    intro x y he
    have hp := congrArg (fun z : {p : BinaryLinear.FivePointSection.KernelOrbit.Pair // p.1 = 0 ∨ p.2 = 0} × ZMod 2 => z.1.val) he
    have hc := congrArg Prod.snd he
    apply Subtype.ext
    apply matrix_injective
    rw [core_shape (hcore x.property),core_shape (hcore y.property)]
    have h01 := congrArg (fun p : BinaryLinear.FivePointSection.KernelOrbit.Pair => p.1 0) hp
    have h02 := congrArg (fun p : BinaryLinear.FivePointSection.KernelOrbit.Pair => p.1 1) hp
    have h03 := congrArg (fun p : BinaryLinear.FivePointSection.KernelOrbit.Pair => p.1 2) hp
    have h14 := congrArg (fun p : BinaryLinear.FivePointSection.KernelOrbit.Pair => p.2 0) hp
    have h24 := congrArg (fun p : BinaryLinear.FivePointSection.KernelOrbit.Pair => p.2 1) hp
    have h34 := congrArg (fun p : BinaryLinear.FivePointSection.KernelOrbit.Pair => p.2 2) hp
    change matrix x.val 0 1 = matrix y.val 0 1 at h01
    change matrix x.val 0 2 = matrix y.val 0 2 at h02
    change matrix x.val 0 3 = matrix y.val 0 3 at h03
    change matrix x.val 1 4 = matrix y.val 1 4 at h14
    change matrix x.val 2 4 = matrix y.val 2 4 at h24
    change matrix x.val 3 4 = matrix y.val 3 4 at h34
    change matrix x.val 0 4 = matrix y.val 0 4 at hc
    rw [h01,h02,h03,h14,h24,h34,hc]
  have hb : Nat.card E ≤ 30 := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod,Nat.card_zmod] at hh
    have hc : Nat.card {p : BinaryLinear.FivePointSection.KernelOrbit.Pair // p.1 = 0 ∨ p.2 = 0} = 15 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rwa [hc] at hh
  obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hd4 : d ≤ 4 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 5 ≤ d by omega)
    rw [hd] at hb
    omega
  rw [hd]
  exact Nat.pow_le_pow_right (by decide) hd4

private theorem middle_normal_elementary_card_basis (b : FiveBasis)
    (E : Subgroup (LinearGroup 5)) [IsElementaryAbelian 2 E]
    (hEP : E ≤ flagStabilizer b {0,3})
    (hPE : flagStabilizer b {0,3} ≤ normalizer (E : Set (LinearGroup 5))) : Nat.card E ≤ 16 := by
  let a := MulAut.conj b.equivFun
  have hPa : (flagStabilizer b {0,3}).map a.toMonoidHom = P := by
    rw [flagStabilizer_map_conj]
    change flagStabilizer _ _ = flagStabilizer standardBasis _
    congr 1
    ext i j
    simp [standardBasis,Module.Basis.equivFun_self,Pi.basisFun_apply,Pi.single_apply,eq_comm]
  let E' := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map a.toMonoidHom
  have hh := middle_normal_elementary_card E' (by change E' ≤ P; rw [←hPa]; exact map_mono hEP)
    (by change P ≤ normalizer (E' : Set _); rw [←hPa]; exact (map_mono hPE).trans (le_normalizer_map a.toMonoidHom))
  rwa [card_map_of_injective a.injective] at hh

private theorem interior_seven_free (b : FiveBasis) :
    ¬ 7 ∣ Nat.card (flagStabilizer b {1,2}) := by
  let H := flagStabilizer b {1,2}
  have hc : Nat.card (H ⧸ pCore 2 H) = 36 := by
    rw [Nat.card_congr (flagDiagonalQuotientEquiv b {1,2}).toEquiv,Nat.card_pi]
    simp_rw [coordinateLinear_card]
    have hl : cutLabel ({1,2} : Set (Fin 4)) = ![0,0,1,2,2] := by
      ext i
      fin_cases i <;> simp [cutLabel,
        show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide,
        Finset.filter_insert,Finset.filter_singleton]
    rw [hl]
    decide
  obtain ⟨d,hd⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have he := (pCore 2 H).card_mul_index
  change Nat.card (pCore 2 H) * Nat.card (H ⧸ pCore 2 H) = Nat.card H at he
  rw [hd,hc] at he
  rw [←he]
  exact (by decide : Nat.Prime 7).not_dvd_mul
    (fun hh => (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow hh)) (by decide)

/-- A Sylow-preserving outer automorphism cannot normalize a sixty-four-group
whose normalizer has a factor seven. -/
theorem normalizing_sylow_actor_inner (S : Sylow 2 (LinearGroup 5))
    (E : Subgroup (LinearGroup 5)) [IsElementaryAbelian 2 E]
    (hc : Nat.card E = 64) (hSN : (S : Subgroup _) ≤ normalizer (E : Set (LinearGroup 5)))
    (hseven : 7 ∣ Nat.card (normalizer (E : Set (LinearGroup 5))))
    (a : MulAut (LinearGroup 5)) (haE : E.map a.toMonoidHom = E)
    (haS : (S : Subgroup (LinearGroup 5)).map a.toMonoidHom = S) :
    a ∈ MulAut.innerSubgroup (LinearGroup 5) := by
  by_contra hout
  let N := normalizer (E : Set (LinearGroup 5))
  have hN : N ≠ ⊤ := by
    intro ht
    let : E.Normal := normalizer_eq_top_iff.mp ht
    have hle : E ≤ pCore 2 (LinearGroup 5) :=
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 E⟩
    rw [linearGroup_twoCore_eq_bot] at hle
    have he : E = ⊥ := bot_unique hle
    rw [he,card_bot] at hc
    omega
  have haN : N.map a.toMonoidHom = N := by
    rw [map_equiv_normalizer_eq,haE]
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  rcases outer_invariant_overgroup (.inr rfl) S b hb a hout haS N hSN hN haN with hNS | hNP | hNI
  · have hs : ¬ 7 ∣ Nat.card S := by
      obtain ⟨d,hd⟩ := S.isPGroup'.exists_card_eq
      rw [hd]
      exact fun hh => (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow hh)
    exact hs (hNS ▸ hseven)
  · have he : ({i : Fin 4 | i.val = 0 ∨ i.val = 4-1} : Set (Fin 4)) = {0,3} := by
      ext i; fin_cases i <;> simp
    change N = flagStabilizer b _ at hNP
    rw [he] at hNP
    have hb := middle_normal_elementary_card_basis b E (hNP ▸ E.le_normalizer) hNP.symm.le
    omega
  · have he : ({i : Fin 4 | i.val = 0 ∨ i.val = 4-1}ᶜ : Set (Fin 4)) = {1,2} := by
      ext i; fin_cases i <;> simp
    change N = flagStabilizer b _ at hNI
    rw [he] at hNI
    exact interior_seven_free b (hNI ▸ hseven)

/-- Every automorphism normalizing the original elementary sixty-four-group is inner. -/
theorem normalizing_actor_inner (S : Sylow 2 (LinearGroup 5))
    (E : Subgroup (LinearGroup 5)) [IsElementaryAbelian 2 E]
    (hc : Nat.card E = 64) (hSN : (S : Subgroup _) ≤ normalizer (E : Set (LinearGroup 5)))
    (hseven : 7 ∣ Nat.card (normalizer (E : Set (LinearGroup 5))))
    (a : MulAut (LinearGroup 5)) (haE : E.map a.toMonoidHom = E) :
    a ∈ MulAut.innerSubgroup (LinearGroup 5) := by
  let N := normalizer (E : Set (LinearGroup 5))
  have haN : N.map a.toMonoidHom = N := by rw [map_equiv_normalizer_eq,haE]
  let aN : MulAut N := (a.subgroupMap N).trans (MulEquiv.subgroupCongr haN)
  let R := S.subtype hSN
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq N (R.mapSurjective (f := aN.toMonoidHom) aN.surjective) R
  let c := MulAut.conj (g : LinearGroup 5)
  let b := c*a
  have hbS : (S : Subgroup (LinearGroup 5)).map b.toMonoidHom = S := by
    have hh := congrArg (fun X : Sylow 2 N => (X : Subgroup N).map N.subtype) hg
    change (((R : Subgroup N).map aN.toMonoidHom).map (MulAut.conj g).toMonoidHom).map N.subtype =
      (R : Subgroup N).map N.subtype at hh
    have he : N.subtype.comp ((MulAut.conj g).toMonoidHom.comp aN.toMonoidHom) =
        b.toMonoidHom.comp N.subtype := by ext x; rfl
    rw [map_map,map_map] at hh
    change map (N.subtype.comp ((MulAut.conj g).toMonoidHom.comp aN.toMonoidHom)) (R : Subgroup N) = _ at hh
    rw [he,←map_map] at hh
    have hR : (R : Subgroup N).map N.subtype = (S : Subgroup (LinearGroup 5)) :=
      map_subgroupOf_eq_of_le hSN
    rwa [hR] at hh
  have hbE : E.map b.toMonoidHom = E := by
    change E.map (c.toMonoidHom.comp a.toMonoidHom) = E
    rw [←map_map,haE]
    exact mem_normalizer_iff_map_conj_eq.mp g.property
  have hb := normalizing_sylow_actor_inner S E hc hSN hseven b hbE hbS
  have hc : c ∈ MulAut.innerSubgroup (LinearGroup 5) := ⟨g,rfl⟩
  have hh := (MulAut.innerSubgroup (LinearGroup 5)).mul_mem
    ((MulAut.innerSubgroup (LinearGroup 5)).inv_mem hc) hb
  simpa only [b,inv_mul_cancel_left] using hh
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular.LinearFive
