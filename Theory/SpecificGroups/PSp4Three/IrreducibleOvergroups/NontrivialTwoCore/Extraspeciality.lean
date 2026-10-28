module

public import Theory.GroupTheory.PGroup.RankTwoSymplecticType
public import Theory.GroupTheory.PGroup.SymplecticRotationDichotomy
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.CoreLift
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Representation
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.ExtendScalars
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Extraspecial lift cores from two symplectic centralizer calculations

For a nonsolvable subgroup of PSp₄(3), the faithful four-dimensional action of
its full preimage embeds the automizer of each abelian two-subgroup in S₄.
Consequently the centralizer of such a normal subgroup cannot be solvable.
Solvability of centralizers of noncentral involutions and of order-four elements
with central square therefore forces every normal abelian two-subgroup into the
scalar kernel: first its involutions are scalar, then elements of order four
are excluded, and the two-group power condition finishes the argument.

The scalar kernel has order at most two. Thus all characteristic abelian
subgroups of the lift core have order at most two. Hall's symplectic-type theorem
makes its central quotient elementary abelian: the alternative large rotation
has a characteristic cyclic square subgroup of order at least four, a
contradiction. The nontrivial projective core makes the lift core larger than
two; its nontrivial center then has exactly two elements, and its central
quotient is nontrivial. These are all three clauses of `IsExtraspecial`.

The final theorem is conditional on the two concrete centralizer calculations.
It uses no maximal-subgroup list, recognition by order, or global classification.
Once those calculations are supplied, maximality, irreducibility and the
rank-two bound in the motivating application are unnecessary for this step.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed
p.4 (and the repeated statement on p.482) of `refs/quasithin.pdf`.
Hall's theorem and its rotation alternative are proved in the imported
finite-two-group modules; the weight automizer argument is the one underlying
Aschbacher–Smith, Lemma A.3.21(c), printed pp.55–56.
-/

namespace Matrix.PSp4Three.NontrivialTwoCore

open Subgroup
open scoped TensorProduct


private theorem card_dvd_two {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A ≤ 2) : Nat.card A ∣ 2 := by
  have hp : 0 < Nat.card A := Nat.card_pos
  have h : Nat.card A = 1 ∨ Nat.card A = 2 := by omega
  rcases h with h | h <;> simp [h]

private theorem small_characteristic_abelian_extraspecial
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hlarge : 2 < Nat.card P)
    (hchar : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A →
      Nat.card A ≤ 2) : IsExtraspecial 2 P := by
  have hcyc (A : Subgroup P) (hc : A.Characteristic) (ha : IsMulCommutative A) :
      IsCyclic A := isCyclic_of_card_dvd_prime (p := 2) (card_dvd_two (hchar A hc ha))
  let : IsCyclic (center P) := hcyc (center P) inferInstance inferInstance
  have hZle := hchar (center P) inferInstance inferInstance
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial (center P) := hP.center_nontrivial
  have hZ : Nat.card (center P) = 2 := by
    have h := Finite.one_lt_card (α := center P)
    omega
  have hquot : IsElementaryAbelian 2 (P ⧸ center P) := by
    rcases IsBinarySymplecticType.elementary_central_quotient_or_large_rotation hP
      (hP.isBinarySymplecticType_of_characteristic_abelian hcyc) with h | ⟨r, hr, _, _, hsq, _⟩
    · exact h
    · have hR : (zpowers (r ^ 2)).Characteristic := by
        apply characteristic_iff_le_comap.mpr
        intro f
        apply zpowers_le.mpr
        change f (r ^ 2) ∈ zpowers (r ^ 2)
        rw [map_pow]
        exact hsq (f r)
      have hcard := card_dvd_two (hchar (zpowers (r ^ 2)) hR inferInstance)
      rw [Nat.card_zpowers] at hcard
      have hp : r ^ 4 = 1 := by
        simpa only [← pow_mul] using (orderOf_dvd_iff_pow_eq_one.mp hcard)
      have hbad := hr.trans (orderOf_dvd_of_pow_eq_one hp)
      norm_num at hbad
  refine {
    center_order_p := hZ
    quotient_elementary_abelian := hquot
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr ?_ }
  intro htop
  have h := Nat.card_congr (Subgroup.topEquiv (G := P)).toEquiv
  rw [← htop, hZ] at h
  omega

private theorem solvable_of_normal_abelian_centralizer
    (M : Subgroup (PSp 2 (ZMod 3))) (A : Subgroup (fullPreimage M))
    [A.Normal] [IsMulCommutative A]
    [Group.IsSolvable (centralizer (A : Set (fullPreimage M)))]
    (hA : IsPGroup 2 A) : Group.IsSolvable (fullPreimage M) := by
  let E := AlgebraicClosure (ZMod 3)
  let rho := (fullPreimageRepresentation M).extendScalars E
  have hf : Function.Injective rho :=
    (Representation.extendScalars_faithful_iff E _).mp
      (fullPreimageRepresentation_injective M)
  have horder : (Nat.card A : E) ≠ 0 := by
    obtain ⟨n, hn⟩ := hA.exists_card_eq
    rw [hn, Nat.cast_pow]
    apply pow_ne_zero
    intro h
    have he : algebraMap (ZMod 3) E (2 : ZMod 3) = algebraMap (ZMod 3) E 0 := by
      simpa only [map_ofNat, map_zero, Nat.cast_ofNat] using h
    have he' := (algebraMap (ZMod 3) E).injective he
    exact (by decide : (2 : ZMod 3) ≠ 0) he'
  have hdim : Module.finrank E (E ⊗[ZMod 3] Vector 2 (ZMod 3)) ≤ 4 := by
    simp only [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_sum,
      Fintype.card_fin]
    decide
  obtain ⟨j, hj⟩ := Representation.automizer_embeds_perm_of_abelian rho A hf horder 4 hdim
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable A.normalizerMonoidHom.range :=
    Group.isSolvable_of_isSolvable_injective hj
  have hk : A.normalizerMonoidHom.rangeRestrict.ker =
      (centralizer (A : Set (fullPreimage M))).subgroupOf (normalizer (A : Set (fullPreimage M))) := by
    rw [MonoidHom.ker_rangeRestrict, A.normalizerMonoidHom_ker]
  let : Group.IsSolvable A.normalizerMonoidHom.rangeRestrict.ker := by
    rw [hk]
    let e := subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set (fullPreimage M)))
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hn : Group.IsSolvable (normalizer (A : Set (fullPreimage M))) :=
    Group.isSolvable_of_ker_le_range A.normalizerMonoidHom.rangeRestrict.ker.subtype
      A.normalizerMonoidHom.rangeRestrict (by rw [range_subtype])
  rw [normalizer_eq_top] at hn
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.topEquiv (G := fullPreimage M)).toMonoidHom)
    (Subgroup.topEquiv (G := fullPreimage M)).surjective

private theorem nonsolvable_element_centralizer
    (M : Subgroup (PSp 2 (ZMod 3))) (hn : ¬ Group.IsSolvable M)
    (A : Subgroup (fullPreimage M)) [A.Normal] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (t : A) :
    ¬ Group.IsSolvable (centralizer ({t.val.val} : Set (Sp 2 (ZMod 3)))) := by
  intro ht
  let C := centralizer (A : Set (fullPreimage M))
  let j : C →* centralizer ({t.val.val} : Set (Sp 2 (ZMod 3))) :=
    ((fullPreimage M).subtype.comp C.subtype).codRestrict _ (fun g => by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val ((g.property t.val t.property).symm))
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : centralizer ({t.val.val} : Set (Sp 2 (ZMod 3))) => z.val) h
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective hj
  exact fullPreimage_not_isSolvable M hn (solvable_of_normal_abelian_centralizer M A hA)

variable
    (h₂ : ∀ t : Sp 2 (ZMod 3), t ^ 2 = 1 → t ∉ center (Sp 2 (ZMod 3)) →
      Group.IsSolvable (centralizer ({t} : Set (Sp 2 (ZMod 3)))))
    (h₄ : ∀ t : Sp 2 (ZMod 3), orderOf t = 4 → t ^ 2 ∈ center (Sp 2 (ZMod 3)) →
      Group.IsSolvable (centralizer ({t} : Set (Sp 2 (ZMod 3)))))

include h₂ h₄ in
/-- If the two indicated ambient centralizers are solvable, every normal abelian
two-subgroup of a nonsolvable full preimage lies in the actual scalar kernel. -/
public theorem normal_abelian_two_subgroup_le_kernel_of_centralizers
    (M : Subgroup (PSp 2 (ZMod 3))) (hn : ¬ Group.IsSolvable M)
    (A : Subgroup (fullPreimage M)) [A.Normal] [IsMulCommutative A]
    (hA : IsPGroup 2 A) : A ≤ (preimageProjection M).ker := by
  have hinvol (t : A) (ht : t ^ 2 = 1) : t.val.val ∈ center (Sp 2 (ZMod 3)) := by
    by_contra hc
    exact nonsolvable_element_centralizer M hn A hA t
      (h₂ t.val.val (congrArg (fun a : A => a.val.val) ht) hc)
  have hfour (t : A) : orderOf t ≠ 4 := by
    intro ht
    have hp : t ^ 4 = 1 := ht ▸ pow_orderOf_eq_one t
    have hs := hinvol (t ^ 2) (by simpa only [← pow_mul] using hp)
    exact nonsolvable_element_centralizer M hn A hA t
      (h₄ t.val.val (by simpa only [orderOf_coe] using ht) hs)
  intro a ha
  let t : A := ⟨a, ha⟩
  obtain ⟨n, hn⟩ := hA.exists_orderOf_eq_pow t
  have hnle : n ≤ 1 := by
    by_contra h
    have hd : 4 ∣ orderOf t := by
      rw [hn]
      exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ n)
    exact hfour (t ^ (orderOf t / 4))
      (orderOf_pow_orderOf_div (orderOf_pos t).ne' hd)
  have ht : t ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hn]
    exact Nat.pow_dvd_pow 2 hnle
  have hc := hinvol t ht
  apply Subtype.ext
  exact (QuotientGroup.eq_one_iff _).mpr hc

private theorem scalar_center_card_le_two : Nat.card (center (Sp 2 (ZMod 3))) ≤ 2 := by
  classical
  have hs (g : center (Sp 2 (ZMod 3))) :
      ∃ a : ZMod 3, a * a = 1 ∧ ∀ x : Vector 2 (ZMod 3), g.val • x = a • x := by
    obtain ⟨a, ha⟩ := central_is_scalar g.val g.property
    refine ⟨a, ?_, ha⟩
    have h := congrArg (fun z : Sp 2 (ZMod 3) => z • e (n := 2) (F := ZMod 3) 0)
      (central_square_eq_one g.val g.property)
    have h' := congrFun h (.inl 0)
    simpa only [pow_two, mul_smul, ha, Pi.smul_apply, smul_eq_mul,
      e, Pi.single_eq_same, one_smul, mul_one] using h'
  choose a ha hh using hs
  let j : center (Sp 2 (ZMod 3)) → {a : ZMod 3 // a * a = 1} := fun g => ⟨a g, ha g⟩
  have hj : Function.Injective j := by
    intro g h he
    have he' : a g = a h := congrArg Subtype.val he
    apply Subtype.ext
    apply ext_action
    intro x
    rw [hh, hh, he']
  have hc : Nat.card {a : ZMod 3 // a * a = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [hc] using Nat.card_le_card_of_injective j hj

private theorem projection_kernel_card_le_two (M : Subgroup (PSp 2 (ZMod 3))) :
    Nat.card (preimageProjection M).ker ≤ 2 := by
  let j : (preimageProjection M).ker → center (Sp 2 (ZMod 3)) := fun g =>
    ⟨g.val.val, by
      apply (show (projection (n := 2) (F := ZMod 3)).ker ≤ center (Sp 2 (ZMod 3)) from
        projection_kernel.le)
      exact congrArg Subtype.val g.property⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center (Sp 2 (ZMod 3)) => z.val) h
  exact (Nat.card_le_card_of_injective j hj).trans scalar_center_card_le_two

/-- Scalar normal abelian two-subgroups force extraspeciality of a lift core
strictly larger than the scalar kernel. Hall's theorem constructs the elementary
central quotient; the center order and quotient nontriviality are proved separately. -/
public theorem lift_core_extraspecial_of_normal_abelian_scalar
    (M : Subgroup (PSp 2 (ZMod 3))) (hn : pCore 2 M ≠ ⊥)
    (hab : ∀ A : Subgroup (fullPreimage M), A.Normal → IsMulCommutative A →
      IsPGroup 2 A → A ≤ (preimageProjection M).ker) :
    IsExtraspecial 2 (pCore 2 (fullPreimage M)) := by
  let P := pCore 2 (fullPreimage M)
  have hchar (A : Subgroup P) (hc : A.Characteristic) (ha : IsMulCommutative A) :
      Nat.card A ≤ 2 := by
    let B := A.map P.subtype
    have hb : B.Normal := ConjAct.normal_of_characteristic_of_normal
    have hB := hab B hb inferInstance ((pCore_isPGroup.to_subgroup A).map P.subtype)
    rw [← card_map_of_injective P.subtype_injective (K := A)]
    exact (card_le_of_le hB).trans (projection_kernel_card_le_two M)
  have hlarge : 2 < Nat.card P := by
    by_contra h
    have hc : IsCyclic P := isCyclic_of_card_dvd_prime (p := 2) (card_dvd_two (by omega))
    let : IsCyclic P := hc
    exact fullPreimage_twoCore_not_le_kernel M hn
      (hab P inferInstance inferInstance pCore_isPGroup)
  exact small_characteristic_abelian_extraspecial pCore_isPGroup hlarge hchar

/-- The lift-core problem reduces to centralizers of noncentral involutions and
order-four elements with central square in the actual symplectic matrix group.
The two centralizer premises remain explicit obligations. -/
public theorem lift_core_extraspecial_of_small_centralizers
    (h₂ : ∀ t : Sp 2 (ZMod 3), t ^ 2 = 1 → t ∉ center (Sp 2 (ZMod 3)) →
      Group.IsSolvable (centralizer ({t} : Set (Sp 2 (ZMod 3)))))
    (h₄ : ∀ t : Sp 2 (ZMod 3), orderOf t = 4 → t ^ 2 ∈ center (Sp 2 (ZMod 3)) →
      Group.IsSolvable (centralizer ({t} : Set (Sp 2 (ZMod 3)))))
    (M : Subgroup (PSp 2 (ZMod 3))) (hn : ¬ Group.IsSolvable M)
    (hcore : pCore 2 M ≠ ⊥) : IsExtraspecial 2 (pCore 2 (fullPreimage M)) := by
  apply lift_core_extraspecial_of_normal_abelian_scalar M hcore
  intro A hAn hAa hA
  let := hAn
  let := hAa
  exact normal_abelian_two_subgroup_le_kernel_of_centralizers h₂ h₄ M hn A hA


end Matrix.PSp4Three.NontrivialTwoCore
