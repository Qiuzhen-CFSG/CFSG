module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddAction
public import Theory.Representation.PSL3Two.NaturalDualRank
public import Theory.Representation.BinaryGroupAction
public import Theory.ElementaryAbelian.Quotient
public import Theory.Mathieu.M24.LargeElementaryPerfectNormalizer
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Kernel
import all Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Kernel

/-!
# Excluding the Mathieu placed component for the binary doubled orbit

The native Sylow catalogue puts every elementary subgroup of order 64 in
one of the two sextet or trio cores. The sextet normalizer has order prime
to seven. Perfectness kills the trio normalizer's permutation action on its
three octads. Its action on the two free translation vectors is therefore
the same on both coordinates, so swapping them gives a nonidentity commuting
linear automorphism. The natural-plus-dual SL₃(2) module has trivial invertible
commutant, excluding this alternative too.

The argument retains the entire six-space and an arbitrary perfect covering
actor; surjectivity onto the literal SL₃(2) supplies the factor seven. The
Chapter12 companion applies it through the original component's full center.
The private Kernel import only unfolds its translation equivalence to connect
the existing pointwise translation theorem; its public boundary is unchanged.
Source: Aschbacher--Smith 4.4.12 and its concluding local inspection, printed
pp.622--623, used in 7.3.4 and 7.6.1, pp.699,702, refs/quasithin.pdf; the
native trio module is H.14.1(3), pp.396--397, and Aschbacher, Sporadic Groups,
Lemma 20.2. The native Golay carrier and certificates are reused unchanged.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedMathieu
open Sporadic.Mathieu M24LocalGeometry M24ChapterHStabilizers
open PairOvergroups PairOvergroups.QuotientConstruction
open TrioAction

private def pairKernelEquiv : Multiplicative (Vector × Vector) ≃* Kernel :=
  translationPairEquiv.symm.toAddEquiv.toMultiplicative.trans translationEquiv

private theorem pair_point (v : Vector × Vector) (i : Fin 3) (w : Vector) :
    (pairKernelEquiv (Multiplicative.ofAdd v)).val.val.val (point (i,w)) =
      point (i,w + ![v.1,v.2,v.1+v.2] i) := translation_point _ _ _

private theorem pair_conjugation (g : Stabilizer)
    (hg : (affineQuotient affineCoverage g).1 = 1) (v : Vector × Vector) :
    g * (pairKernelEquiv (Multiplicative.ofAdd v)).val * g⁻¹ =
      (pairKernelEquiv (Multiplicative.ofAdd
        (Matrix.SpecialLinearGroup.toLin' (affineQuotient affineCoverage g).2 v.1,
         Matrix.SpecialLinearGroup.toLin' (affineQuotient affineCoverage g).2 v.2))).val := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  obtain ⟨t,ht⟩ := affineQuotient_spec affineCoverage g
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,w⟩,rfl⟩ := point.surjective x
  change g.val.val ((pairKernelEquiv (Multiplicative.ofAdd v)).val.val.val (point (i,w))) = _
  rw [pair_point,ht]
  change _ = (pairKernelEquiv _).val.val.val (g.val.val (point (i,w)))
  rw [ht,hg]
  change _ = (pairKernelEquiv _).val.val.val (point (i,_))
  rw [pair_point]
  let ℓ := Matrix.SpecialLinearGroup.toLin' (affineQuotient affineCoverage g).2
  have hl (j : Fin 3) : ℓ (![v.1,v.2,v.1+v.2] j) =
      ![ℓ v.1,ℓ v.2,ℓ v.1+ℓ v.2] j := by
    fin_cases j
    · rfl
    · rfl
    · exact ℓ.map_add _ _
  change point (i,ℓ (w + ![v.1,v.2,v.1+v.2] i) + t i) =
    point (i,ℓ w + t i + ![ℓ v.1,ℓ v.2,ℓ v.1+ℓ v.2] i)
  rw [map_add,hl,add_right_comm]

private def linearize {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : Multiplicative U ≃* Multiplicative V) : U ≃ₗ[ZMod 2] V :=
  let a : U ≃+ V := {
    toFun v := (e (Multiplicative.ofAdd v)).toAdd
    invFun v := (e.symm (Multiplicative.ofAdd v)).toAdd
    left_inv v := e.symm_apply_apply v
    right_inv v := e.apply_symm_apply v
    map_add' v w := congrArg Multiplicative.toAdd (e.map_mul
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  { a with map_smul' := ZMod.map_smul a }

private theorem no_trio_natural_dual
    {R : Type*} [Group R] [Group.IsPerfect R]
    (f : R →* Stabilizer) (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (u : Multiplicative BinaryLinearThree.NaturalDual.Space ≃* Kernel)
    (ha : ∀ r v, f r * (u (Multiplicative.ofAdd v)).val * (f r)⁻¹ =
      (u (Multiplicative.ofAdd (BinaryLinearThree.NaturalDual.action (q r) v))).val) : False := by
  let χ := (MonoidHom.fst (Equiv.Perm (Fin 3)) SL(3,ZMod 2)).comp
    ((affineQuotient affineCoverage).comp f)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsPerfect χ.range := Group.IsPerfect.range χ
  have hs : Subsingleton χ.range := by
    by_contra! h
    exact Group.IsPerfect.not_isSolvable χ.range inferInstance
  let := hs
  have hχ (r : R) : (affineQuotient affineCoverage (f r)).1 = 1 :=
    congrArg Subtype.val (Subsingleton.elim (χ.rangeRestrict r) 1)
  let e := linearize (u.trans pairKernelEquiv.symm)
  have he (r : R) (v : BinaryLinearThree.NaturalDual.Space) :
      e (BinaryLinearThree.NaturalDual.action (q r) v) =
        (Matrix.SpecialLinearGroup.toLin' (affineQuotient affineCoverage (f r)).2 (e v).1,
         Matrix.SpecialLinearGroup.toLin' (affineQuotient affineCoverage (f r)).2 (e v).2) := by
    apply Multiplicative.ofAdd.injective
    apply pairKernelEquiv.injective
    apply Subtype.ext
    have hv : pairKernelEquiv (Multiplicative.ofAdd (e v)) = u (Multiplicative.ofAdd v) :=
      pairKernelEquiv.apply_symm_apply _
    have hv' : pairKernelEquiv (Multiplicative.ofAdd
        (e (BinaryLinearThree.NaturalDual.action (q r) v))) =
        u (Multiplicative.ofAdd (BinaryLinearThree.NaturalDual.action (q r) v)) :=
      pairKernelEquiv.apply_symm_apply _
    rw [hv',←ha,←hv]
    exact pair_conjugation (f r) (hχ r) (e v)
  let s := e.trans ((LinearEquiv.prodComm (ZMod 2) Vector Vector).trans e.symm)
  have hc := BinaryLinearThree.NaturalDual.centralizer_eq_one s (by
    intro g v
    obtain ⟨r,rfl⟩ := hq g
    apply e.injective
    have hs (x) : e (s x) = Prod.swap (e x) := e.apply_symm_apply _
    rw [hs]
    rw [he,he]
    change _ = (_, _)
    simp [s])
  have hh := congrArg (fun a : BinaryLinearThree.NaturalDual.Space ≃ₗ[ZMod 2]
      BinaryLinearThree.NaturalDual.Space => e (a (e.symm ((fun _ => 1),0)))) hc
  dsimp only [s,LinearEquiv.trans_apply,LinearEquiv.refl_apply,LinearEquiv.prodComm_apply] at hh
  simp only [e.apply_symm_apply] at hh
  have hz := congrArg (fun x : Vector × Vector => x.1 0) hh
  exact zero_ne_one hz


/-- The whole natural–dual six-space cannot be normalized by its perfect
covering actor in the actual Mathieu group. -/
public theorem no_mathieu_natural_dual
    {R : Type*} [Group R] [Finite R] [Group.IsPerfect R]
    (f : R →* M24) (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (u : Multiplicative BinaryLinearThree.NaturalDual.Space →* M24)
    (hu : Function.Injective u)
    (ha : ∀ r v, f r * u (Multiplicative.ofAdd v) * (f r)⁻¹ =
      u (Multiplicative.ofAdd (BinaryLinearThree.NaturalDual.action (q r) v))) : False := by
  let E := u.range
  let : IsElementaryAbelian 2 (Multiplicative BinaryLinearThree.NaturalDual.Space) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    u.rangeRestrict u.rangeRestrict_surjective
  have hE : Nat.card E = 64 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hu).toEquiv]
    change Nat.card BinaryLinearThree.NaturalDual.Space = 64
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2)]
    norm_num [BinaryLinearThree.NaturalDual.Space,Module.finrank_prod]
  have hnorm : f.range ≤ normalizer (E : Set M24) := by
    apply le_set_normalizer_iff.mpr
    rintro _ ⟨r,rfl⟩ _ ⟨v,rfl⟩
    exact ⟨Multiplicative.ofAdd (BinaryLinearThree.NaturalDual.action (q r) v.toAdd),
      (ha r v.toAdd).symm⟩
  have hk : f.rangeRestrict.ker ≤ q.ker := by
    intro r hr
    have hfr : f r = 1 := congrArg Subtype.val hr
    apply BinaryLinearThree.NaturalDual.action_injective
    apply LinearMap.ext
    intro v
    have he := ha r v
    rw [hfr,one_mul,inv_one,mul_one] at he
    have hh := congrArg Multiplicative.toAdd (hu he)
    change v = BinaryLinearThree.NaturalDual.action (q r) v at hh
    simpa only [map_one,Module.End.one_apply] using hh.symm
  let qB : f.range →* BinaryLinearThree.Group :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q,hk⟩
  have hqB : Function.Surjective qB := by
    intro g
    obtain ⟨r,rfl⟩ := hq g
    exact ⟨f.rangeRestrict r,by simp [qB]⟩
  have hseven : 7 ∣ Nat.card f.range := by
    have hh := card_dvd_of_surjective qB hqB
    rw [Matrix.PSL3Two.card_SL] at hh
    exact (by decide : 7 ∣ 168).trans hh
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  let a := MulAut.conj g
  let U := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.toMonoidHom
  have hUP : U ≤ SylowNormalizer.candidate := by
    have hh := map_mono (f:=a.toMonoidHom) hES
    change U ≤ (g • S : Sylow 2 M24) at hh
    rw [hg] at hh
    exact hh
  have hUc : Nat.card U = 64 := (card_map_of_injective a.injective).trans hE
  obtain htrio | hsextet := ElementaryFusion.elementary_card64_eq_candidate U hUc hUP
  · let c := MulAut.conj (FourNormalizers.certificateElement 0)
    let b := a.trans c
    let j := b.toMonoidHom.comp u
    let k := b.toMonoidHom.comp f
    have hj : Function.Injective j := b.injective.comp hu
    have hN : (normalizer (E : Set M24)).map b.toMonoidHom = Stabilizer := by
      change (normalizer (E : Set M24)).map (c.toMonoidHom.comp a.toMonoidHom) = _
      rw [←map_map,map_equiv_normalizer_eq]
      change (normalizer (U : Set M24)).map c.toMonoidHom = _
      rw [htrio]
      exact EvenCatalogue.NormalSeeds.trio_normalizer_map_eq
    have hjN : normalizer (j.range : Set M24) = Stabilizer := by
      rw [MonoidHom.range_comp,←map_equiv_normalizer_eq]
      exact hN
    have hjE : j.range = core := by
      have hp : IsPGroup 2 j.range := by
        rw [MonoidHom.range_comp]
        exact (IsElementaryAbelian.isPGroup 2 E).map b.toMonoidHom
      have hle : j.range ≤ core := le_pCoreIn_of_normalizes hp
        (j.range.le_normalizer.trans hjN.le) hjN.symm.le
      apply eq_of_le_of_card_ge hle
      rw [core_ambient_card,MonoidHom.range_comp,card_map_of_injective b.injective]
      exact hE.ge
    have hkN : k.range ≤ Stabilizer := by
      rw [MonoidHom.range_comp,←hN]
      exact map_mono hnorm
    let kN : R →* Stabilizer := k.codRestrict _ (fun r => hkN ⟨r,rfl⟩)
    let v : Multiplicative BinaryLinearThree.NaturalDual.Space ≃* Kernel :=
      ((MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjE)).trans
        (Kernel.equivMapOfInjective Stabilizer.subtype Stabilizer.subtype_injective).symm
    have hv (x) : ((v x).val : M24) = j x := by
      have hh := (Kernel.equivMapOfInjective Stabilizer.subtype
        Stabilizer.subtype_injective).apply_symm_apply
        (((MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjE)) x)
      exact congrArg Subtype.val hh
    apply no_trio_natural_dual kN q hq v
    intro r x
    apply Subtype.ext
    change k r * ((v (Multiplicative.ofAdd x)).val : M24) * (k r)⁻¹ = _
    rw [hv,hv]
    dsimp only [k,j,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
    simpa only [map_mul,map_inv] using congrArg b (ha r x)
  · have hBN : f.range.map a.toMonoidHom ≤ EvenCandidates.localGroup 1 := by
      have hh := (map_mono (f:=a.toMonoidHom) hnorm).trans (le_normalizer_map a.toMonoidHom)
      change f.range.map a.toMonoidHom ≤ normalizer (U : Set M24) at hh
      rw [hsextet] at hh
      exact hh
    have hd : 7 ∣ Nat.card (EvenCandidates.localGroup 1) := by
      have hh := card_dvd_of_le hBN
      rw [card_map_of_injective a.injective] at hh
      exact hseven.trans hh
    rw [Nat.card_congr EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.toEquiv,
      SextetCore.stabilizer_card] at hd
    norm_num at hd

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedMathieu
