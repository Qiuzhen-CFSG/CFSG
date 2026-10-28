module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.ComponentRank.Radical
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Short
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Long
public import Theory.GroupTheory.CComponent.SylowCentral
public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import FeitThompson.FinalTheorem

/-!
# Confinement of the permuted-component G₂ branch

A rank-one radical-quotient actor over a field of degree greater than one
has a nontrivial two-core kernel. Intersecting the two-core with the normal
model subgroup and applying the actual octonion normalizer-cover theorem
places H intersect L in a conjugate of either full parabolic.

The image of H intersect L in H/O∞(H) is normal. If its Sylow two-subgroups
are abelian, its two-elements normalize every component: a component either
centralizes this normal subgroup or lies inside it, where an abelian Sylow
fixes a nonidentity element of the centerless component. The Odd Order Theorem
supplies the required even order. This rules out the permutation alternative.

The final theorem instantiates the actual radical quotient equivalences for
both full parabolics, completing this branch without additional model premises.
It retains the source's local tau orbit; the normalization argument in fact
applies to every quotient component. Only normality of the model copy is
needed, so arbitrary ambient outer two-extensions are included. No choice of
a specified parabolic, outer splitting, or weak-closure premise is assumed.

Source: Aschbacher--Smith, E.1.2(E2.2), E.1.5, printed p.210, and E.1.14(1),
printed p.214, citing Asc82a Lemma 4.7. The octonion model is from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank.PermutationGeometry

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
/-- A nontrivial intrinsic kernel produces a conjugate-parabolic placement of
the literal model intersection, through the normalizer of O₂(H) intersect L. -/
theorem socle_intersection_parabolic_of_kernel
    (L : Subgroup G) (e : L ≃* Model F) {A H : Subgroup G}
    (hAL : A ≤ L)
    (hker : A.subgroupOf H ⊓ pCore 2 H ≠ ⊥) :
    ∃ g : Model F,
      ((H.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
      ((H.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ parabolic₂ := by
  let P := ((pCore 2 H).map H.subtype).subgroupOf L
  have hp : IsPGroup 2 P := (pCore_isPGroup.map H.subtype).comap_subtype
  have hP : P ≠ ⊥ := by
    intro hb
    apply hker
    apply bot_unique
    intro x hx
    let y : L := ⟨x.val, hAL hx.1⟩
    have hy : y ∈ P := ⟨x, hx.2, rfl⟩
    have hy1 : y = 1 := mem_bot.mp (hb ▸ hy)
    change x = 1
    exact Subtype.ext (congrArg (fun z : L => (z : G)) hy1)
  have hn : H.subgroupOf L ≤ normalizer (P : Set L) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    obtain ⟨z, hz, he⟩ := hy
    let xh : H := ⟨x.val, hx⟩
    refine ⟨xh * z * xh⁻¹, (inferInstance : (pCore 2 H).Normal).conj_mem z hz xh, ?_⟩
    change x.val * z.val * x.val⁻¹ = x.val * y.val * x.val⁻¹
    change z.val = y.val at he
    rw [he]
  have hmN : (H.subgroupOf L).map e.toMonoidHom ≤
      normalizer ((P.map e.toMonoidHom : Subgroup (Model F)) : Set (Model F)) :=
    (map_mono hn).trans (P.le_normalizer_map e.toMonoidHom)
  have hmP : P.map e.toMonoidHom ≠ ⊥ := by
    intro hb
    exact hP ((P.map_eq_bot_iff_of_injective e.injective).mp hb)
  obtain ⟨g, hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    (P.map e.toMonoidHom) hmP (hp.map e.toMonoidHom)
  exact ⟨g, hg.imp ((map_mono hmN).trans) ((map_mono hmN).trans)⟩

/-- The source rank-one alternative supplies the nontrivial kernel needed for
normalizer coverage. The family is the full ambient orbit. -/
theorem socle_intersection_parabolic_of_rank_one
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) = 1) :
    ∃ g : Model F,
      ((H.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
      ((H.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ parabolic₂ := by
  exact socle_intersection_parabolic_of_kernel L e (family_le_socle L e hA)
    (proper_core_kernel_of_rank_lt L e hA hm hc hF (hr ▸ hf)).1

omit [Field F] [Finite F] [CharP F 2] in
private theorem normalizes_components_of_abelian_sylow
    {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hX : solvableRadical X = ⊥)
    (hab : ∀ S : Sylow 2 N, IsMulCommutative S)
    (B : Subgroup X) (hBN : B ≤ N) (hB : IsPGroup 2 B)
    (D : Subgroup X) (hD : IsComponent X D) : B ≤ normalizer (D : Set X) := by
  rcases hD.normal_dichotomy N with hDN | hcomm
  · have hN : solvableRadical N = ⊥ :=
      solvableRadical_eq_bot_of_isSubnormal hX (inferInstance : N.Normal).isSubnormal
    have hDn := hD.subgroupOf hDN
    have hc : (D.subgroupOf N).IsCComponent :=
      (isCComponent_iff_isSubnormal_and_isQuasisimple_of_solvableRadical_eq_bot hN).mpr hDn
    let _ := hDn.2
    let _ : IsSimpleGroup (D.subgroupOf N) :=
      hc.isSimpleGroup_of_solvableRadical_eq_bot hN
    have hd : 2 ∣ Nat.card (D.subgroupOf N) := by
      by_contra hd
      have ho : Odd (Nat.card (D.subgroupOf N)) :=
        Nat.not_even_iff_odd.mp (fun he => hd (even_iff_two_dvd.mp he))
      exact Group.IsPerfect.not_isSolvable _ (odd_order_theorem _ ho)
    obtain ⟨S, hS⟩ := (hB.comap_subtype (K := N)).exists_le_sylow
    let _ := hab S
    intro b hb
    have hbS : (⟨b, hBN hb⟩ : N) ∈ S := hS hb
    have hn : (⟨b, hBN hb⟩ : N) ∈ normalizer (D.subgroupOf N : Set N) :=
      hc.mem_normalizer_of_centralizes_sylow hN hd S (fun s => by
        exact congrArg Subtype.val (mul_comm (⟨⟨b, hBN hb⟩, hbS⟩ : S) s))
    rwa [← subgroupOf_normalizer_eq hDN] at hn
  · rw [commutator_comm] at hcomm
    exact hBN.trans ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _))

omit [Field F] [Finite F] [CharP F 2] in
private theorem abelian_sylow_of_equiv {X Y : Type*} [Group X] [Finite X]
    [Group Y] (e : X ≃* Y) (hab : ∀ S : Sylow 2 Y, IsMulCommutative S) :
    ∀ S : Sylow 2 X, IsMulCommutative S := by
  intro S
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let _ := hab U
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply e.injective
  simp only [map_mul, Subgroup.coe_mul]
  exact congrArg Subtype.val (mul_comm
    (⟨e x, mem_map_of_mem e.toMonoidHom x.property⟩ : U)
    (⟨e y, mem_map_of_mem e.toMonoidHom y.property⟩ : U))


omit [Finite F] [CharP F 2] in
/-- Abelian Sylow subgroups of the intrinsic socle-intersection radical quotient
force the literal source actor to normalize every quotient component. -/
theorem actor_normalizes_of_socle_abelian_sylow
    (L : Subgroup G) [L.Normal] (e : L ≃* Atlas.G2.Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e) (hm : IsEMember T A H)
    (hab : ∀ S : Sylow 2 ((L.subgroupOf H) ⧸ solvableRadical (L.subgroupOf H)),
      IsMulCommutative S)
    (D : Subgroup (H ⧸ solvableRadical H)) (hD : IsComponent _ D) :
    (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H)) ≤
      normalizer (D : Set (H ⧸ solvableRadical H)) := by
  let N := L.subgroupOf H
  let q := QuotientGroup.mk' (solvableRadical H)
  let B := (A.subgroupOf H).map q
  let _ := hm.1
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hm.2.2.1
  have hp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 (A.subgroupOf H)).map q
  have hAN : A.subgroupOf H ≤ N := fun _ hx => family_le_socle L e hA hx
  have hB : B ≤ N.map q := map_mono hAN
  have he := normalRadicalQuotientEquivImage N
  have hcomm : ∀ S : Sylow 2 (N.map q), IsMulCommutative S :=
    abelian_sylow_of_equiv he.symm hab
  exact normalizes_components_of_abelian_sylow (N.map q)
    solvableRadical_quotient_solvableRadical hcomm B hB hp D hD

private def intersectionEquiv (L H : Subgroup G) : L.subgroupOf H ≃* H.subgroupOf L where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

open Atlas.G2 Atlas.G2.LieParabolicSetup

/-- Conditional confinement from abelian Sylow two-subgroups of all full
parabolic radical sections. This independent model premise remains explicit. -/
theorem confinement_of_parabolic_sections
    (hsections : ∀ J : Subgroup (Model F), (J ≤ parabolic₁ ∨ J ≤ parabolic₂) →
      ∀ S : Sylow 2 (J ⧸ solvableRadical J), IsMulCommutative S)
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (D : Subgroup (H ⧸ solvableRadical H)) (hD : IsComponent _ D)
    (hperm : ¬ (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H)) ≤
      normalizer (D : Set (H ⧸ solvableRadical H)))
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) = 1) :
    H ≤ shortOvergroup L T e := by
  obtain ⟨g, hg⟩ := socle_intersection_parabolic_of_rank_one L e hA hm hc hf hF hr
  let N := L.subgroupOf H
  let J := ((H.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
  let b : N ≃* J := (intersectionEquiv L H).trans
    ((e.subgroupMap (H.subgroupOf L)).trans
      ((MulAut.conj g).subgroupMap ((H.subgroupOf L).map e.toMonoidHom)))
  let bq : (N ⧸ solvableRadical N) ≃* (J ⧸ solvableRadical J) :=
    QuotientGroup.congr _ _ b (map_solvableRadical_equiv b)
  have hab : ∀ S : Sylow 2 (N ⧸ solvableRadical N), IsMulCommutative S :=
    abelian_sylow_of_equiv bq (hsections J hg)
  exact (hperm (actor_normalizes_of_socle_abelian_sylow L e hA hm hab D hD)).elim


private theorem abelian_sylow_image {X Y : Type*} [Group X] [Finite X]
    [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (hab : ∀ S : Sylow 2 X, IsMulCommutative S) :
    ∀ S : Sylow 2 Y, IsMulCommutative S := by
  intro S
  obtain ⟨U, rfl⟩ := Sylow.mapSurjective_surjective hf 2 S
  let _ := hab U
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨u, hu, heu⟩ := x.property
  obtain ⟨v, hv, hev⟩ := y.property
  apply Subtype.ext
  change x.val * y.val = y.val * x.val
  rw [← heu, ← hev, ← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val (mul_comm (⟨u, hu⟩ : U) (⟨v, hv⟩ : U)))

private theorem abelian_sylow_subgroup {X : Type*} [Group X] [Finite X]
    (hab : ∀ S : Sylow 2 X, IsMulCommutative S) (J : Subgroup X) :
    ∀ S : Sylow 2 J, IsMulCommutative S := by
  intro S
  obtain ⟨U, hU⟩ := (S.2.map J.subtype).exists_le_sylow
  let _ := hab U
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val * y.val.val = y.val.val * x.val.val
  exact congrArg (fun u : U => (u : X)) (mul_comm
    (⟨x.val.val, hU (mem_map_of_mem J.subtype x.property)⟩ : U)
    (⟨y.val.val, hU (mem_map_of_mem J.subtype y.property)⟩ : U))

private theorem section_sylow {X : Type*} [Group X] [Finite X]
    (P J : Subgroup X) (hJP : J ≤ P)
    (hab : ∀ S : Sylow 2 (P ⧸ solvableRadical P), IsMulCommutative S) :
    ∀ S : Sylow 2 (J ⧸ solvableRadical J), IsMulCommutative S := by
  let i := inclusion hJP
  let f := (QuotientGroup.mk' (solvableRadical P)).comp i
  let k : f.rangeRestrict.ker →* solvableRadical P :=
    (i.comp f.rangeRestrict.ker.subtype).codRestrict _ (by
      intro x
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val x.property)
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply (inclusion_injective hJP)
    exact congrArg Subtype.val h
  let _ : Group.IsSolvable f.rangeRestrict.ker :=
    Group.isSolvable_of_isSolvable_injective hk
  let b := solvableRadicalQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  apply abelian_sylow_of_equiv b
  exact abelian_sylow_image (QuotientGroup.mk' (solvableRadical f.range))
    (QuotientGroup.mk'_surjective _) (abelian_sylow_subgroup hab f.range)

private theorem psl_sylow {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    ∀ S : Sylow 2 PSL(2,F), IsMulCommutative S := by
  let _ := Fintype.ofFinite F
  intro S
  obtain ⟨d⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF S
  refine ⟨⟨fun x y => d.symm.injective ?_⟩⟩
  simp only [map_mul]
  exact mul_comm _ _

/-- Conditional source assembly from the two full-parabolic quotient calculations.
The quotient equivalences are supplied by the existing short- and long-parabolic
model owners; they are not constructed by this theorem. -/
theorem confinement_of_full_parabolic_quotients
    (e₁ : (parabolic₁ (F := F) ⧸ solvableRadical (parabolic₁ (F := F))) ≃* PSL(2,F))
    (e₂ : (parabolic₂ (F := F) ⧸ solvableRadical (parabolic₂ (F := F))) ≃* PSL(2,F))
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (D : Subgroup (H ⧸ solvableRadical H)) (hD : IsComponent _ D)
    (hperm : ¬ (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H)) ≤
      normalizer (D : Set (H ⧸ solvableRadical H)))
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) = 1) :
    H ≤ shortOvergroup L T e := by
  apply confinement_of_parabolic_sections ?_ L e hA hm hc hf hF D hD hperm hr
  intro J hJ
  rcases hJ with hJ | hJ
  · exact section_sylow parabolic₁ J hJ (abelian_sylow_of_equiv e₁ (psl_sylow hF))
  · exact section_sylow parabolic₂ J hJ (abelian_sylow_of_equiv e₂ (psl_sylow hF))

/-- The permuted-component geometric premise of the G₂ rank obstruction.
Both full-parabolic radical quotient identifications are discharged by the
concrete model constructions. The displayed orbit is the literal local tau
orbit required by `rank_lower_bound_of_component_geometry`; normality of L
suffices, without simplicity, Sylow alignment, or restrictions on outer actions. -/
theorem confinement
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (D : Subgroup (H ⧸ solvableRadical H)) (hD : IsComponent _ D)
    (_horbit : componentLayer (H ⧸ solvableRadical H) = conjugateJoin
      ((tau (T.subgroupOf H) (A.subgroupOf H)).map
        (QuotientGroup.mk' (solvableRadical H))) D)
    (hperm : ¬ (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H)) ≤
      normalizer (D : Set (H ⧸ solvableRadical H)))
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) = 1) :
    H ≤ shortOvergroup L T e := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa only [pow_one] using (Nat.pow_lt_pow_right (by decide : 1 < 2) hf)
  exact confinement_of_full_parabolic_quotients
    (HigherParabolicRadical.Short.parabolic₁RadicalQuotientEquivPSL hq)
    (HigherParabolicRadical.Long.parabolic₂RadicalQuotientEquivPSL hq)
    L e hA hm hc hf hF D hD hperm hr

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank.PermutationGeometry
