module
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.SpecificGroups.SL2.PrimePlaneAction
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Sylow-radical normalizers in the elementary SL₂ extension

In a perfect nonquasisimple extension of SL₂(p) by an elementary plane,
the quotient conjugation action is nontrivial: otherwise the extension is
a perfect central cover and hence quasisimple. The prime-plane action
lemma therefore makes every lift of the central involution invert the
literal odd kernel. A Sylow subgroup of the radical contains such a lift.
Its normalizer intersects the odd kernel trivially, so the radical
intersection embeds into the two-group center of SL₂(p).

This is the intrinsic kernel calculation used by the actual residual
projection in the companion source application. No splitting or natural
action marking of the extension is assumed.
Source: Aschbacher--Smith, 11.4.2, printed p.777, using A.1.33(2), p.29.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Kernel
variable {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
  {p : ℕ} [Fact p.Prime]

omit [Finite A] [Group.IsPerfect A] in
private theorem kernel_centralizes_self (N : Subgroup A) [IsMulCommutative N] :
    N ≤ centralizer (N : Set A) := by
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : N) ⟨x,hx⟩)

omit [Finite A] in
private theorem quotient_action_nontrivial (N : Subgroup A) [N.Normal]
    [IsMulCommutative N] [IsQuasisimple (A ⧸ N)] (hn : ¬ IsQuasisimple A) :
    MulAut.quotientConjNormal N N (kernel_centralizes_self N) ≠ 1 := by
  intro ha
  have hN : N ≤ center A := by
    intro n hn'
    apply mem_center_iff.mpr
    intro a
    have he := congrArg (fun f : MulAut N => (f ⟨n,hn'⟩ : A))
      (DFunLike.congr_fun ha (QuotientGroup.mk' N a))
    change a * n * a⁻¹ = n at he
    exact mul_inv_eq_iff_eq_mul.mp he
  let f : PerfectCentralCovering.Cover A (A ⧸ N) := {
    toMonoidHom := QuotientGroup.mk' N
    surjective := QuotientGroup.mk'_surjective N
    isPerfect := inferInstance
    ker_le_center := by simpa only [QuotientGroup.ker_mk'] using hN }
  exact hn f.isQuasisimple

/-- Conjugation by every lift of the central SL₂ involution inverts the
literal elementary extension kernel. No splitting or marked action is assumed. -/
theorem central_involution_inverts (hp : 3 < p) (hn : ¬ IsQuasisimple A)
    (N : Subgroup A) [N.Normal] [IsElementaryAbelian p N]
    (hN : Nat.card N = p ^ 2) (e : (A ⧸ N) ≃* SL(2, ZMod p))
    (t : A) (ht : e (QuotientGroup.mk' N t) = -1) (x : N) :
    t * (x : A) * t⁻¹ = (x : A)⁻¹ := by
  let : IsQuasisimple (A ⧸ N) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa only [Nat.card_zmod] using hp) e
  let ρ := MulAut.quotientConjNormal N N (kernel_centralizes_self N)
  have hρ : ρ.comp e.symm.toMonoidHom ≠ 1 := by
    intro hh
    apply quotient_action_nontrivial N hn
    apply MonoidHom.ext
    intro a
    change ρ a = 1
    have hh' := DFunLike.congr_fun hh (e a)
    change ρ (e.symm (e a)) = 1 at hh'
    simpa only [e.symm_apply_apply] using hh'
  have hi := (Matrix.SpecialLinearGroup.PrimePlaneAction.faithful_and_inverts
    hp hN (ρ.comp e.symm.toMonoidHom) hρ).2 x
  have ht' : e.symm (-1) = QuotientGroup.mk' N t := by rw [← ht, e.symm_apply_apply]
  change ρ (e.symm (-1)) x = x⁻¹ at hi
  rw [ht'] at hi
  exact congrArg Subtype.val hi

/-- In a perfect nonquasisimple elementary-plane extension of SL₂(p),
the radical intersection with a Sylow-radical normalizer is a two-group. -/
theorem radical_inf_normalizer_isPGroup (hp : 3 < p) (hn : ¬ IsQuasisimple A)
    (N : Subgroup A) [N.Normal] [IsElementaryAbelian p N]
    (hN : Nat.card N = p ^ 2) (e : (A ⧸ N) ≃* SL(2, ZMod p))
    (P : Sylow 2 (solvableRadical A)) :
    IsPGroup 2 (solvableRadical A ⊓
      normalizer (((P : Subgroup (solvableRadical A)).map (solvableRadical A).subtype) : Set A) : Subgroup A) := by
  let B := SL(2, ZMod p)
  let q : A →* B := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hk : q.ker = N := by
    ext x
    change e (QuotientGroup.mk' N x) = 1 ↔ x ∈ N
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsSolvable q.ker := hk ▸ inferInstance
  let : IsQuasisimple B :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa only [Nat.card_zmod] using hp) (MulEquiv.refl _)
  have hcenter : solvableRadical B = center B :=
    le_antisymm IsQuasisimple.solvableRadical_le_center
      (le_solvableRadical _ inferInstance inferInstance)
  have hpre : (center B).comap q = solvableRadical A := by
    rw [← hcenter]
    exact comap_solvableRadical_eq_of_solvable_ker q hq
  let qR : solvableRadical A →* center B :=
    (q.comp (solvableRadical A).subtype).codRestrict _ (by
      intro x
      change x.val ∈ (center B).comap q
      rw [hpre]
      exact x.property)
  have hqR : Function.Surjective qR := by
    intro b
    obtain ⟨a,ha⟩ := hq b.val
    have har : a ∈ solvableRadical A := by rw [← hpre]; change q a ∈ center B; rw [ha]; exact b.property
    exact ⟨⟨a,har⟩,Subtype.ext ha⟩
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hZ : IsPGroup 2 (center B) :=
    (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup (ZMod p)
      (by simpa only [Nat.card_zmod] using ho)).of_equiv
        (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker (ZMod p)))
  have hPtop : (P.mapSurjective hqR : Subgroup (center B)) = ⊤ :=
    top_unique ((hZ.to_subgroup ⊤).le_sylow_of_normal _)
  have hm : (-1 : B) ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    change (b : Matrix (Fin 2) (Fin 2) (ZMod p)) * (-1) =
      (-1) * (b : Matrix (Fin 2) (Fin 2) (ZMod p))
    simp
  have htP : (⟨-1,hm⟩ : center B) ∈ (P : Subgroup (solvableRadical A)).map qR := by
    change _ ∈ (P.mapSurjective hqR : Subgroup (center B))
    rw [hPtop]
    trivial
  obtain ⟨t,ht,htq⟩ := htP
  let Q := (P : Subgroup (solvableRadical A)).map (solvableRadical A).subtype
  have htQ : t.val ∈ Q := mem_map_of_mem _ ht
  have htq' : e (QuotientGroup.mk' N t.val) = -1 := congrArg Subtype.val htq
  have hdis : Disjoint N Q := IsPGroup.disjoint_of_ne p 2 (by omega)
    N Q (IsElementaryAbelian.isPGroup p N) (P.isPGroup'.map _)
  have hNC : N ⊓ normalizer (Q : Set A) ≤ centralizer (Q : Set A) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hdis.eq_bot]
    exact le_inf
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal))
      (le_normalizer_iff_commutator_le_right.mp inf_le_right)
  have hinter : N ⊓ normalizer (Q : Set A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hc := mem_centralizer_iff.mp (hNC hx) t.val htQ
    have hi := central_involution_inverts hp hn N hN e t.val htq' ⟨x,hx.1⟩
    have hx2 : (⟨x,hx.1⟩ : N)^2 = 1 := by
      apply Subtype.ext
      change x^2 = 1
      have he : x = x⁻¹ := by simpa only [hc,mul_inv_cancel_right] using hi
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr he
    have he : (⟨x,hx.1⟩ : N) = 1 :=
      (IsElementaryAbelian.isPGroup p N).powEquiv (Nat.coprime_two_right.mpr ho) |>.injective
        (by simpa only [IsPGroup.powEquiv_apply,one_pow] using hx2)
    exact congrArg Subtype.val he
  let D := solvableRadical A ⊓ normalizer (Q : Set A)
  let j : D →* center B := (q.comp D.subtype).codRestrict _ (by
    intro d
    change d.val ∈ (center B).comap q
    rw [hpre]
    exact d.property.1)
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply eq_bot_iff.mpr
    intro d hd
    have hdq : q d.val = 1 := congrArg Subtype.val (show j d = 1 from hd)
    have hdN : d.val ∈ N := hk ▸ hdq
    have he : d.val = 1 := by
      have := (show d.val ∈ N ⊓ normalizer (Q : Set A) from ⟨hdN,d.property.2⟩)
      simpa only [hinter,mem_bot] using this
    exact Subtype.ext he
  exact hZ.of_injective j hj
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Kernel
