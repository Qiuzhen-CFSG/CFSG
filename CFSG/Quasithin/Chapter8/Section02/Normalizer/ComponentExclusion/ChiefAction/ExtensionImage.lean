module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Omega
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Section

/-!
# The natural extension in the component-invariant section action

Source: Aschbacher–Smith, Lemma 8.2.7, printed p.718/PDF735, and A.3.6(3).

For the SAME action ρ of J=K_U T constructed in `ChiefAction.Section`,
irreducibility kills O₂(K_U). Thus restriction to K_U induces a literal
homomorphism from K_U/O₂(K_U). Its omega plane acts nontrivially because
Y≤Ξ_p(K_U) acts nontrivially on the section. In the natural A.3.6 branch,
SL₂-transitivity makes the kernel on that plane trivial; its faithful
self-centralizing action then makes the entire quotient homomorphism
injective. The image is the desired natural extension. The quotient
isomorphism and every conjugation coordinate are transported explicitly.

The main theorem applies to the constructor's W=R/(D.subgroupOf R), without
replacing W by another chief factor. It does not use a dimension bound or an
inverting element. This module completes the natural branch only: constructing
the SL₂(5) supplement in the nilpotent source branch remains separate.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter1.RadicalActions

namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.ExtensionImage
variable {A B : Type*} [Group A] [Group B]

private theorem irreducible_kernel_bot (N : Subgroup A) [N.Normal] (f : A →* B)
    (hirr : ∀ C : Subgroup N,
      (∀ (g : A) (x : N), x ∈ C →
        (⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x x.property g⟩ : N) ∈ C) →
      C = ⊥ ∨ C = ⊤)
    (hactive : ¬ N ≤ f.ker) : (f.comp N.subtype).ker = ⊥ := by
  rcases hirr (f.comp N.subtype).ker (by
    intro g x hx
    change f (g * (x : A) * g⁻¹) = 1
    have hx' : f x = 1 := hx
    simp only [map_mul, map_inv, hx', mul_one, mul_inv_cancel]) with hb | ht
  · exact hb
  · exact False.elim (hactive (by
      intro x hx
      exact show (⟨x, hx⟩ : N) ∈ (f.comp N.subtype).ker from ht ▸ mem_top _))

private theorem injective_of_irreducible_selfCentralizing (N : Subgroup A) [N.Normal]
    (f : A →* B)
    (hirr : ∀ C : Subgroup N,
      (∀ (g : A) (x : N), x ∈ C →
        (⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x x.property g⟩ : N) ∈ C) →
      C = ⊥ ∨ C = ⊤)
    (hcent : centralizer (N : Set A) ≤ N)
    (hactive : ¬ N ≤ f.ker) : Function.Injective f := by
  have hk := irreducible_kernel_bot N f hirr hactive
  have hdis : Disjoint f.ker N := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hy
    have hh : (⟨x, hy⟩ : N) ∈ (⊥ : Subgroup N) := hk ▸ hx
    exact congrArg Subtype.val (mem_bot.mp hh)
  have hc : f.ker ≤ N :=
    (commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_eq_bot_of_disjoint hdis)).trans hcent
  apply (MonoidHom.ker_eq_bot_iff f).mp
  exact bot_unique (fun x hx => hdis.le_bot ⟨hx, hc hx⟩)

private theorem natural_selfCentralizing {N : Subgroup A} [N.Normal] {p : ℕ}
    (h : NaturalSL2Action A N p) : centralizer (N : Set A) ≤ N := by
  obtain ⟨F, _, _, _, v, q, ha⟩ := h
  intro g hg
  apply (QuotientGroup.eq_one_iff g).mp
  apply q.injective
  rw [map_one]
  apply Matrix.SL2.naturalAction_injective F
  rw [map_one]
  apply MulEquiv.ext
  intro w
  obtain ⟨x, rfl⟩ := v.surjective w
  have he : (⟨g * x * g⁻¹,
      (inferInstance : N.Normal).conj_mem x x.property g⟩ : N) = x := by
    apply Subtype.ext
    change g * (x : A) * g⁻¹ = x
    rw [← (mem_centralizer_iff.mp hg x x.property), mul_inv_cancel_right]
  have hh := ha g x
  rw [he] at hh
  exact hh.symm

private theorem natural_injective [Finite A] {N : Subgroup A} [N.Normal] {p : ℕ}
    (h : NaturalSL2Action A N p) (f : A →* B) (hactive : ¬ N ≤ f.ker) :
    Function.Injective f :=
  injective_of_irreducible_selfCentralizing N f (natural_irreducible h)
    (natural_selfCentralizing h) hactive

private theorem natural_map {N : Subgroup A} [N.Normal] {p : ℕ}
    (h : NaturalSL2Action A N p) (e : A ≃* B) :
    let : (N.map e.toMonoidHom).Normal := (inferInstance : N.Normal).map e.toMonoidHom e.surjective
    NaturalSL2Action B (N.map e.toMonoidHom) p := by
  let : (N.map e.toMonoidHom).Normal := (inferInstance : N.Normal).map e.toMonoidHom e.surjective
  obtain ⟨F, _, _, hc, v, q, ha⟩ := h
  let eN := e.subgroupMap N
  let eQ := QuotientGroup.congr N (N.map e.toMonoidHom) e rfl
  refine ⟨F, inferInstance, inferInstance, hc, eN.symm.trans v, eQ.symm.trans q, ?_⟩
  intro g x
  obtain ⟨a, rfl⟩ := e.surjective g
  obtain ⟨y, rfl⟩ := eN.surjective x
  have he : (⟨e a * eN y * (e a)⁻¹,
      (inferInstance : (N.map e.toMonoidHom).Normal).conj_mem (eN y) (eN y).property (e a)⟩ :
      N.map e.toMonoidHom) =
      eN ⟨a * y * a⁻¹, (inferInstance : N.Normal).conj_mem y y.property a⟩ := by
    apply Subtype.ext
    change e a * e y * (e a)⁻¹ = e (a * y * a⁻¹)
    simp only [map_mul, map_inv]
  rw [he]
  change v (eN.symm (eN _)) = Multiplicative.ofAdd
    (Matrix.mulVec (q (eQ.symm (QuotientGroup.mk' _ (e a)))).val
      (Multiplicative.toAdd (v (eN.symm (eN y)))))
  rw [eN.symm_apply_apply, eN.symm_apply_apply]
  have heq : eQ.symm (QuotientGroup.mk' _ (e a)) = QuotientGroup.mk' _ a := by
    change eQ.symm (eQ (QuotientGroup.mk' _ a)) = _
    exact eQ.symm_apply_apply _
  rw [heq]
  exact ha a y
end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.ExtensionImage


open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalStructure
open CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.ExtensionImage

private theorem natural_omega {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hnat : A36Natural A) (hd : p ∣ Nat.card (fittingSubgroup A)) :
    3 < p ∧ NaturalSL2Action A (omegaCore p A) p := by
  obtain ⟨hfit, r, hr, hr3, ha⟩ := hnat
  obtain ⟨helem, hc⟩ := natural_elementary ha
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ r ^ 2 by
      simpa only [← hfit, hc] using hd))
  subst r
  have hGF : generalizedFitting A = pCore p A := hfit.trans
    (fitting_eq_core (by rw [← hfit]; exact IsPGroup.of_card hc))
  let : IsElementaryAbelian p (pCore p A) := hGF ▸ helem
  have hW : omegaCore p A = generalizedFitting A := by
    unfold omegaCore
    rw [omega_top (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (pCore p A))),
      ← MonoidHom.range_eq_map, range_subtype]
    exact hGF.symm
  exact ⟨hr3, by simpa only [hW] using ha⟩

variable {G W : Type*} [Group G] [Finite G] [Group W]

/-- The actual restriction to K, factored through its two-core quotient. -/
def componentQuotientAction (J K : Subgroup G) (hKJ : K ≤ J)
    (ρ : J →* MulAut W) (hQker : (K.pCoreIn 2).subgroupOf J ≤ ρ.ker) :
    XiQuotient K →* MulAut W :=
  QuotientGroup.lift (pCore 2 K) (ρ.comp (inclusion hKJ)) (by
    intro k hk
    exact hQker (show (k : G) ∈ K.pCoreIn 2 from ⟨k, hk, rfl⟩))

omit [Finite G] in
/-- The descended homomorphism agrees with the literal inclusion K → J. -/
theorem componentQuotientAction_apply_mk (J K : Subgroup G) (hKJ : K ≤ J)
    (ρ : J →* MulAut W) (hQker : (K.pCoreIn 2).subgroupOf J ≤ ρ.ker) (k : K) :
    componentQuotientAction J K hKJ ρ hQker (QuotientGroup.mk' (pCore 2 K) k) =
      ρ (inclusion hKJ k) := rfl

omit [Finite G] in
/-- Activity of the chosen Sylow subgroup survives on the actual component omega core. -/
theorem omega_active (p : ℕ) (J K Y : Subgroup G) (hKJ : K ≤ J)
    (hYX : Y ≤ XiP p K) (ρ : J →* MulAut W)
    (hQker : (K.pCoreIn 2).subgroupOf J ≤ ρ.ker)
    (hactive : ¬ Y.subgroupOf J ≤ ρ.ker) :
    ¬ omegaCore p (XiQuotient K) ≤ (componentQuotientAction J K hKJ ρ hQker).ker := by
  intro hk
  apply hactive
  intro y hy
  have hx : (⟨(y : G), XiP_le p K (hYX hy)⟩ : K) ∈ xiPIn p K := by
    rw [← XiP_subgroupOf]
    exact hYX hy
  have hpre : (⟨(y : G), XiP_le p K (hYX hy)⟩ : K) ∈ xiPPreimage p K :=
    map_subtype_le _ hx
  exact hk hpre

/-- In the natural source branch the action of K/O₂(K) on the chosen section is faithful. -/
theorem natural_componentQuotientAction_injective (p : ℕ) [Fact p.Prime]
    (J K Y : Subgroup G) (hKJ : K ≤ J) (hYX : Y ≤ XiP p K)
    (ρ : J →* MulAut W) (hQker : (K.pCoreIn 2).subgroupOf J ≤ ρ.ker)
    (hactive : ¬ Y.subgroupOf J ≤ ρ.ker)
    (hnat : A36Natural (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    Function.Injective (componentQuotientAction J K hKJ ρ hQker) :=
  natural_injective (natural_omega hnat hd).2 _
    (omega_active p J K Y hKJ hYX ρ hQker hactive)

/-- The kernel on the containing component is exactly its two-core. -/
theorem natural_component_kernel (p : ℕ) [Fact p.Prime]
    (J K Y : Subgroup G) (hKJ : K ≤ J) (hYX : Y ≤ XiP p K)
    (ρ : J →* MulAut W) (hQker : (K.pCoreIn 2).subgroupOf J ≤ ρ.ker)
    (hactive : ¬ Y.subgroupOf J ≤ ρ.ker)
    (hnat : A36Natural (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    (ρ.comp (inclusion hKJ)).ker = pCore 2 K := by
  let f := componentQuotientAction J K hKJ ρ hQker
  have hf := natural_componentQuotientAction_injective p J K Y hKJ hYX ρ hQker
    hactive hnat hd
  ext k
  constructor
  · intro hk
    apply (QuotientGroup.eq_one_iff k).mp
    apply hf
    change f (QuotientGroup.mk' _ k) = f 1
    rw [map_one]
    exact hk
  · intro hk
    exact hQker (show (k : G) ∈ K.pCoreIn 2 from ⟨k, hk, rfl⟩)

/-- The literal restriction to the selected odd Sylow plane is injective. -/
theorem natural_plane_faithful (p : ℕ) [Fact p.Prime]
    (J K Y : Subgroup G) (hKJ : K ≤ J) (hYX : Y ≤ XiP p K)
    (ρ : J →* MulAut W) (hQker : (K.pCoreIn 2).subgroupOf J ≤ ρ.ker)
    (hactive : ¬ Y.subgroupOf J ≤ ρ.ker)
    (hnat : A36Natural (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) (hY : IsPGroup p Y) :
    Function.Injective (ρ.comp (inclusion (hYX.trans ((XiP_le p K).trans hKJ)))) := by
  have hk := natural_component_kernel p J K Y hKJ hYX ρ hQker hactive hnat hd
  have hp3 := (natural_omega hnat hd).1
  have hdis := IsPGroup.disjoint_of_ne p 2 (by omega) Y (K.pCoreIn 2)
    hY (isPGroup_pCoreIn 2 K)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro y hy
  apply mem_bot.mpr
  apply Subtype.ext
  apply Subgroup.disjoint_def.mp hdis y.property
  have hyK : (⟨(y : G), XiP_le p K (hYX y.property)⟩ : K) ∈ pCore 2 K := by
    rw [← hk]
    exact hy
  exact ⟨_, hyK, rfl⟩

variable [Finite W]

/-- Construct the natural extension inside the fixed section action image. The
embedding, elementary plane, cardinality and marked quotient action are
conclusions; only the genuine natural A.3.6 source structure is assumed. -/
theorem natural_extension_of_component_section (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian 2 W] [Nontrivial W]
    (K T Y : Subgroup G) (hTK : T ≤ normalizer (K : Set G))
    (hYX : Y ≤ XiP p K) (ρ : (K ⊔ T : Subgroup G) →* MulAut W)
    (hirr : ∀ C : Subgroup W,
      (∀ j : (K ⊔ T : Subgroup G), ∀ w, w ∈ C → ρ j w ∈ C) → C = ⊥ ∨ C = ⊤)
    (hactive : ¬ Y.subgroupOf (K ⊔ T) ≤ ρ.ker)
    (hnat : A36Natural (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    3 < p ∧ ∃ (E : Subgroup (MulAut W)) (hE : E ≤ ρ.range)
      (e : XiQuotient K ≃* E) (N : Subgroup E) (_ : N.Normal),
      (∀ k : K, (e (QuotientGroup.mk' (pCore 2 K) k) : MulAut W) =
        ρ (inclusion (show K ≤ K ⊔ T from le_sup_left) k)) ∧
      IsElementaryAbelian p N ∧ Nat.card N = p ^ 2 ∧ NaturalSL2Action E N p ∧
      Function.Injective ((ρ.range.subtype).comp (inclusion hE)) := by
  have hQker := core_killed (K ⊔ T) K ρ (sup_le K.le_normalizer hTK) hirr
  let f := componentQuotientAction (K ⊔ T) K le_sup_left ρ hQker
  have hf : Function.Injective f := natural_componentQuotientAction_injective p
    (K ⊔ T) K Y le_sup_left hYX ρ hQker hactive hnat hd
  let e : XiQuotient K ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hE : f.range ≤ ρ.range := by
    rintro a ⟨x, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    exact ⟨inclusion le_sup_left k, rfl⟩
  let N := (omegaCore p (XiQuotient K)).map e.toMonoidHom
  let : N.Normal := (inferInstance : (omegaCore p (XiQuotient K)).Normal).map
    e.toMonoidHom e.surjective
  obtain ⟨hp3, hm⟩ := natural_omega hnat hd
  have hmodel : NaturalSL2Action f.range N p := natural_map hm e
  obtain ⟨helem, hcard⟩ := natural_elementary hmodel
  exact ⟨hp3, f.range, hE, e, N, inferInstance, fun _ => rfl, helem, hcard, hmodel,
    ρ.range.subtype_injective.comp (inclusion_injective hE)⟩
end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.ExtensionImage
