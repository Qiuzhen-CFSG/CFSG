module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingEnumeration
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.QuotientBasic

/-!
# The actual alternating core modulo a centralizer kernel

The source product Q=UD identifies Φ(Q) with Φ(D), and the commutator
plane identifies the opposite UD product with Qˣ before quotienting.
Every quotient killing Φ(D) therefore has elementary core. These are
source consequences, not assumptions about the quotient family.

Source: Aschbacher–Smith C.5.6(4)–(6), printed pp.157–158.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open RankOne
variable {G : Type*} [Group G] [Finite G] {R L K : Subgroup G}

omit [Finite G] in
private theorem module_elementary (h : AlternatingPairSetup R L K) : IsElementaryAbelian 2 (U L) := by
  let := h.block.2.1.elementary
  exact IsElementaryAbelian.map L.subtype

omit [Finite G] in
private theorem module_le_core (h : AlternatingPairSetup R L K) : U L ≤ Q R L :=
  le_sup_left.trans_eq h.product.symm

theorem AlternatingPairSetup.core_frattini (h : AlternatingPairSetup R L K) :
    (frattini (Q R L)).map (Q R L).subtype = Phi R L :=
  frattini_map_eq_of_central_elementary_supplement (Q R L) (D R L) (U L)
    (isPGroup_pCoreIn 2 (L ⊔ S R)) (module_elementary h)
    (le_centralizer_iff.mp (h.core.le.trans inf_le_right)) h.product

theorem AlternatingPairSetup.phi_normal (h : AlternatingPairSetup R L K) :
    ((Phi R L).subgroupOf (S R)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [← h.core_frattini]
  exact (S_normalizes_Q R L).trans
    (normalizer_le_normalizer_characteristic_image (Q R L) (frattini (Q R L)))

private theorem elementary_image_of_frattini_le_ker {P T : Type*} [Group P] [Finite P] [Group T]
    (hp : IsPGroup 2 P) (f : P →* T) (hk : frattini P ≤ f.ker) :
    IsElementaryAbelian 2 f.range := by
  let : Fact (IsPGroup 2 P) := ⟨hp⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let g := QuotientGroup.lift (frattini P) f hk
  have hg : g.range = f.range := by
    ext a
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) q
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨QuotientGroup.mk' (frattini P) p, rfl⟩
  rw [← hg]
  exact IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective

variable {T : Type*} [Group T]

theorem AlternatingPairSetup.quotient_core_elementary (h : AlternatingPairSetup R L K)
    (f : S R →* T) (hk : (Phi R L).subgroupOf (S R) ≤ f.ker) :
    IsElementaryAbelian 2 (baumannImage R f (Q R L)) := by
  have hQS : Q R L ≤ S R := h.core.le.trans inf_le_left
  let g := f.comp (inclusion hQS)
  have hg : g.range = baumannImage R f (Q R L) := by
    ext t
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨inclusion hQS q, q.property, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  rw [← hg]
  apply elementary_image_of_frattini_le_ker (isPGroup_pCoreIn 2 (L ⊔ S R))
  intro q hq
  change f (inclusion hQS q) = 1
  apply MonoidHom.mem_ker.mp
  apply hk
  exact h.core_frattini ▸ mem_map_of_mem (Q R L).subtype hq

theorem AlternatingPairSetup.opposite_eq_conjugate (h : AlternatingPairSetup R L K)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    (U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔ D R L =
      (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  let Q' := (Q R L).map (MulAut.conj x⁻¹).toMonoidHom
  have hp : Q R L = U L ⊔ D R L := h.product
  have hd : D R L ≤ centralizer (V : Set G) := h.centralizer_centralizes_conjugate x hx hnc
  have hs : S R = V ⊔ Q R L := h.first_factorization x hx hnc
  have hDQ' : D R L ≤ Q' := by
    dsimp only [Q']
    rw [h.conjugate_core x hx]
    exact le_inf inf_le_left hd
  have hVQ' : V ≤ Q' := map_mono (module_le_core h)
  apply le_antisymm (sup_le hVQ' hDQ')
  intro q hq
  have hqS := ((h.conjugate_core x hx).le.trans inf_le_left) hq
  have hV : V ≤ S R := hVQ'.trans ((h.conjugate_core x hx).le.trans inf_le_left)
  have hqprod : q ∈ (V : Set G) * (Q R L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right V (Q R L)
      (hV.trans (S_normalizes_Q R L))]
    exact hs ▸ hqS
  obtain ⟨v, hv, a, ha, rfl⟩ := hqprod
  have haQ' : a ∈ Q' := by
    have hh := Q'.mul_mem (Q'.inv_mem (hVQ' hv)) hq
    simpa only [inv_mul_cancel_left] using hh
  have haprod : a ∈ (U L : Set G) * (D R L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right (U L) (D R L)
      ((le_centralizer_iff.mp ((hp ▸ le_sup_right).trans (h.core.le.trans inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _))]
    exact hp ▸ ha
  obtain ⟨u, hu, d, hd', rfl⟩ := haprod
  have huC : u ∈ centralizer (V : Set G) :=
    ((centralizer (V : Set G)).mul_mem_cancel_right (hd hd')).mp
      (((h.conjugate_core x hx).le.trans inf_le_right) haQ')
  have huV : u ∈ V :=
    (h.commutator_eq_fixed x hx hnc).2 ▸
      ((h.commutator_eq_fixed x hx hnc).1.symm ▸ (show u ∈ U L ⊓ centralizer (V : Set G) from ⟨hu, huC⟩)) |>.2
  exact (V ⊔ D R L).mul_mem (mem_sup_left hv) (mul_mem_sup huV hd')

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
end
