module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.HexadLocals.Transport
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.AlternatingPower

/-!
# The full Sylow closure of the M₂₂ hexad subgroup

Work inside H, where L is a component. Distinct S-conjugate components
commute and are centerless. Invariance under N_S(L) identifies the hexad
factors in each component, so their orbit join is an actual direct power
of the hexad factor. Its maps onto A₆ give a surjection onto a finite power
of A₆ with two-group kernel. Adjoining S gives a normal layer with two-group
upper quotient and preserves the self-centralizing two-core.

The final equivalence transports this construction to the literal subgroup
K ⊔ SG in G. The three intrinsic premises are supplied by the extension,
characteristic-two and normalizer transport theorems in `Transport`; their
model inputs remain the responsibility of the hexad witness assembly.

Source: Aschbacher–Smith 2.3.8(4) and 2.3.9(7)(f), printed pp.523 and
525–526, combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem hexad_le_local {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) (t : L) :
    mathieuTwentyTwoHexadGroup e t ≤ H :=
  (map_subtype_le _).trans h.component_le

private theorem relative_component_center
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) :
    center (L.subgroupOf H) = ⊥ := by
  let eL : L.subgroupOf H ≃* M22 := (subgroupOfEquivOfLe h.component_le).trans e
  apply bot_unique
  intro x hx
  have hm : eL x ∈ center M22 := (centerCongr eL ⟨x, hx⟩).property
  rw [m22_center_eq_bot, mem_bot] at hm
  exact mem_bot.mpr (eL.injective (hm.trans (map_one eL).symm))

private theorem hexad_quotient_map {K : Type*} [Group K]
    (h : AlternatingBySixteen K 6) :
    ∃ f : K →* alternatingGroup (Fin 6),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  obtain ⟨U, hn, he, _, ⟨e⟩⟩ := h
  let := hn
  let := he
  let f := e.toMonoidHom.comp (QuotientGroup.mk' U)
  refine ⟨f, e.surjective.comp (QuotientGroup.mk'_surjective U), ?_⟩
  change IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' U)).ker
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact IsElementaryAbelian.isPGroup 2 U

/-- The conditional hexad construction for the whole supplied Sylow group.
The projection and involution hypotheses are needed to produce the intrinsic
inputs in `Transport`; the orbit step uses just these three resulting facts. -/
theorem mathieuTwentyTwo_hexadOvergroup_structure
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) (t : L)
    (hext : AlternatingBySixteen (mathieuTwentyTwoHexadGroup e t) 6)
    (hc : centralizer (pCore 2 (mathieuTwentyTwoHexadGroup e t) :
      Set (mathieuTwentyTwoHexadGroup e t)) ≤ pCore 2 (mathieuTwentyTwoHexadGroup e t))
    (hinv : ((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) ≤
      normalizer (mathieuTwentyTwoHexadGroup e t : Set G)) :
    mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t ∈ Chapter1.He G ∧
      AlternatingPowerTwoExtension
        (mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t) 6 := by
  let := h.finite
  let K := mathieuTwentyTwoHexadGroup e t
  let J := K.subgroupOf H
  have hKH : K ≤ H := hexad_le_local h e t
  let eJ : J ≃* K := subgroupOfEquivOfLe hKH
  have hJL : J ≤ L.subgroupOf H := subgroupOf_mono H (map_subtype_le _)
  have hinvH : (S : Subgroup H) ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (J : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le, ← subgroupOf_normalizer_eq hKH]
    rintro x ⟨hs, hn⟩
    exact hinv ⟨mem_map_of_mem H.subtype hs, hn⟩
  have hcJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 eJ).mpr hc
  obtain ⟨f, hf, hk⟩ := hexad_quotient_map (hext.of_equiv eJ.symm)
  obtain ⟨hchar, hshape⟩ := component_local_closure_alternatingPower h.component
    (relative_component_center h e) S.isPGroup' hJL hinvH hcJ f hf hk
  let eX : (J ⊔ (S : Subgroup H) : Subgroup H) ≃*
      mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t :=
    ((J ⊔ (S : Subgroup H)).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (by
        rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH]
        rfl))
  exact ⟨Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 eX).mp hchar), hshape.of_equiv eX⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
