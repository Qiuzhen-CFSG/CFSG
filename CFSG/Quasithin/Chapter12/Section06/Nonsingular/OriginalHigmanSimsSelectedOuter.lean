module

public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentLinearOdd
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsPrimeOuter

/-!
# The selected equality and prime rows contradict the actual residual outer action

The specified original V element acts on the selected component and fixes
an actual full Sylow two-subgroup pointwise. Its restriction to the literal
common-residual A5 is precisely the specified normalizer action in H/O2(H).
The equality and odd-prime PSL2 rows force this restriction to be inner,
contradicting the original outer witness.

The actual J, its inclusion, A5 identification and acting element are
retained. The outer-action hypothesis is explicit: this transfer does not
supply the original HS witness. No nonsingular-centralizer conclusion or
natural-module hypothesis is used.

Source: Aschbacher--Smith 12.6.34, using the prime-field and equality rows
of A.3.14(3) and 16.1.6.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
  (J : Subgroup G) (hJK : J ≤ c.K)
  (eJ : Nonabelian.Setup.star H J ≃* alternatingGroup (Fin 5))
  (x : H) (hxV : (x : G) ∈ V)
  (hxN : QuotientGroup.mk' (pCore 2 H) x ∈
    normalizer (Nonabelian.Setup.star H J : Set (H ⧸ pCore 2 H)))
  (houter : (Nonabelian.Setup.star H J).normalizerMonoidHom
    ⟨QuotientGroup.mk' (pCore 2 H) x,hxN⟩ ∉
      MulAut.innerSubgroup (Nonabelian.Setup.star H J))

include hz hTV hTz hbound hH hn a hJK eJ hxV hxN houter in
private theorem selected_outer_restriction :
    ∃ (P : Sylow 2 (Nonabelian.Setup.star H c.K))
      (B : Subgroup (Nonabelian.Setup.star H c.K))
      (_ : B ≃* alternatingGroup (Fin 5))
      (α : MulAut (Nonabelian.Setup.star H c.K)),
      (∀ k ∈ P, α k = k) ∧
      ∃ hB : B.map α.toMonoidHom = B,
        ((α.subgroupMap B).trans (MulEquiv.subgroupCongr hB)) ∉
          MulAut.innerSubgroup B := by
  let K := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H J
  have hAK : A ≤ K := map_mono (comap_mono hJK)
  let B := A.subgroupOf K
  let j : B ≃* A := subgroupOfEquivOfLe hAK
  have hVX : V ≤ c.localActor := le_sup_right
  let v : c.localActor := ⟨x.val,hVX hxV⟩
  let α := a.action v
  have hv : α ∈ (V.subgroupOf c.localActor).map a.action := ⟨v,hxV,rfl⟩
  obtain ⟨P,hP⟩ := S.original_action_module_fixes_component_sylow
    D hZ z hz hTV hTz hbound hH hn c a
  have hconj (k : K) : (α k : H ⧸ pCore 2 H) =
      QuotientGroup.mk' (pCore 2 H) x * k.val * (QuotientGroup.mk' (pCore 2 H) x)⁻¹ := by
    have he : inclusion a.local_le v = x := Subtype.ext rfl
    simpa only [he] using a.conjugation v k
  have hB : B.map α.toMonoidHom = B := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨k,hk,rfl⟩
      change (α k : H ⧸ pCore 2 H) ∈ A
      rw [hconj]
      exact (A.normalizerMonoidHom ⟨QuotientGroup.mk' (pCore 2 H) x,hxN⟩
        ⟨k.val,hk⟩).property
    · rw [card_map_of_injective α.injective]
  let β : MulAut B := (α.subgroupMap B).trans (MulEquiv.subgroupCongr hB)
  have he : MulAut.congr j β =
      A.normalizerMonoidHom ⟨QuotientGroup.mk' (pCore 2 H) x,hxN⟩ := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    exact hconj (j.symm y).val
  refine ⟨P,B,j.trans eJ,α,hP α hv,hB,?_⟩
  intro hi
  apply houter
  rw [←he,←MulAut.map_innerSubgroup_congr j]
  exact mem_map_of_mem (MulAut.congr j).toMonoidHom hi

include hz hTV hTz hbound hH hn a hJK eJ hxV hxN houter in
/-- An outer action on the literal common-residual A5 excludes the equality row. -/
theorem SourceHypothesis.original_hs_selected_not_alternatingFive_of_outer :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  obtain ⟨P,B,eB,α,hfix,hB,ho⟩ := selected_outer_restriction
    S D hZ z hz hTV hTz hbound hH hn c a J hJK eJ x hxV hxN houter
  exact ho (OriginalHigmanSimsPrimeOuter.five_sylow_fixed_restriction_inner e P B eB α hfix hB)

include hz hTV hTz hbound hH hn a hJK eJ hxV hxN houter in
/-- The same specified outer action excludes every odd-prime PSL2 row above three. -/
theorem SourceHypothesis.original_hs_selected_not_primeLinearTwo_of_outer
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hl : 3 < p) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 2 p := by
  intro he
  obtain ⟨P,B,eB,α,hfix,hB,hout⟩ := selected_outer_restriction
    S D hZ z hz hTV hTz hbound hH hn c a J hJK eJ x hxV hxN houter
  exact hout (OriginalHigmanSimsPrimeOuter.prime_sylow_fixed_restriction_inner
    hp ho hl he P B eB α hfix hB)

end CFSG.Quasithin.Chapter12.Section06
