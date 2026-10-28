module

public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.ElementaryAbelian.Join

/-!
# Products and maximality of reduced normal subgroups

Reduced normal elementary abelian p-subgroups commute because they lie in
and centralize the p-core. Their product is elementary abelian. The core of
the centralizer quotient of a product maps trivially to each factor's
centralizer quotient, so it is trivial. The same argument applies to the
join of all reduced subgroups, which is therefore the unique largest member.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.2.11–12, printed pp.77–78. The maximal member is used in A.1.11.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ}

theorem isPReduced_bot : IsPReduced p (⊥ : Subgroup G) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · exact { exponent_dvd_p := by simp }
  · apply bot_unique
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (centralizer ((⊥ : Subgroup G) : Set G)) x
    apply (QuotientGroup.eq_one_iff g).mpr
    simp [mem_centralizer_iff]


/-- Pulling back the core of a larger centralizer quotient centralizes every
reduced normal subgroup it contains. -/
theorem IsPReduced.quotient_core_preimage_le_centralizer
    {V W : Subgroup G} (hV : IsPReduced p V) [W.Normal] (hVW : V ≤ W) :
    (pCore p (G ⧸ centralizer (W : Set G))).comap
      (QuotientGroup.mk' (centralizer (W : Set G))) ≤ centralizer (V : Set G) := by
  let := hV.normal
  let C := centralizer (W : Set G)
  let D := centralizer (V : Set G)
  have hCD : C ≤ D.comap (MonoidHom.id G) := centralizer_le hVW
  let f := QuotientGroup.map C D (MonoidHom.id G) hCD
  have hf : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective C D (MonoidHom.id G)
      (QuotientGroup.mk'_surjective D) hCD
  have him : (pCore p (G ⧸ C)).map f ≤ pCore p (G ⧸ D) :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  intro x hx
  have hh := him (mem_map_of_mem f hx)
  rw [hV.quotient_pCore_eq_bot] at hh
  exact (QuotientGroup.eq_one_iff x).mp (mem_bot.mp hh)

theorem IsPReduced.sup {V W : Subgroup G}
    (hV : IsPReduced p V) (hW : IsPReduced p W) : IsPReduced p (V ⊔ W) := by
  let := hV.normal
  let := hW.normal
  let := hV.elementary
  let := hW.elementary
  refine ⟨inferInstance, ?_, ?_⟩
  · exact IsElementaryAbelian.sup_of_le_centralizer
      (hW.le_centralizer_pCore.trans (centralizer_le hV.le_pCore))
  · let C := centralizer ((V ⊔ W : Subgroup G) : Set G)
    let q := QuotientGroup.mk' C
    have hc : (pCore p (G ⧸ C)).comap q ≤ C := by
      apply le_centralizer_iff.mpr
      exact sup_le
        (le_centralizer_iff.mp (hV.quotient_core_preimage_le_centralizer le_sup_left))
        (le_centralizer_iff.mp (hW.quotient_core_preimage_le_centralizer le_sup_right))
    apply bot_unique
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    exact (QuotientGroup.eq_one_iff g).mpr (hc hx)

instance reducedPSubgroup_normal : (reducedPSubgroup p G).Normal :=
  sSup_normal _ fun _ h => h.normal

/-- The product of all reduced subgroups is itself reduced and elementary abelian. -/
theorem isPReduced_reducedPSubgroup : IsPReduced p (reducedPSubgroup p G) := by
  have hdir : DirectedOn (· ≤ ·) {V : Subgroup G | IsPReduced p V} := by
    intro V hV W hW
    exact ⟨V ⊔ W, hV.sup hW, le_sup_left, le_sup_right⟩
  have hne : ({V : Subgroup G | IsPReduced p V} : Set (Subgroup G)).Nonempty :=
    ⟨⊥, isPReduced_bot⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact le_centralizer_iff_isMulCommutative.mp
        ((reducedPSubgroup_le_centralizer_pCore p G).trans
          (centralizer_le (reducedPSubgroup_le_pCore p G)))
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      obtain ⟨V, hV, hx⟩ := (mem_sSup_of_directedOn hne hdir).mp x.property
      let := hV.elementary
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.val hx)
  · let C := centralizer (reducedPSubgroup p G : Set G)
    let q := QuotientGroup.mk' C
    have hc : (pCore p (G ⧸ C)).comap q ≤ C := by
      apply le_centralizer_iff.mpr
      exact sSup_le fun V hV => le_centralizer_iff.mp
        (hV.quotient_core_preimage_le_centralizer hV.le_reducedPSubgroup)
    apply bot_unique
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    exact (QuotientGroup.eq_one_iff g).mpr (hc hx)

end Theory.GroupTheory
