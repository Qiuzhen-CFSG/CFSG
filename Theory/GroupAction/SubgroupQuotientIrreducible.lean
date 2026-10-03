module
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Irreducible conjugation quotients from maximal invariant denominators

If P normalizes E and D, and D is maximal among P-invariant proper subgroups
of E, then every invariant subgroup of the literal quotient E/D is trivial
or the whole quotient. The supplied normality instance and conjugation
formula are retained.

Lift an invariant quotient subgroup through the projection and E's subtype.
The lifted subgroup contains D, lies in E, and is P-invariant. Maximality
makes it D or E, giving the two quotient possibilities.

This source-neutral quotient correspondence was extracted from the
residual-active chief-section construction in Stellmacher Section Three;
it also supplies the actual chief quotient in source (10.1)(15).
-/

namespace Subgroup
public theorem quotient_conjugation_irreducible_of_maximal
    {H : Type*} [Group H] (P E D : Subgroup H)
    (hDE : D ≤ E) (hPE : P ≤ Subgroup.normalizer (E : Set H))
    (hN : (D.subgroupOf E).Normal)
    (hmax : ∀ L : Subgroup H, D ≤ L → L < E →
      P ≤ Subgroup.normalizer (L : Set H) → L = D) :
    let _ := hN
    ∀ f : P →* MulAut (E ⧸ D.subgroupOf E),
      (∀ p : P, ∀ e : E,
        f p (QuotientGroup.mk' (D.subgroupOf E) e) =
          QuotientGroup.mk' (D.subgroupOf E)
            ⟨(p : H) * (e : H) * (p : H)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPE p.property) e).mp e.property⟩) →
      ∀ K : Subgroup (E ⧸ D.subgroupOf E),
        (∀ p : P, ∀ w, w ∈ K → f p w ∈ K) → K = ⊥ ∨ K = ⊤ := by
  let _ := hN
  dsimp only
  intro f hf K hK
  let q := QuotientGroup.mk' (D.subgroupOf E)
  let L := (K.comap q).map E.subtype
  have hLE : L ≤ E := Subgroup.map_subtype_le _
  have hDL : D ≤ L := by
    intro d hd
    refine ⟨⟨d,hDE hd⟩,?_,rfl⟩
    change q ⟨d,hDE hd⟩ ∈ K
    have hdq : q ⟨d,hDE hd⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := D.subgroupOf E) _).mpr hd
    rw [hdq]
    exact K.one_mem
  have hPL : P ≤ Subgroup.normalizer (L : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp x hx
    obtain ⟨e,he,rfl⟩ := hx
    refine ⟨⟨p * (e : H) * p⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPE hp) e).mp e.property⟩,?_,rfl⟩
    change q _ ∈ K
    rw [← hf ⟨p,hp⟩ e]
    exact hK ⟨p,hp⟩ (q e) he
  by_cases htop : L = E
  · right
    apply top_unique
    intro w _
    obtain ⟨e,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf E) w
    have he : (e : H) ∈ L := by rw [htop]; exact e.property
    obtain ⟨e',he',hee⟩ := he
    have heq : e' = e := Subtype.ext hee
    change q e ∈ K
    change q e' ∈ K at he'
    simpa only [heq] using he'
  · left
    have hLD := hmax L hDL (lt_of_le_of_ne hLE htop) hPL
    apply bot_unique
    intro w hw
    obtain ⟨e,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf E) w
    apply Subgroup.mem_bot.mpr
    apply (QuotientGroup.eq_one_iff (N := D.subgroupOf E) e).mpr
    change (e : H) ∈ D
    rw [← hLD]
    exact ⟨e,hw,rfl⟩

end Subgroup
