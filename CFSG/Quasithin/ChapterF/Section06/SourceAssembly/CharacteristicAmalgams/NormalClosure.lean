module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Complete

/-!
# Normal generation in a faithful characteristic-two Goldschmidt pair

The full normal-subgroup rigidity theorem forbids a normal subgroup from
containing exactly one local residual when both original vertices have
characteristic two. If neither residual is contained, F.6.7--8 makes the
normal subgroup odd. Consequently every nontrivial two-subgroup normally
generates a subgroup containing O²(G), and each original local residual
normally generates exactly O²(G).

The ambient residual is nonabelian: an abelian local residual would be a
normal nilpotent subgroup inside F*=O₂, contrary to its cubic quotient.
Thus a nontrivial two-subgroup cannot centralize the ambient residual.
These statements use the actual generated pair and trivial ambient two-core;
they do not infer subnormality inside a local centralizer or any order bound.

Source: Aschbacher--Smith F.6.6--8,13, applied to the faithful pair needed
by F.1.12 and F.6.5, printed pp.305--307.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- A normal subgroup contains either both original local residuals or neither. -/
theorem IsGoldschmidtTriple.normal_residual_containment_iff
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hg₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hg₂ : generalizedFitting G₂ = pCore 2 G₂)
    (X : Subgroup G) [X.Normal] :
    (pResidual 2 G₁).map G₁.subtype ≤ X ↔ (pResidual 2 G₂).map G₂.subtype ≤ X := by
  constructor
  · intro h₁
    by_contra h₂
    exact (SourceAssembly.left_not_characteristic_two_of_residual_cubic h
      (SourceAssembly.left_residual_card_three_of_normal_subgroup h hcore X h₁ h₂)) hg₁
  · intro h₂
    by_contra h₁
    exact (SourceAssembly.left_not_characteristic_two_of_residual_cubic h.symm
      (SourceAssembly.left_residual_card_three_of_normal_subgroup h.symm hcore X h₂ h₁)) hg₂

/-- Every normal subgroup is odd or contains the whole ambient two-residual. -/
theorem IsGoldschmidtTriple.normal_odd_or_twoResidual_le
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hg₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hg₂ : generalizedFitting G₂ = pCore 2 G₂)
    (X : Subgroup G) [X.Normal] : Odd (Nat.card X) ∨ pResidual 2 G ≤ X := by
  by_cases h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X
  · right
    rw [h.twoResidual_eq_sup]
    exact sup_le h₁ ((IsGoldschmidtTriple.normal_residual_containment_iff h hcore hg₁ hg₂ X).mp h₁)
  · left
    have h₂ : ¬(pResidual 2 G₂).map G₂.subtype ≤ X := by
      simpa only [← IsGoldschmidtTriple.normal_residual_containment_iff h hcore hg₁ hg₂ X] using h₁
    have hi₁ := (h.left_subnormal_core_iff_not_residual_le X (Normal.isSubnormal inferInstance)).mpr h₁
    have hi₂ := (h.right_subnormal_core_iff_not_residual_le X (Normal.isSubnormal inferInstance)).mpr h₂
    have ho := h.normal_quotient_odd X hi₁ hi₂
    rw [hcore, sup_bot_eq, bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv] at ho
    exact ho

/-- The normal closure of any nontrivial two-subgroup contains O²(G). -/
theorem IsGoldschmidtTriple.twoResidual_le_normalClosure_of_nontrivial_two_subgroup
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hg₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hg₂ : generalizedFitting G₂ = pCore 2 G₂)
    (U : Subgroup G) (hU : IsPGroup 2 U) (hne : U ≠ ⊥) :
    pResidual 2 G ≤ normalClosure (U : Set G) := by
  rcases IsGoldschmidtTriple.normal_odd_or_twoResidual_le h hcore hg₁ hg₂ (normalClosure (U : Set G)) with ho | hr
  · have hd : 2 ∣ Nat.card U := hU.card_eq_or_dvd.resolve_left
      (fun he => hne (Subgroup.card_eq_one.mp he))
    exact (ho.not_two_dvd_nat (hd.trans (card_dvd_of_le (le_normalClosure (H := U))))).elim
  · exact hr


/-- The original left residual normally generates exactly O²(G). -/
theorem IsGoldschmidtTriple.normalClosure_left_residual
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hg₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hg₂ : generalizedFitting G₂ = pCore 2 G₂) :
    normalClosure ((pResidual 2 G₁).map G₁.subtype : Set G) = pResidual 2 G := by
  let X := normalClosure ((pResidual 2 G₁).map G₁.subtype : Set G)
  have h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X := le_normalClosure
  have h₂ := (IsGoldschmidtTriple.normal_residual_containment_iff h hcore hg₁ hg₂ X).mp h₁
  apply le_antisymm
  · apply normalClosure_le_normal
    rw [h.twoResidual_eq_sup]
    exact (le_sup_left : (pResidual 2 G₁).map G₁.subtype ≤
      (pResidual 2 G₁).map G₁.subtype ⊔ (pResidual 2 G₂).map G₂.subtype)
  · rw [h.twoResidual_eq_sup]
    exact sup_le h₁ h₂

/-- A characteristic-two vertex prevents the ambient residual from being abelian. -/
theorem IsGoldschmidtTriple.twoResidual_not_self_centralizing
    (h : IsGoldschmidtTriple G₁ G₂)
    (hg₁ : generalizedFitting G₁ = pCore 2 G₁) :
    ¬ pResidual 2 G ≤ centralizer (pResidual 2 G : Set G) := by
  intro hc
  let L := pResidual 2 G₁
  have hL : L.map G₁.subtype ≤ pResidual 2 G := by
    rw [h.twoResidual_eq_sup]
    exact le_sup_left
  let : IsMulCommutative L := ⟨⟨fun x y => Subtype.ext (G₁.subtype_injective
      ((mem_centralizer_iff.mp (hc (hL (mem_map_of_mem G₁.subtype y.property))))
        (x : G₁) (hL (mem_map_of_mem G₁.subtype x.property))))⟩⟩
  have hLF : L ≤ fittingSubgroup G₁ := le_sSup ⟨inferInstance,inferInstance⟩
  have hLQ : L ≤ pCore 2 G₁ := hg₁ ▸ hLF.trans (fitting_le_generalizedFitting G₁)
  have hLp : IsPGroup 2 L := pCore_isPGroup.to_le hLQ
  have h3 : 3 ∣ Nat.card L := by
    have hh := (pCore 2 L).index_dvd_card
    change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card L at hh
    rwa [Noncyclic.local_residual_quotient_card_three h.quotient_left] at hh
  obtain ⟨n,hn⟩ := hLp.exists_card_eq
  have hcop : (Nat.card L).Coprime 3 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop.symm) h3

/-- Every nontrivial two-subgroup fails to centralize the ambient residual. -/
theorem IsGoldschmidtTriple.two_subgroup_not_centralize_twoResidual
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hg₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hg₂ : generalizedFitting G₂ = pCore 2 G₂)
    (U : Subgroup G) (hU : IsPGroup 2 U) (hne : U ≠ ⊥) :
    ¬ U ≤ centralizer (pResidual 2 G : Set G) := by
  intro hc
  have hh : normalClosure (U : Set G) ≤ centralizer (pResidual 2 G : Set G) :=
    normalClosure_le_normal hc
  exact IsGoldschmidtTriple.twoResidual_not_self_centralizing h hg₁
    ((IsGoldschmidtTriple.twoResidual_le_normalClosure_of_nontrivial_two_subgroup h hcore hg₁ hg₂ U hU hne).trans hh)

end CFSG.Quasithin.ChapterF
