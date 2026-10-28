module

public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The unique maximum abelian subgroup of the ternary Sylow product

Let V have order81 and let D be extraspecial of order243, with abelian
intersection of order27. If V normalizes D and outside elements of D
have no fixed points in V outside D, every abelian subgroup of VD escaping
V has order at most27. The intersection is self-centralizing in D, which
first derives the missing normality of V. The intermediate subgroup
(VB) ∩ D then has order81 or243; its centralizer in V has order at most9
or3, respectively, and the product formulas give the result.

V is uniquely of maximum abelian order; the claim is not uniqueness among
subgroups maximal by inclusion. No exponent-p assumption on D is used.
Source: Aschbacher, Sporadic Groups (1994),45.8,last paragraph,p246.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement Pointwise
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
/-- The intersection of order27 is self-centralizing in the extraspecial
subgroup; the elementary81 therefore becomes normal in their join. -/
theorem cubic_extraspecial_intersection_and_normalizer
    (V D:Subgroup G) [IsMulCommutative V] [IsExtraspecial 3 D]
    (hD:Nat.card D=243) (hI:Nat.card (V⊓D:Subgroup G)=27)
    (hVD:V≤normalizer (D:Set G)) :
    D⊓centralizer (V⊓D:Subgroup G)=V⊓D ∧ D≤normalizer (V:Set G) := by
  let A:=V⊓D
  let A':=A.subgroupOf D
  let f:A'→*V := (inclusion (show A≤V from inf_le_left)).comp
    (subgroupOfEquivOfLe (show A≤D from inf_le_right)).toMonoidHom
  have hf:Function.Injective f := (inclusion_injective (show A≤V from inf_le_left)).comp
      (subgroupOfEquivOfLe (show A≤D from inf_le_right)).injective
  let :IsMulCommutative A':=⟨⟨fun x y=>hf (by simp only [map_mul,mul_comm])⟩⟩
  have hA':Nat.card A'=27:=(Nat.card_congr (subgroupOfEquivOfLe (show A≤D from inf_le_right)).toEquiv).trans hI
  have hs:centralizer (A':Set D)=A':=
    extraspecial_prime_selfcentralizing_of_card_sq (p:=3) A' (by rw [hA',hD];decide)
  have hcen:D⊓centralizer (A:Set G)=A:=by
    apply le_antisymm
    · intro x hx
      have hm:(⟨x,hx.1⟩:D)∈centralizer (A':Set D):=by
        intro a ha
        exact Subtype.ext (hx.2 a ha)
      exact hs.le hm
    · exact le_inf inf_le_right
        (inf_le_left.trans V.le_centralizer |>.trans (centralizer_le inf_le_left))
  have hZA:(center D).map D.subtype≤A:=by
    rintro x ⟨d,hd,rfl⟩
    apply hcen.le
    exact ⟨d.property,fun a ha=>congrArg Subtype.val (mem_center_iff.mp hd ⟨a,ha.2⟩)⟩
  have hder:⁅D,D⁆≤(center D).map D.subtype:=by
    rw [←map_subtype_commutator]
    exact map_mono (IsExtraspecial.quotient_elementary_abelian 3 D).commutator_le_center_of_central_quotient
  have hDA:D≤normalizer (A:Set G):=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl (show A≤D from inf_le_right)).trans (hder.trans hZA))
  have hVCA:V≤centralizer (A:Set G):=V.le_centralizer.trans (centralizer_le inf_le_left)
  have hDCA:D≤normalizer (centralizer (A:Set G):Set G):=
    hDA.trans (normalizer_le_normalizer_centralizer A)
  have hc:⁅D,V⁆≤D⊓centralizer (A:Set G):=le_inf
    (le_normalizer_iff_commutator_le_left.mp hVD)
    ((commutator_mono le_rfl hVCA).trans (le_normalizer_iff_commutator_le_right.mp hDCA))
  exact ⟨hcen,le_normalizer_iff_commutator_le_right.mpr (hc.trans (hcen.le.trans inf_le_left))⟩

/-- Any abelian subgroup escaping the elementary81 has order at most27. -/
theorem cubic_extraspecial_abelian_card_le
    (V D:Subgroup G) [IsMulCommutative V] [IsExtraspecial 3 D]
    (hV:Nat.card V=81) (hD:Nat.card D=243) (hI:Nat.card (V⊓D:Subgroup G)=27)
    (hVD:V≤normalizer (D:Set G))
    (hfix:∀d∈D,d∉V→V⊓centralizer ({d}:Set G)≤D)
    (B:Subgroup G) [IsMulCommutative B] (hBP:B≤V⊔D) (hBV:¬B≤V) :
    Nat.card B≤27 := by
  obtain ⟨hcen,hDV⟩:=cubic_extraspecial_intersection_and_normalizer V D hD hI hVD
  let L:=V⊓D
  let R:=V⊔B
  let D0:=R⊓D
  let U:=V⊓B
  have hLI:L≤D0:=le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hD0D:D0≤D:=inf_le_right
  have hRP:R≤V⊔D:=sup_le le_sup_left hBP
  have hRN:R≤normalizer (V:Set G):=hRP.trans (sup_le V.le_normalizer hDV)
  have hRN':R≤normalizer (D:Set G):=hRP.trans (sup_le hVD D.le_normalizer)
  have hRD:V⊔D0=R:=by
    apply le_antisymm (sup_le le_sup_left inf_le_left)
    intro a ha
    have hp:a∈(V:Set G)*(D:Set G):=by
      rw [←coe_mul_of_right_le_normalizer_left V D hDV]
      exact hRP ha
    obtain ⟨v,hv,d,hd,hvd⟩:=hp
    have hdR:d∈R:=by
      have hh:=R.mul_mem (R.inv_mem (mem_sup_left hv)) ha
      rw [←hvd] at hh
      simpa only [inv_mul_cancel_left] using hh
    rw [←hvd]
    exact mul_mem_sup hv ⟨hdR,hd⟩
  have hVL:V⊓D0=L:=by
    apply le_antisymm
    · exact inf_le_inf_left V inf_le_right
    · exact le_inf inf_le_left hLI
  obtain ⟨b,hb,hbV⟩:=SetLike.not_le_iff_exists.mp hBV
  have hD0not:¬D0≤V:=by
    intro hh
    exact hbV ((hRD.symm.le.trans (sup_le le_rfl hh)) (mem_sup_right hb))
  obtain ⟨d,hd,hdV⟩:=SetLike.not_le_iff_exists.mp hD0not
  have hUC:U≤centralizer (D0:Set G):=by
    intro u hu d hd
    have hdprod:d∈(V:Set G)*(B:Set G):=by
      rw [←coe_mul_of_right_le_normalizer_left V B (hBP.trans (sup_le V.le_normalizer hDV))]
      exact hd.1
    obtain ⟨v,hv,b,hb,rfl⟩:=hdprod
    have huv:v*u=u*v:=V.le_centralizer hu.1 v hv
    have hub:b*u=u*b:=B.le_centralizer hu.2 b hb
    rw [mul_assoc,hub,←mul_assoc,huv,mul_assoc]
  have hUD:U≤D:=by
    intro u hu
    exact hfix d hd.2 hdV ⟨hu.1,mem_centralizer_singleton_iff.mpr (hUC hu d hd).symm⟩
  have hUL:U≤L:=le_inf inf_le_left hUD
  have hD0big:27<Nat.card D0:=by
    have hc:=card_le_of_le hLI
    change Nat.card (V⊓D:Subgroup G)≤Nat.card D0 at hc
    rw [hI] at hc
    have hne:Nat.card D0≠27:=by
      intro he
      have hh:L=D0:=eq_of_le_of_card_ge hLI (by change Nat.card D0≤Nat.card (V⊓D:Subgroup G);rw [he,hI])
      exact hD0not (hh.symm.le.trans inf_le_left)
    omega
  have hdvd:Nat.card D0∣243:=hD ▸ card_dvd_of_le hD0D
  have hcases:Nat.card D0=81 ∨ Nat.card D0=243:=by
    have hh:=Nat.mem_divisors.mpr ⟨hdvd,(by decide:243≠0)⟩
    have he:Nat.divisors 243={1,3,9,27,81,243}:=by decide
    simp only [he,Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  have hcB:=card_mul_eq_card_inf_mul_card_sup_of_normalizes V B
    (hBP.trans (sup_le V.le_normalizer hDV))
  have hcD:=card_mul_eq_card_inf_mul_card_sup_of_normalizes V D0 (hD0D.trans hDV)
  change Nat.card V*Nat.card B=Nat.card U*Nat.card R at hcB
  rw [hV] at hcB
  rw [hV,hVL,hI,hRD] at hcD
  rcases hcases with h81|h243
  · have hUne:Nat.card U≠27:=by
      intro hu
      have he:U=L:=eq_of_le_of_card_ge hUL (by change Nat.card (V⊓D:Subgroup G)≤Nat.card U;rw [hI,hu])
      have hl:D0≤L:=by
        apply (le_inf hD0D ((le_centralizer_iff.mp hUC).trans (by rw [he]))).trans
        exact hcen.le
      exact hD0not (hl.trans inf_le_left)
    have hUd:Nat.card U∣27:=hI ▸ card_dvd_of_le hUL
    have hU9:Nat.card U≤9:=by
      have hh:=Nat.mem_divisors.mpr ⟨hUd,(by decide:27≠0)⟩
      have he:Nat.divisors 27={1,3,9,27}:=by decide
      simp only [he,Finset.mem_insert,Finset.mem_singleton] at hh
      omega
    rw [h81] at hcD
    nlinarith
  · have he:D0=D:=eq_of_le_of_card_ge hD0D (by rw [h243,hD])
    have hUZ:U≤(center D).map D.subtype:=by
      intro u hu
      refine ⟨⟨u,hUD hu⟩,mem_center_iff.mpr ?_,rfl⟩
      intro x
      exact Subtype.ext (hUC hu x (he.symm ▸ x.property))
    have hU3:=card_le_of_le hUZ
    rw [card_map_of_injective D.subtype_injective,IsExtraspecial.center_order_p 3 D] at hU3
    rw [h243] at hcD
    nlinarith

/-- V is the unique abelian subgroup of maximum order in V D. -/
theorem cubic_extraspecial_unique_maximum_abelian
    (V D:Subgroup G) [IsMulCommutative V] [IsExtraspecial 3 D]
    (hV:Nat.card V=81) (hD:Nat.card D=243) (hI:Nat.card (V⊓D:Subgroup G)=27)
    (hVD:V≤normalizer (D:Set G))
    (hfix:∀d∈D,d∉V→V⊓centralizer ({d}:Set G)≤D)
    (B:Subgroup G) [IsMulCommutative B] (hBP:B≤V⊔D) (hB:81≤Nat.card B) :
    B=V := by
  by_cases hh:B≤V
  · exact eq_of_le_of_card_ge hh (by rw [hV];exact hB)
  · have hb:=cubic_extraspecial_abelian_card_le V D hV hD hI hVD hfix B hBP hh
    omega

end Subgroup
