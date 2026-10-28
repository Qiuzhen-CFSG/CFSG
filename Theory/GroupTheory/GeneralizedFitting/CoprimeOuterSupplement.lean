module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.CenterlessSupplementCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient

/-!+# Sylow supplements and coprime outer automorphism groups

Suppose the centerless generalized Fitting subgroup L and a Sylow p-subgroup
generate a finite group G. The quotient G/L is a p-group. Since C_G(L)
intersects L trivially, it embeds in that quotient and is a normal p-subgroup.
It therefore lies in O_p(G) ≤ F*(G) = L and is trivial. Thus the actual outer
action embeds G/L in Aut(L)/Inn(L). If this outer group has order prime to p,
then G = L.

This avoids the general self-centralization theorem for F*(G). The Suzuki
case is the extension reduction used in Aschbacher--Smith E.1.14(1), printed
p.214 (PDF p.225), citing Aschbacher (1982), Lemma 4.7.
-/

public section
namespace Theory.GroupTheory
open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A centerless generalized Fitting subgroup with a Sylow supplement has
trivial ambient centralizer. -/
theorem centralizer_generalizedFitting_eq_bot_of_centerless_supplement
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hgen : generalizedFitting G ⊔ (S : Subgroup G) = ⊤)
    (hZ : center (generalizedFitting G) = ⊥) :
    centralizer (generalizedFitting G : Set G) = ⊥ := by
  let L := generalizedFitting G
  let C := centralizer (L : Set G)
  have hCS : C ≤ (S : Subgroup G) :=
    centralizer_le_sylow_of_centerless_supplement L S hgen hZ
  have hpC : IsPGroup p C := S.isPGroup'.to_le hCS
  have hCp : C ≤ pCore p G := le_sSup ⟨inferInstance, hpC⟩
  have hCL : C ≤ L :=
    hCp.trans ((pCore_le_fitting G p).trans (fitting_le_generalizedFitting G))
  apply le_bot_iff.mp
  intro c hc
  have hz : (⟨c, hCL hc⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (hc l l.property)
  rw [hZ, mem_bot] at hz
  exact congrArg (fun l : L => (l : G)) hz

/-- A Sylow p-extension of a centerless generalized Fitting subgroup is
trivial when its full outer automorphism group has order prime to p. -/
theorem generalizedFitting_eq_top_of_coprime_outer_supplement
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hgen : generalizedFitting G ⊔ (S : Subgroup G) = ⊤)
    (hZ : center (generalizedFitting G) = ⊥)
    (hcop : (Nat.card (MulAut.Outer (generalizedFitting G))).Coprime p) :
    generalizedFitting G = ⊤ := by
  let L := generalizedFitting G
  have hquot : IsPGroup p (G ⧸ L) :=
    isPGroup_quotient_of_sup_eq_top L (S : Subgroup G) S.isPGroup' hgen
  have hd := Subgroup.card_dvd_of_injective (MulAut.outerAction L)
    (MulAut.outerAction_injective L
      (centralizer_generalizedFitting_eq_bot_of_centerless_supplement S hgen hZ))
  obtain ⟨k, hk⟩ := hquot.exists_card_eq
  apply Subgroup.index_eq_one.mp
  change Nat.card (G ⧸ L) = 1
  exact Nat.eq_one_of_dvd_coprimes (hcop.pow_right k) hd (dvd_of_eq hk)

end Theory.GroupTheory
