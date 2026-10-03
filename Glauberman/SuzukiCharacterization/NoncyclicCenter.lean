module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import Glauberman.ZStar.CoreFree
public import FeitThompson.BGsection1.PLengthLemmas
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The center of the Sylow two-subgroup is noncyclic

A normalizer-fixed involution is central and weakly closed in P, since the
normalizer controls element fusion. The core-free Z* theorem makes it central
in G. Its normal-complement hypothesis would then give a normal two-complement
in G, contradicting the explicit characterization hypotheses.

If Z(P) were cyclic, its unique involution would be fixed by the normalizer.
This proves the binary specialization of Glauberman, *A Characterization of
the Suzuki Groups* (1968), Theorem 4.1(iv), using the already proved Z* theorem.
It avoids the general-prime numerical argument on printed p. 92.
-/

namespace Glauberman.SuzukiCharacterization

/-- No involution of P is fixed by every element of its normalizer. -/
public theorem Hypotheses.not_normalizer_fixed_involution {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P) (t : G)
    (htP : t ∈ (P : Subgroup G)) (ht : orderOf t = 2)
    (hfix : ∀ n ∈ Subgroup.normalizer (P : Set G), n * t * n⁻¹ = t) : False := by
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution t :=
    ⟨by intro he; simp [he] at ht, ht ▸ pow_orderOf_eq_one t⟩
  have htcentral : ∀ s ∈ (P : Subgroup G), s * t = t * s := by
    intro s hs
    exact mul_inv_eq_iff_eq_mul.mp (hfix s ((P : Subgroup G).le_normalizer hs))
  have htweak : Glauberman.ZStar.IsWeaklyClosedInSylow t (P : Subgroup G) := by
    refine ⟨htP, fun g hg => ?_⟩
    obtain ⟨n, hn, he⟩ := h.fusion t htP (g * t * g⁻¹) hg
      (isConj_iff.mpr ⟨g, rfl⟩)
    exact he.symm.trans (hfix n hn)
  have htZ := Glauberman.ZStar.glauberman_zstar_corefree
    h.oddCore_eq_bot P t htI htP htcentral htweak
  have htop : Subgroup.centralizer ({t} : Set G) = ⊤ := by
    apply top_unique
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp htZ g)
  have hcomp := h.involution_complement t htP ht
  rw [htop] at hcomp
  exact h.not_hasNormalPComplement P
    (hasNormalPComplement_of_equiv 2 Subgroup.topEquiv hcomp)

/-- Under the characterization hypotheses the Sylow center is noncyclic. -/
public theorem Hypotheses.not_isCyclic_center {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P) : ¬ IsCyclic (Subgroup.center P) := by
  intro hcyc
  let := hcyc
  have hnontriv : Nontrivial P := by
    by_contra hn
    have : Subsingleton P := not_nontrivial_iff_subsingleton.mp hn
    exact h.not_commutative ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  let := hnontriv
  let := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  let t := z ^ (orderOf z / 2)
  have ht : orderOf t = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos z).ne'
      ((P.isPGroup'.to_subgroup (Subgroup.center P)).dvd_orderOf hz)
  have htG : orderOf ((t : P) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact ht
  apply h.not_normalizer_fixed_involution P ((t : P) : G) (t : P).property htG
  intro n hn
  let f : MulAut P := (P : Subgroup G).normalizerMonoidHom ⟨n, hn⟩
  let fZ := Subgroup.centerCongr f
  have heq : fZ t = t := IsCyclic.eq_of_orderOf_eq_two
    (by rw [fZ.orderOf_eq]; exact ht) ht
  exact congrArg (fun a : Subgroup.center P => ((a : P) : G)) heq


end Glauberman.SuzukiCharacterization
