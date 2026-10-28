module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.MaximalSylow
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.GroupTheory.DihedralGeneratedFactor

/-!
# Four-group centralizer generation for a full A₆ action

Suppose J acts as the full automorphism group on a normal A₆ subgroup.
The centralizer of an inner involution maps onto a Sylow two-subgroup of
Aut(A₆), which is maximal. If all involution centralizers of an elementary
four-group lay above that Sylow, the fixed-subgroup calculation would map
the whole four-group into the order-two inner Sylow center. Its nontrivial
kernel then centralizes A₆, contradicting that image bound. The action kernel
already lies in the inner involution centralizer, so generation holds in J
itself, not only in its automorphism image.

Source: Aschbacher–Smith, the Γ₁,E step in 2.4.36, printed p.549. The actual
paired-cubic consumer supplies the original involution centralizers.
-/

public section
open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal

private theorem innerSylowCenter_card (P : Sylow 2 AutA6) :
    Nat.card (innerSylowCenter P) = 2 := by
  rw [innerSylowCenter, card_map_of_injective
    (show Function.Injective (P.toSubgroup.subtype.comp (sylowInner P).subtype) from
      fun x y h => Subtype.ext (Subtype.ext h))]
  obtain ⟨e⟩ := sylowInner_dihedral P
  exact DihedralGroup.center_card_of_equiv (n := 2) (by decide) e

/-- In a group acting fully on a normal A₆, the involution centralizers
of a four-group containing an inner involution generate the whole group. -/
theorem eq_top_of_four_involution_centralizers
    {J : Type*} [Group J] [Finite J]
    (K : Subgroup J) [K.Normal] (e : K ≃* A6)
    (hsurj : Function.Surjective (conjugationAction K e))
    (E : Subgroup J) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (z : K) (hz : orderOf z = 2) (hzE : (z : J) ∈ E)
    (N : Subgroup J)
    (hc : ∀ a : J, a ∈ E → orderOf a = 2 → centralizer ({a} : Set J) ≤ N) :
    N = ⊤ := by
  let α := conjugationAction K e
  have hzJ : orderOf (z : J) = 2 := (orderOf_coe z).trans hz
  have hzα : orderOf (α z) = 2 := by
    rw [conjugationAction_on_inner, orderOf_injective _ inner_injective, e.orderOf_eq, hz]
  have hzinner : α z ∈ inner := by
    rw [conjugationAction_on_inner]
    exact ⟨e z,rfl⟩
  obtain ⟨P,hP⟩ := inner_involution_centralizer_sylow (α z) hzα hzinner
  have hCiff (g : J) : α g ∈ centralizer ({α z} : Set AutA6) ↔
      g ∈ centralizer ({(z : J)} : Set J) := by
    rw [conjugationAction_on_inner,centralizer_inner_eq_stabilizer]
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, mem_centralizer_singleton_iff]
    change α g (e z) = e z ↔ g * (z : J) = (z : J) * g
    exact (mem_centralizer_iff_action_fixed K e g z).symm.trans
      (by rw [mem_centralizer_singleton_iff]; exact eq_comm)
  have hCmap : (centralizer ({(z : J)} : Set J)).map α = (P : Subgroup AutA6) := by
    rw [hP]
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      exact (hCiff g).mpr hg
    · intro a ha
      obtain ⟨g,rfl⟩ := hsurj a
      exact ⟨g,(hCiff g).mp ha,rfl⟩
  have hPN : (P : Subgroup AutA6) ≤ N.map α := by
    rw [←hCmap]
    exact map_mono (hc z hzE hzJ)
  have hkerN : α.ker ≤ N := by
    apply le_trans ?_ (hc z hzE hzJ)
    intro g hg
    apply (hCiff g).mp
    rw [show α g = 1 from hg]
    exact one_mem _
  have hNfull : N.map α = ⊤ := by
    rcases (sylow_isCoatom P).le_iff.mp hPN with ht | heq
    · exact ht
    exfalso
    have himage : E.map α ≤ innerSylowCenter P := by
      rintro _ ⟨a,ha,rfl⟩
      by_cases hone : α a = 1
      · rw [hone]
        exact one_mem _
      have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
      have haorder : orderOf a = 2 := orderOf_eq_prime ha2 (fun hh => hone (hh ▸ map_one α))
      have hαorder : orderOf (α a) = 2 := orderOf_eq_prime
        (by rw [←map_pow,ha2,map_one]) hone
      apply (involution_fixed_le_sylow_iff P (α a) hαorder).mp
      rintro _ ⟨v,hv,rfl⟩
      let k : K := e.symm v
      have hka : (k : J) ∈ centralizer ({a} : Set J) := by
        apply (mem_centralizer_iff_action_fixed K e a k).mpr
        simpa only [k,e.apply_symm_apply] using (show α a v = v from hv)
      have hm : α (k : J) ∈ N.map α := mem_map_of_mem α (hc a ha haorder hka)
      rw [heq] at hm
      simpa only [α,conjugationAction_on_inner,k,e.apply_symm_apply] using hm
    by_cases hd : E ⊓ α.ker = ⊥
    · have hinj : Function.Injective (α.subgroupMap E) := by
        rw [←MonoidHom.ker_eq_bot_iff,ker_subgroupMap,subgroupOf_eq_bot]
        exact (disjoint_iff.mpr hd).symm
      have hcard : Nat.card (E.map α) = 4 :=
        (Nat.card_congr (MulEquiv.ofBijective (α.subgroupMap E)
          ⟨hinj,α.subgroupMap_surjective E⟩).toEquiv).symm.trans hE
      have hle := card_le_of_le himage
      rw [hcard,innerSylowCenter_card] at hle
      omega
    · obtain ⟨⟨r,hr⟩,hne⟩ := ne_bot_iff_exists_ne_one.mp hd
      have hrorder : orderOf r = 2 := orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian r hr.1) (fun h => hne (Subtype.ext h))
      have hKN : K ≤ N := by
        intro k hk
        apply hc r hr.1 hrorder
        apply (mem_centralizer_iff_action_fixed K e r ⟨k,hk⟩).mpr
        rw [show conjugationAction K e r = 1 from hr.2]
        rfl
      have hi : inner ≤ (P : Subgroup AutA6) := by
        rw [←conjugationAction_map_inner K e,←heq]
        exact map_mono hKN
      have hdiv := card_dvd_of_le hi
      rw [card_inner,sylow_card] at hdiv
      norm_num at hdiv
  have hh := congrArg (Subgroup.comap α) hNfull
  rw [comap_map_eq,sup_eq_left.mpr hkerN,comap_top] at hh
  exact hh

end AlternatingSix.ShadowLocal
