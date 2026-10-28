module
public import Theory.GroupTheory.CentralProductPrimeProjection
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Combining inner implementations across commuting factors

For finitely many pairwise commuting subgroups, inner implementations on each
factor combine to an inner implementation on their join. An induction removes
one implementing factor at a time. This is the group-theoretic input for the
actual component orbit in Aschbacher--Smith 4.4.10, printed p.621.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem le_sup_centralizer_iSup_of_factorwise_inner {ι : Type*} [Finite ι]
    (K : ι → Subgroup G) (F : Subgroup G)
    (hc : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G))
    (hi : ∀ i, F ≤ K i ⊔ centralizer (K i : Set G)) :
    F ≤ (⨆ i, K i) ⊔ centralizer ((⨆ i, K i : Subgroup G) : Set G) := by
  classical
  let := Fintype.ofFinite ι
  have hs (s : Finset ι) : ∀ x : G,
      (∀ i ∈ s, x ∈ K i ⊔ centralizer (K i : Set G)) →
      x ∈ s.sup K ⊔ centralizer ((s.sup K : Subgroup G) : Set G) := by
    induction s using Finset.induction_on with
    | empty =>
      intro x _
      apply mem_sup_right
      intro y hy
      have hy1 : y = 1 := by
        change y ∈ (⊥ : Subgroup G) at hy
        exact mem_bot.mp hy
      subst y
      simp
    | @insert i s his ih =>
      intro x hx
      have hprod : x ∈ (K i : Set G) * (centralizer (K i : Set G) : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left (K i) (centralizer (K i : Set G))
          (Subgroup.centralizer_le_normalizer _)]
        exact hx i (Finset.mem_insert_self i s)
      obtain ⟨a,ha,c,hcK,rfl⟩ := hprod
      have hac (j : ι) (hj : j ∈ s) : a ∈ centralizer (K j : Set G) :=
        hc i j ((ne_of_mem_of_not_mem hj his).symm) ha
      have hci (j : ι) (hj : j ∈ s) : c ∈ K j ⊔ centralizer (K j : Set G) := by
        exact (K j ⊔ centralizer (K j : Set G)).mul_mem_cancel_left
          (mem_sup_right (hac j hj)) |>.mp (hx j (Finset.mem_insert_of_mem hj))
      have hrest := ih c hci
      have hprod' : c ∈ ((s.sup K : Subgroup G) : Set G) *
          (centralizer ((s.sup K : Subgroup G) : Set G) : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left (s.sup K)
          (centralizer ((s.sup K : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _)]
        exact hrest
      obtain ⟨b,hb,d,hd,rfl⟩ := hprod'
      have hbK : b ∈ centralizer (K i : Set G) :=
        (Finset.sup_le (fun j hj => hc j i (ne_of_mem_of_not_mem hj his))) hb
      have hdK : d ∈ centralizer (K i : Set G) :=
        (centralizer (K i : Set G)).mul_mem_cancel_left hbK |>.mp hcK
      have hdall : d ∈ centralizer ((K i ⊔ s.sup K : Subgroup G) : Set G) := by
        have hleft : K i ≤ centralizer (zpowers d : Set G) :=
          le_centralizer_iff.mp (zpowers_le.mpr hdK)
        have hright : s.sup K ≤ centralizer (zpowers d : Set G) :=
          le_centralizer_iff.mp (zpowers_le.mpr hd)
        exact (le_centralizer_iff.mp (sup_le hleft hright)) (mem_zpowers d)
      rw [Finset.sup_insert]
      change a * (b * d) ∈ _
      rw [←mul_assoc]
      exact mul_mem
        (mem_sup_left (mul_mem (mem_sup_left ha) (mem_sup_right hb)))
        (mem_sup_right hdall)
  intro x hx
  have hh := hs Finset.univ x (fun i _ => hi i hx)
  simpa only [Finset.sup_univ_eq_iSup] using hh

/-- Inner action on every actual conjugate combines on the component orbit. -/
theorem IsComponent.le_orbit_sup_centralizer_of_inner [Finite G]
    {K : Subgroup G} (hK : IsComponent G K) (A F : Subgroup G)
    (hi : ∀ a : A, F ≤ K.map (MulAut.conj (a : G)).toMonoidHom ⊔
      centralizer (K.map (MulAut.conj (a : G)).toMonoidHom : Set G)) :
    F ≤ componentOrbit K A ⊔ centralizer (componentOrbit K A : Set G) := by
  let c := fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom
  let I := {J : Subgroup G // J ∈ Set.range c}
  have hsup : (⨆ i : I, (i : Subgroup G)) = componentOrbit K A := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨J,a,rfl⟩
      exact le_iSup c a
    · exact iSup_le fun a => le_iSup (fun i : I => (i : Subgroup G)) ⟨c a,a,rfl⟩
  rw [←hsup]
  apply le_sup_centralizer_iSup_of_factorwise_inner (fun i : I => i.val) F
  · intro i j hij
    obtain ⟨a,ha⟩ := i.property
    obtain ⟨b,hb⟩ := j.property
    have hc := commutator_eq_bot_iff_le_centralizer.mp
      ((hK.map_conj (a : G)).commutator_eq_bot_of_ne (hK.map_conj (b : G))
        (fun he => hij (Subtype.ext (ha.symm.trans (he.trans hb)))))
    change c a ≤ centralizer (c b : Set G) at hc
    rw [ha,hb] at hc
    exact hc
  · rintro ⟨J,a,rfl⟩
    exact hi a

/-- An invariant actor's inner implementation on one component transports to
its entire conjugate orbit. -/
theorem IsComponent.le_orbit_sup_centralizer_of_normalized_inner [Finite G]
    {K : Subgroup G} (hK : IsComponent G K) (A F : Subgroup G)
    (hAF : A ≤ normalizer (F : Set G))
    (hi : F ≤ K ⊔ centralizer (K : Set G)) :
    F ≤ componentOrbit K A ⊔ centralizer (componentOrbit K A : Set G) := by
  apply hK.le_orbit_sup_centralizer_of_inner A F
  intro a
  have hF : F.map (MulAut.conj (a : G)).toMonoidHom = F :=
    mem_normalizer_iff_map_conj_eq.mp (hAF a.property)
  have hh := map_mono (f := (MulAut.conj (a : G)).toMonoidHom) hi
  rw [Subgroup.map_sup,hF] at hh
  exact hh.trans (sup_le_sup le_rfl (map_centralizer_le_centralizer_image _ _))

/-- A separate normalization actor allows the original uniqueness subgroup
to retain all its factors when the centralizer projection is eliminated. -/
theorem binary_subgroup_le_of_normalized_inner_product_uniqueness [Finite G]
    (K V A I M : Subgroup G) (hV : IsPGroup 2 V)
    (hVK : V ≤ K ⊔ centralizer (K : Set G))
    (hAK : A ≤ normalizer (K : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (hIA : I ≤ A)
    (hu : ∀ H : Subgroup G, IsMaximalTwoLocal H → I ≤ H → H = M)
    (hout : ¬ K ≤ M) : V ≤ K := by
  obtain ⟨Q,hQC,hQ,hAQ,hVQ⟩ := exists_prime_projection_of_central_product
    K (centralizer (K : Set G)) V A (le_centralizer_iff.mpr le_rfl)
    hV hVK hAK (hAK.trans (normalizer_le_normalizer_centralizer K)) hAV
  have hbot : Q = ⊥ := by
    by_contra hn
    have hNM := normalizer_le_of_unique_maximalTwoLocal hu hQ hn (hIA.trans hAQ)
    exact hout ((le_centralizer_iff.mp hQC).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNM))
  simpa only [hbot,sup_bot_eq] using hVQ

end Theory.GroupTheory
