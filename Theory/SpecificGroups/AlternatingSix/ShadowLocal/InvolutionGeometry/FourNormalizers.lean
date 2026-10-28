module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Automorphisms
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Selection
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Fusion

/-!
# Four-group normalizers and compatible outer complements in A₆

Every Klein four-group in the actual A₆ has normalizer S₄. Its normalizer
in Aut(A₆) is the direct product of the specified inner normalizer and an
outer involution fixing it pointwise. The multiplication equivalence below
retains both embeddings, and gives the order 48 and the S₄ × C₂ model.
The marked calculation transports through the actual exceptional automorphism,
which interchanges the two classes of four-groups.

The re-exported selection theorem chooses the four-group appropriate to a
transposition centralizing a Sylow two-subgroup. The fusion theorems give
normalizer transitivity and an actual coboundary witness for each outside
involution. The S₄ identification and coboundary result retain exactly the
uniform transposition-fixed-subgroup premise; the source assembly must supply it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.567–570, especially the final argument
on p.570. This is a conditional local-model helper, not the source assembly.
-/

public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal.FourNormalizers

/-- An outer involution complements the inner normalizer and fixes it pointwise. -/
theorem exists_outer_complement (F : Subgroup A6) [IsKleinFour F] :
    ∃ τ : AutA6, orderOf τ = 2 ∧ τ ∉ inner ∧
      (∀ g ∈ normalizer (F : Set A6), τ g = g) ∧
      normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) =
        (normalizer (F : Set A6)).map (MulAut.conj : A6 →* AutA6) ⊔ zpowers τ ∧
      Disjoint ((normalizer (F : Set A6)).map (MulAut.conj : A6 →* AutA6)) (zpowers τ) := by
  obtain ⟨α, rfl⟩ := exists_map_standardFour F
  let τ := (MulAut.conj α) (permutationAction tailSwap)
  have hN := map_equiv_normalizer_eq standardFour α
  have hH : ((normalizer (standardFour : Set A6)).map (MulAut.conj : A6 →* AutA6)).map
      (MulAut.conj α).toMonoidHom =
      (normalizer (standardFour.map α.toMonoidHom : Set A6)).map (MulAut.conj : A6 →* AutA6) := by
    rw [inner_map_transport, hN]
  have hA : (normalizer (standardFour.map (MulAut.conj : A6 →* AutA6) : Set AutA6)).map
      (MulAut.conj α).toMonoidHom =
      normalizer ((standardFour.map α.toMonoidHom).map (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
    rw [map_equiv_normalizer_eq, inner_map_transport]
  have hz : (zpowers (permutationAction tailSwap)).map (MulAut.conj α).toMonoidHom = zpowers τ :=
    MonoidHom.map_zpowers _ _
  refine ⟨τ, ((MulAut.conj α).orderOf_eq _).trans tailSwap_order, ?_, ?_, ?_, ?_⟩
  · intro hi
    have hc := inner_normal.conj_mem τ hi α⁻¹
    apply tailSwap_not_inner
    simpa [τ, MulAut.conj_apply, mul_assoc] using hc
  · intro g hg
    rw [← hN, mem_map_equiv] at hg
    change α (permutationAction tailSwap (α.symm g)) = g
    rw [tailSwap_fixes_normalizer _ hg, α.apply_symm_apply]
  · rw [← hA, standard_aut_normalizer_eq, Subgroup.map_sup, hH, hz]
  · have hd := Subgroup.disjoint_map (f := (MulAut.conj α).toMonoidHom)
      (MulAut.conj α).injective standard_complement_disjoint
    rwa [hH, hz] at hd

/-- The product isomorphism preserves the specified inner embedding. -/
theorem exists_compatible_product (F : Subgroup A6) [IsKleinFour F] :
    ∃ τ : AutA6, orderOf τ = 2 ∧ τ ∉ inner ∧
      (∀ g ∈ normalizer (F : Set A6), τ g = g) ∧
      ∃ e : (normalizer (F : Set A6)) × zpowers τ ≃*
        normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6),
        ∀ g z, (e (g, z) : AutA6) = MulAut.conj (g : A6) * (z : AutA6) := by
  obtain ⟨τ, ht, ho, hfix, heq, hd⟩ := exists_outer_complement F
  have hc : (normalizer (F : Set A6)).map (MulAut.conj : A6 →* AutA6) ≤
      centralizer (zpowers τ : Set AutA6) := by
    rintro _ ⟨g, hg, rfl⟩ z ⟨n, rfl⟩
    have h := aut_conj_inner τ g
    rw [hfix g hg, mul_inv_eq_iff_eq_mul] at h
    exact (Commute.zpow_left h n).eq
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc
  let eI := (normalizer (F : Set A6)).equivMapOfInjective
    (MulAut.conj : A6 →* AutA6) inner_injective
  refine ⟨τ, ht, ho, hfix,
    ((eI.prodCongr (MulEquiv.refl _)).trans e).trans (MulEquiv.subgroupCongr heq.symm), ?_⟩
  intro g z
  exact he (eI g) z

/-- The full automorphism normalizer has order 48. -/
theorem aut_normalizer_card
    (htransS4 : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap →
      Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Equiv.Perm (Fin 4)))
    (F : Subgroup A6) [IsKleinFour F] :
    Nat.card (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6)) = 48 := by
  obtain ⟨τ, ht, _, _, e, _⟩ := exists_compatible_product F
  obtain ⟨eS⟩ := normalizer_equiv_symmetric htransS4 F
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, ht,
    Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

/-- The abstract product model follows from the compatible multiplication model. -/
theorem aut_normalizer_equiv_symmetric_prod
    (htransS4 : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap →
      Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Equiv.Perm (Fin 4)))
    (F : Subgroup A6) [IsKleinFour F] :
    Nonempty (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) ≃*
      (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))) := by
  obtain ⟨τ, ht, _, _, e, _⟩ := exists_compatible_product F
  obtain ⟨eS⟩ := normalizer_equiv_symmetric htransS4 F
  have hcard : Nat.card (zpowers τ) = Nat.card (Multiplicative (ZMod 2)) := by
    rw [Nat.card_zpowers, ht]
    simp
  let eZ : zpowers τ ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq hcard
  exact ⟨e.symm.trans (eS.prodCongr eZ)⟩
/-- Any outer automorphism normalizing a four-group generates its full
normalizer together with the inner normalizer. -/
theorem outer_normalizer_generates (F : Subgroup A6) [IsKleinFour F]
    (a : AutA6) (ha : a ∉ inner) (haF : F.map a.toMonoidHom = F)
    (b : AutA6) (hbF : F.map b.toMonoidHom = F) :
    b ∈ zpowers a ⊔ (normalizer (F : Set A6)).map (MulAut.conj : A6 →* AutA6) := by
  obtain ⟨τ, ht, _, _, e, he⟩ := exists_compatible_product F
  let J := zpowers a ⊔ (normalizer (F : Set A6)).map (MulAut.conj : A6 →* AutA6)
  obtain ⟨⟨g, z⟩, hgz⟩ := e.surjective
    ⟨a, (mem_inner_normalizer_iff F a).mpr haF⟩
  have haeq : MulAut.conj (g : A6) * (z : AutA6) = a :=
    (he g z).symm.trans (congrArg Subtype.val hgz)
  have hzne : z ≠ 1 := by
    intro hz
    apply ha
    rw [← haeq, hz, coe_one, mul_one]
    exact ⟨g, rfl⟩
  have hzJ : (z : AutA6) ∈ J := by
    have hgJ : MulAut.conj (g : A6) ∈ J := mem_sup_right ⟨g, g.property, rfl⟩
    have haJ : a ∈ J := mem_sup_left (mem_zpowers a)
    have h := J.mul_mem (J.inv_mem hgJ) haJ
    rw [← haeq] at h
    simpa [mul_assoc] using h
  have htJ : τ ∈ J := by
    have hgen : (⟨τ, mem_zpowers τ⟩ : zpowers τ) ∈ zpowers z :=
      mem_zpowers_of_prime_card (show Nat.card (zpowers τ) = 2 by rw [Nat.card_zpowers, ht]) hzne
    obtain ⟨n, hn⟩ := hgen
    have hn' : (z : AutA6) ^ n = τ := congrArg Subtype.val hn
    exact hn' ▸ J.zpow_mem hzJ n
  obtain ⟨⟨g', z'⟩, hgz'⟩ := e.surjective
    ⟨b, (mem_inner_normalizer_iff F b).mpr hbF⟩
  have hbeq : MulAut.conj (g' : A6) * (z' : AutA6) = b :=
    (he g' z').symm.trans (congrArg Subtype.val hgz')
  rw [← hbeq]
  exact J.mul_mem (mem_sup_right ⟨g', g'.property, rfl⟩) ((zpowers_le.mpr htJ) z'.property)

end AlternatingSix.ShadowLocal.FourNormalizers
