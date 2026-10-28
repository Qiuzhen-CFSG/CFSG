module
public import Theory.Mathieu.M11.Properties.Centralizer
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.SpecificGroups.GL2.ThreeFourCentralizer
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# Normalizers of arbitrary four-subgroups in M₁₁

Every involution centralizer is GL₂(3), whose four-subgroups are
self-centralizing. In the sharply four-transitive action on eleven points,
each nonidentity element fixes at most three points. The union of the three
fixed sets therefore misses a point, giving a regular four-point orbit.
Every permutation of a Klein four-group is affine, so sharp transitivity
lifts all permutations of this orbit into its subgroup normalizer. The
self-centralizer bounds that normalizer by 4 · |Aut(E₄)| = 24, proving S₄.

This proves the intrinsic M₁₁ assertion of Aschbacher–Smith 2.5.8(5),
printed pp.556–557. The M₁₁ model is the original Witt-design carrier.
-/

open Subgroup
namespace Sporadic.Mathieu

/-- Every elementary four-subgroup of the actual Mathieu group is self-centralizing. -/
public theorem m11_four_centralizer (F : Subgroup M11) [IsKleinFour F] : centralizer (F : Set M11) = F := by
  classical
  let : IsElementaryAbelian 2 F :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp }
  have hcard : Nat.card F = 4 := IsKleinFour.card_four
  have hn : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : F)
  have hzo : orderOf (z : M11) = 2 := by
    apply orderOf_eq_prime
    · exact congrArg Subtype.val (by simpa only [pow_two] using IsKleinFour.mul_self z)
    · exact fun h => hz (Subtype.ext h)
  obtain ⟨g, hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA z hzo)
  let N := centralizer ({(z : M11)} : Set M11)
  have hCN : centralizer (F : Set M11) ≤ N :=
    centralizer_le (Set.singleton_subset_iff.mpr z.property)
  have hFN : F ≤ N := F.le_centralizer.trans hCN
  let A := F.subgroupOf N
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hFN
  let e : N ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.conj g) (z : M11)).trans
      ((MulEquiv.subgroupCongr (show centralizer ({MulAut.conj g (z : M11)} : Set M11) =
        m11InvolutionCentralizer by rw [show MulAut.conj g (z : M11) = m11GeneratorAInM11 from hg]; rfl)).trans
        m11InvolutionCentralizer_mulEquiv_gl2)
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hA : Nat.card (A.map e.toMonoidHom) = 4 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv, hcard]
  have hc := Matrix.GeneralLinearGroup.three_four_centralizer (A.map e.toMonoidHom) hA
  apply le_antisymm _ F.le_centralizer
  intro c hcF
  let c' : N := ⟨c, hCN hcF⟩
  have hec : e c' ∈ centralizer (A.map e.toMonoidHom : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    change e a * e c' = e c' * e a
    simpa only [map_mul] using congrArg e (show a * c' = c' * a from
      Subtype.ext (hcF a ha))
  rw [hc] at hec
  obtain ⟨a, ha, heq⟩ := hec
  have hae : a = c' := e.injective heq
  have hca : c' ∈ A := hae ▸ ha
  exact hca

private theorem fixed_card_le (g : M11) (hg : g ≠ 1) :
    (Finset.univ.filter fun x : Fin 11 => g • x = x).card ≤ 3 := by
  classical
  let fixed := Finset.univ.filter fun x : Fin 11 => g • x = x
  by_contra h
  change ¬ fixed.card ≤ 3 at h
  have hf : 4 ≤ Fintype.card ↥fixed := by rw [Fintype.card_coe]; omega
  let j : Fin 4 ↪ ↥fixed := (Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := ↥fixed) (by simpa using hf)).some
  let b : Fin 4 ↪ Fin 11 := j.trans (Function.Embedding.subtype _)
  have hb : g • b = b := by
    apply Function.Embedding.ext
    intro i
    exact (Finset.mem_filter.mp (j i).property).2
  apply hg
  exact (m11_isSharplyFourPretransitive.bijective_orbitMap b).injective (hb.trans (one_smul M11 b).symm)

private theorem exists_free_point (F : Subgroup M11) [IsKleinFour F] :
    ∃ x : Fin 11, ∀ f : F, f • x = x → f = 1 := by
  classical
  let bad := (Finset.univ.erase (1 : F)).biUnion
    (fun f => Finset.univ.filter fun x : Fin 11 => f • x = x)
  have hcard : bad.card ≤ 9 := calc
    bad.card ≤ ∑ f ∈ Finset.univ.erase (1 : F),
        (Finset.univ.filter fun x : Fin 11 => f • x = x).card := Finset.card_biUnion_le
    _ ≤ ∑ f ∈ Finset.univ.erase (1 : F), 3 := by
      apply Finset.sum_le_sum
      intro f hf
      exact fixed_card_le f (fun h => (Finset.mem_erase.mp hf).1 (Subtype.ext h))
    _ = 9 := by simp
  obtain ⟨x, hx⟩ : ∃ x : Fin 11, x ∉ bad := by
    by_contra h
    have he : bad = Finset.univ := Finset.eq_univ_iff_forall.mpr (by simpa using h)
    rw [he] at hcard
    norm_num at hcard
  refine ⟨x, fun f hf => ?_⟩
  by_contra hne
  exact hx (Finset.mem_biUnion.mpr ⟨f, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩)

private theorem normalizer_card_le (F : Subgroup M11) [IsKleinFour F]
    (hc : centralizer (F : Set M11) = F) : Nat.card (normalizer (F : Set M11)) ≤ 24 := by
  have hk : Nat.card F.normalizerMonoidHom.ker = 4 := by
    rw [F.normalizerMonoidHom_ker, hc,
      Nat.card_congr (subgroupOfEquivOfLe F.le_normalizer).toEquiv, IsKleinFour.card_four]
  have hr : Nat.card F.normalizerMonoidHom.range ≤ 6 := by
    simpa only [IsKleinFour.card_mulAut] using
      Nat.card_le_card_of_injective F.normalizerMonoidHom.range.subtype Subtype.val_injective
  have hh := F.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker, hk] at hh
  omega

private theorem affine (F : Type*) [Group F] [IsKleinFour F] (σ : Equiv.Perm F) (a b : F) :
    σ (a * b) = (σ a * (σ 1)⁻¹) * σ b := by
  let α : MulAut F := IsKleinFour.mulEquiv (σ.trans (Equiv.mulLeft (σ 1)⁻¹)) (by simp)
  have h := α.map_mul a b
  change (σ 1)⁻¹ * σ (a * b) = ((σ 1)⁻¹ * σ a) * ((σ 1)⁻¹ * σ b) at h
  calc
    σ (a * b) = σ 1 * ((σ 1)⁻¹ * σ (a * b)) := by group
    _ = σ 1 * (((σ 1)⁻¹ * σ a) * ((σ 1)⁻¹ * σ b)) := congrArg (σ 1 * ·) h
    _ = (σ a * (σ 1)⁻¹) * σ b := by group

private noncomputable instance fourFintype (F : Subgroup M11) : Fintype F := Fintype.ofFinite F

section Lift
variable (F : Subgroup M11) [IsKleinFour F]
variable (b : F ↪ Fin 11)

private noncomputable def fourTuple : Fin 4 ↪ Fin 11 :=
  (Fintype.equivFinOfCardEq (IsKleinFour.card_four' (G := F))).symm.toEmbedding.trans b

private theorem rigid (g h : M11) (he : ∀ f : F, g • b f = h • b f) : g = h := by
  apply (m11_isSharplyFourPretransitive.bijective_orbitMap (fourTuple F b)).injective
  apply Function.Embedding.ext
  intro i
  exact he _

private noncomputable def lift (σ : Equiv.Perm F) : M11 :=
  (m11_isSharplyFourPretransitive.existsUnique_smul_eq (fourTuple F b)
    (fourTuple F (σ.toEmbedding.trans b))).choose

private theorem lift_spec (σ : Equiv.Perm F) (f : F) :
    lift F b σ • b f = b (σ f) := by
  have hh := (m11_isSharplyFourPretransitive.existsUnique_smul_eq (fourTuple F b)
    (fourTuple F (σ.toEmbedding.trans b))).choose_spec.1
  have hi := congrArg (fun j : Fin 4 ↪ Fin 11 =>
    j ((Fintype.equivFinOfCardEq (IsKleinFour.card_four' (G := F))) f)) hh
  simpa [fourTuple, Function.Embedding.smul_apply, lift] using hi

private noncomputable def liftHom : Equiv.Perm F →* M11 where
  toFun := lift F b
  map_one' := by
    apply rigid F b
    intro f
    simpa using lift_spec F b 1 f
  map_mul' σ τ := by
    apply rigid F b
    intro f
    simp only [mul_smul, lift_spec, Equiv.Perm.mul_apply]

private theorem lift_injective : Function.Injective (liftHom F b) := by
  intro σ τ he
  apply Equiv.ext
  intro f
  apply b.injective
  rw [← lift_spec F b σ f, ← lift_spec F b τ f]
  exact congrArg (fun g : M11 => g • b f) he

private theorem lift_mem_normalizer
    (hb : ∀ (f h : F), (f : M11) • b h = b (f * h)) (σ : Equiv.Perm F) :
    liftHom F b σ ∈ normalizer (F : Set M11) := by
  let g := liftHom F b σ
  have hconj (f : F) : g * (f : M11) * g⁻¹ = ((σ f * (σ 1)⁻¹ : F) : M11) := by
    have hp : g * (f : M11) = ((σ f * (σ 1)⁻¹ : F) : M11) * g := by
      apply rigid F b
      intro h
      simp only [mul_smul, hb]
      change lift F b σ • b (f * h) = ((σ f * (σ 1)⁻¹ : F) : M11) • (lift F b σ • b h)
      rw [lift_spec, lift_spec, hb, affine]
    rw [hp]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨f, hf, rfl⟩
    change g * f * g⁻¹ ∈ F
    rw [hconj ⟨f,hf⟩]
    exact Subtype.property _
  · rw [card_map_of_injective (MulAut.conj g).injective]

private theorem normalizer_equiv_of_embedding
    (hb : ∀ (f h : F), (f : M11) • b h = b (f * h))
    (hc : centralizer (F : Set M11) = F) :
    Nonempty (normalizer (F : Set M11) ≃* Equiv.Perm (Fin 4)) := by
  let j : Equiv.Perm F →* normalizer (F : Set M11) :=
    (liftHom F b).codRestrict _ (lift_mem_normalizer F b hb)
  have hj : Function.Injective j := by
    intro σ τ h
    exact lift_injective F b (congrArg Subtype.val h)
  have hcard : Nat.card (normalizer (F : Set M11)) ≤ Nat.card (Equiv.Perm F) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm,
      IsKleinFour.card_four', Nat.factorial] using normalizer_card_le F hc
  let e := MulEquiv.ofBijective j (hj.bijective_of_nat_card_le hcard)
  exact ⟨e.symm.trans (Fintype.equivFinOfCardEq (IsKleinFour.card_four' (G := F))).permCongrHom⟩

end Lift

/-- The normalizer of every elementary four-subgroup of M11 is S4. -/
public theorem m11_four_normalizer (F : Subgroup M11) [IsKleinFour F] :
    Nonempty (normalizer (F : Set M11) ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨x, hx⟩ := exists_free_point F
  let b : F ↪ Fin 11 :=
    { toFun := fun f => f • x
      inj' := by
        intro f h he
        change f • x = h • x at he
        have hh : (h⁻¹ * f) • x = x := by rw [mul_smul, he, inv_smul_smul]
        exact (inv_mul_eq_one.mp (hx _ hh)).symm }
  apply normalizer_equiv_of_embedding F b _ (m11_four_centralizer F)
  intro f h
  exact (mul_smul f h x).symm

/-- Transport both intrinsic four-group conclusions through an actual M11 identification. -/
public theorem m11_four_structure_of_equiv {G : Type*} [Group G]
    (e : G ≃* M11) (F : Subgroup G) [IsKleinFour F] :
    centralizer (F : Set G) = F ∧
      Nonempty (normalizer (F : Set G) ≃* Equiv.Perm (Fin 4)) := by
  let A := F.map e.toMonoidHom
  let eF := e.subgroupMap F
  let : IsKleinFour A :=
    { card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eF.symm).trans IsKleinFour.exponent_two }
  have hc := m11_four_centralizer A
  let : IsMulCommutative F := IsKleinFour.isMulCommutative
  constructor
  · apply le_antisymm _ F.le_centralizer
    intro x hx
    have he : e x ∈ centralizer (A : Set M11) :=
      map_centralizer_le_centralizer_image (F : Set G) e.toMonoidHom ⟨x, hx, rfl⟩
    rw [hc] at he
    simpa only [e.symm_apply_apply] using (mem_map_equiv (f := e)).mp he
  · obtain ⟨h⟩ := m11_four_normalizer A
    exact ⟨((e.subgroupMap (normalizer (F : Set G))).trans
      (MulEquiv.subgroupCongr (map_equiv_normalizer_eq F e))).trans h⟩

end Sporadic.Mathieu

