module

public import Theory.GroupTheory.TransferSelfNormalizer
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transfer with an automorphism-invariant involution image

Suppose all proper-subgroup transfers vanish on an element of a subgroup,
and every automorphism preserves its image in a commutative target. If
that image has square one and all proper subgroups have even index, then
ambient transfer is the index power of the image.

The Mackey decomposition uses the same orbit-adapted transversal as
`TransferSelfNormalizer` (whose private construction is repeated here to
preserve its API). Each proper stabilizer contributes one, equal to the
corresponding even power. A full stabilizer contributes the original image
because its representative normalizes the subgroup. Orbit indices sum to
the ambient index.

Source: the ordinary transfer Mackey formula, Gorenstein--Lyons--Solomon,
No. 2, Lemma 15.13, and Andersen--Oliver--Ventura, *Fusion systems and
amalgams*, Proposition 2.3(b).
-/

open scoped Pointwise BigOperators
open MulAction Subgroup

namespace MonoidHom

variable {G A : Type*} [Group G] [CommGroup A]
variable (H : Subgroup G)

private theorem sectionTerm_mem (r : G ⧸ H → G) (hr : ∀ q, (r q : G ⧸ H) = q)
    (g : G) (q : G ⧸ H) : (r q)⁻¹ * g * r (g⁻¹ • q) ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, hr]
  change q = g • (r (g⁻¹ • q) : G ⧸ H)
  rw [hr, smul_inv_smul]

private theorem transfer_eq_prod_section [Finite G] (φ : H →* A)
    (r : G ⧸ H → G) (hr : ∀ q, (r q : G ⧸ H) = q) (g : G)
    [Fintype (G ⧸ H)] :
    transfer φ g = ∏ q : G ⧸ H,
      φ ⟨(r q)⁻¹ * g * r (g⁻¹ • q), sectionTerm_mem H r hr g q⟩ := by
  let T : H.LeftTransversal := ⟨Set.range r, isComplement_range_left hr⟩
  rw [transfer_def φ T]
  unfold leftTransversals.diff
  dsimp only
  rw [Subsingleton.elim H.fintypeQuotientOfFiniteIndex ‹Fintype (G ⧸ H)›]
  refine Fintype.prod_congr (α := G ⧸ H) (M := A) _ _ ?_
  intro q
  congr 1
  apply Subtype.ext
  change ((T.2.leftQuotientEquiv q : G)⁻¹ *
    ((g • T).2.leftQuotientEquiv q : G)) = _
  rw [smul_apply_eq_smul_apply_inv_smul]
  simp only [T, IsComplement.leftQuotientEquiv_apply hr, smul_eq_mul, mul_assoc]

private abbrev orbitIndex := orbitRel.Quotient H (G ⧸ H)

private noncomputable def cosetOrbitEquiv :
    G ⧸ H ≃ Σ ω : orbitIndex H, H ⧸ stabilizer H ω.out :=
  selfEquivSigmaOrbitsQuotientStabilizer H (G ⧸ H)

private theorem cosetOrbitEquiv_symm (ω : orbitIndex H)
    (q : H ⧸ stabilizer H ω.out) :
    (cosetOrbitEquiv H).symm ⟨ω, q⟩ = ofQuotientStabilizer H ω.out q := rfl

private theorem cosetOrbitEquiv_symm_smul (ω : orbitIndex H)
    (q : H ⧸ stabilizer H ω.out) (u : H) :
    (cosetOrbitEquiv H).symm ⟨ω, u • q⟩ =
      (u : G) • (cosetOrbitEquiv H).symm ⟨ω, q⟩ := by
  rw [cosetOrbitEquiv_symm, cosetOrbitEquiv_symm, ofQuotientStabilizer_smul]
  rfl

private noncomputable def orbitSection (q : G ⧸ H) : G :=
  (((cosetOrbitEquiv H q).2.out : H) : G) * (cosetOrbitEquiv H q).1.out.out

private theorem orbitSection_symm (ω : orbitIndex H)
    (q : H ⧸ stabilizer H ω.out) :
    orbitSection H ((cosetOrbitEquiv H).symm ⟨ω,q⟩) =
      (q.out : G) * ω.out.out := by
  unfold orbitSection
  generalize h : (cosetOrbitEquiv H) ((cosetOrbitEquiv H).symm ⟨ω,q⟩) = y
  have hy : y = ⟨ω,q⟩ := h.symm.trans ((cosetOrbitEquiv H).apply_symm_apply _)
  cases hy
  rfl

private theorem orbitSection_eq (q : G ⧸ H) :
    ((orbitSection H q : G) : G ⧸ H) = q := by
  obtain ⟨⟨ω, s⟩, rfl⟩ := (cosetOrbitEquiv H).symm.surjective q
  rw [orbitSection_symm, cosetOrbitEquiv_symm]
  have h : s = (s.out : H ⧸ stabilizer H ω.out) := (Quotient.out_eq' s).symm
  conv_rhs => rw [h, ofQuotientStabilizer_mk]
  exact Quotient.coe_smul_out H (s.out : G) ω.out

private noncomputable def orbitConjugate (q : G ⧸ H) : stabilizer H q →* H where
  toFun k := ⟨q.out⁻¹ * (k : H) * q.out, by
    rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq']
    change q = ((k : H) : G) • (q.out : G ⧸ H)
    rw [QuotientGroup.out_eq']
    exact k.property.symm⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [mul_assoc]

private theorem transfer_eq_prod_stabilizer [Finite G] (φ : H →* A) (u : H)
    [Fintype (orbitIndex H)] :
    transfer φ (u : G) =
      ∏ ω : orbitIndex H, transfer (φ.comp (orbitConjugate H ω.out)) u := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let (ω : orbitIndex H) : Fintype (H ⧸ stabilizer H ω.out) := Fintype.ofFinite _
  rw [transfer_eq_prod_section H φ (orbitSection H) (orbitSection_eq H) (u : G)]
  rw [← (cosetOrbitEquiv H).symm.prod_comp]
  rw [Fintype.prod_sigma]
  refine Fintype.prod_congr _ _ fun ω => ?_
  rw [transfer_eq_prod_section (stabilizer H ω.out) _ Quotient.out Quotient.out_eq' u]
  refine Fintype.prod_congr _ _ fun q => ?_
  change φ _ = φ _
  congr 1
  apply Subtype.ext
  change (orbitSection H ((cosetOrbitEquiv H).symm ⟨ω,q⟩))⁻¹ * (u : G) *
      orbitSection H ((u : G)⁻¹ • (cosetOrbitEquiv H).symm ⟨ω,q⟩) =
    ω.out.out⁻¹ * (((q.out : H)⁻¹ * u * (u⁻¹ • q).out : H) : G) * ω.out.out
  rw [← Subgroup.coe_inv, ← cosetOrbitEquiv_symm_smul H ω q u⁻¹,
    orbitSection_symm, orbitSection_symm]
  simp only [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]

private theorem stabilizer_top_out_mem_normalizer [Finite G] (q : G ⧸ H)
    (hq : stabilizer H q = ⊤) : q.out ∈ normalizer (H : Set G) := by
  apply Sylow.mem_fixedPoints_mul_left_cosets_iff_mem_normalizer.mp
  rw [QuotientGroup.out_eq']
  intro h
  exact (show h ∈ stabilizer H q by rw [hq]; trivial)

private theorem transfer_stabilizer_top_invariant [Finite G]
    (φ : H →* A) (u : H) (hinvariant : ∀ f : MulAut H, φ (f u) = φ u)
    (q : G ⧸ H) (hq : stabilizer H q = ⊤) :
    transfer (φ.comp (orbitConjugate H q)) u = φ u := by
  classical
  let K := stabilizer H q
  let : Subsingleton (H ⧸ K) := by
    change Subsingleton (H ⧸ stabilizer H q)
    rw [hq]
    exact QuotientGroup.subsingleton_quotient_top
  let : Fintype (H ⧸ K) := Fintype.ofFinite _
  have hr (s : H ⧸ K) : ((1 : H) : H ⧸ K) = s := Subsingleton.elim _ _
  rw [transfer_eq_prod_section K _ (fun _ => 1) hr u]
  rw [Fintype.prod_eq_single ((1 : H) : H ⧸ K)]
  · have hn := stabilizer_top_out_mem_normalizer H q hq
    let n : normalizer (H : Set G) := ⟨q.out, hn⟩
    refine Eq.trans ?_ (hinvariant (H.normalizerMonoidHom n⁻¹))
    change φ (orbitConjugate H q _) = φ (H.normalizerMonoidHom n⁻¹ u)
    apply congrArg φ
    apply Subtype.ext
    simp [orbitConjugate, Subgroup.normalizerMonoidHom, n,
      MulDistribMulAction.toMulAut]
    change q.out⁻¹ * (u : G) * q.out = q.out⁻¹ * (u : G) * (q.out⁻¹)⁻¹
    rw [inv_inv]
  · intro s hs
    exact (hs (Subsingleton.elim _ _)).elim

/-- Proper-subgroup vanishing and invariance under automorphisms evaluate transfer. -/
public theorem transfer_eq_pow_of_automorphism_invariant [Finite G]
    (φ : H →* A) (u : H)
    (hsquare : (φ u) ^ 2 = 1)
    (hinvariant : ∀ f : MulAut H, φ (f u) = φ u)
    (heven : ∀ K : Subgroup H, K ≠ ⊤ → 2 ∣ K.index)
    (hvanish : ∀ K : Subgroup H, K ≠ ⊤ →
      ∀ ψ : K →* A, transfer ψ u = 1) :
    transfer φ (u : G) = φ u ^ H.index := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let : Fintype (orbitIndex H) := Fintype.ofFinite _
  let (ω : orbitIndex H) : Fintype (H ⧸ stabilizer H ω.out) := Fintype.ofFinite _
  have hsum : ∑ ω : orbitIndex H, (stabilizer H ω.out).index = H.index := by
    simp only [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (cosetOrbitEquiv H).symm
  rw [transfer_eq_prod_stabilizer H φ u]
  calc
    _ = ∏ ω : orbitIndex H, φ u ^ (stabilizer H ω.out).index := by
      apply Fintype.prod_congr
      intro ω
      by_cases htop : stabilizer H ω.out = ⊤
      · rw [transfer_stabilizer_top_invariant H φ u hinvariant _ htop,
          htop, Subgroup.index_top, pow_one]
      · rw [hvanish _ htop]
        obtain ⟨k, hk⟩ := heven _ htop
        rw [hk, pow_mul, hsquare, one_pow]
    _ = φ u ^ H.index := by rw [Finset.prod_pow_eq_pow_sum, hsum]

end MonoidHom
