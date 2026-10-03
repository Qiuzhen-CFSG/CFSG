module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Transfer on a self-normalizing subgroup

Let `H` be a self-normalizing subgroup of a finite group `G`, and let
`φ : H →* A` have commutative codomain. If every transfer from a proper
subgroup of `H` vanishes on `u : H`, then the transfer of `φ` from `G`
takes `u` to `φ u`.

The proof establishes the required ordinary Mackey formula privately.
Decompose the left coset space `G/H` into `H`-orbits and identify each orbit
with the cosets of its stabilizer in `H`. Choose a representative of each
orbit and representatives of these stabilizer cosets. Their products give
a left transversal of `H` in `G`, adapted to the orbit decomposition.
Expanding Mathlib's transfer with this transversal shows that each orbit
contributes the transfer of the homomorphism obtained by conjugating its
stabilizer back into `H` and applying `φ`.

A coset fixed by all of `H` has a representative in the normalizer of `H`;
finiteness is essential for this implication. Self-normalization therefore
leaves only the identity coset as a fixed orbit. All other stabilizers are
proper, so their transfer terms vanish by hypothesis. The remaining term
is `φ u`, since its representative lies in `H` and `A` is commutative.

This is the self-subgroup specialization of the ordinary transfer Mackey
formula in Gorenstein--Lyons--Solomon, No. 2, Lemma 15.13 (printed p. 92;
`refs/KGroup/GLS2/ChapterD.tex`). It supplies the final ordinary-transfer
step in Andersen--Oliver--Ventura, Proposition 2.3(b), independently of any
fusion-system or classification hypotheses. All coset and intersection
constructions are private; the public statement uses Mathlib's transfer.
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

private theorem transfer_stabilizer_top [Finite G] (φ : H →* A) (u : H)
    (q : G ⧸ H) (hq : stabilizer H q = ⊤) (hout : q.out ∈ H) :
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
  · let x : H := ⟨q.out, hout⟩
    simp only [inv_one, one_mul, mul_one]
    change φ (x⁻¹ * u * x) = φ u
    simp [map_mul, mul_comm, mul_left_comm]
  · intro s hs
    exact (hs (Subsingleton.elim _ _)).elim

/-- Proper-subgroup transfer terms vanish, leaving the self-normalizer term. -/
public theorem transfer_eq_self_of_self_normalizing [Finite G]
    (hN : normalizer (H : Set G) = H)
    (φ : H →* A) (u : H)
    (hvanish : ∀ K : Subgroup H, K ≠ ⊤ →
      ∀ ψ : K →* A, transfer ψ u = 1) :
    transfer φ (u : G) = φ u := by
  classical
  let : Fintype (orbitIndex H) := Fintype.ofFinite _
  let ω₀ : orbitIndex H := Quotient.mk'' ((1 : G) : G ⧸ H)
  have hfixed : ((1 : G) : G ⧸ H) ∈ fixedPoints H (G ⧸ H) :=
    Sylow.mem_fixedPoints_mul_left_cosets_iff_mem_normalizer.mpr
      (Subgroup.one_mem (normalizer (H : Set G)))
  have hout : ω₀.out = ((1 : G) : G ⧸ H) :=
    mem_fixedPoints'.mp hfixed _ (Quotient.exact' (Quotient.out_eq' ω₀))
  have htop : stabilizer H ω₀.out = ⊤ := by
    apply top_unique
    intro h _
    rw [hout]
    exact hfixed h
  rw [transfer_eq_prod_stabilizer H φ u, Fintype.prod_eq_single ω₀]
  · apply transfer_stabilizer_top H φ u _ htop
    exact hN.le (stabilizer_top_out_mem_normalizer H ω₀.out htop)
  · intro ω hω
    apply hvanish
    intro hstab
    apply hω
    have hx : ω.out.out ∈ H := hN.le (stabilizer_top_out_mem_normalizer H ω.out hstab)
    have hq : ω.out = ((1 : G) : G ⧸ H) := by
      rw [← QuotientGroup.out_eq' ω.out]
      exact QuotientGroup.eq.mpr (by simpa using H.inv_mem hx)
    calc
      ω = Quotient.mk'' ω.out := (Quotient.out_eq' ω).symm
      _ = ω₀ := congrArg Quotient.mk'' hq

end MonoidHom
