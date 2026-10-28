module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FixedKernel

/-!
# The whole source Cartan image in the faithful panel

H maps into the intersection of the faithful Borel with its reflected
Borel. If this two-point subgroup has odd order, the map is onto. Indeed,
a representative in the original Borel intersection factors as v h with
v in U ∩ U^s. The image of v lies in the odd two-point subgroup and has
two-power order, hence vanishes. Both the full Borel and the chosen
reflection are preserved by the model equivalence.

This supplies the actual Cartan-image equality needed for the q−1 order
calculation in Fong–Seitz I (6H)(a), p.51. RankOneOrders discharges oddness
from the natural linear and Suzuki markings. It does not assume that
unrelated abstract tori are the source Cartan images.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The literal two-point subgroup of the actual faithful panel quotient. -/
def panelCartanPair (s : RootReflection Q split i) : Subgroup (Endpoint Q i ⧸ panelKernel Q i) :=
  quotientBorel Q i ⊓ rightConjugate (quotientBorel Q i)
    (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s))

theorem cartanPanelMap_range_le_pair (s : RootReflection Q split i) :
    (cartanPanelMap Q i).range ≤ panelCartanPair Q split i s := by
  rintro x ⟨h,rfl⟩
  refine ⟨cartanPanelMap_mem_borel Q i h, ?_⟩
  let a := normalizerCartanAction Q s.val h
  have he : cartanPanelMap Q i a =
      QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s) *
        cartanPanelMap Q i h *
          (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s))⁻¹ := by
    simp only [cartanPanelMap_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  change (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s)) *
    cartanPanelMap Q i h * (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s))⁻¹ ∈ quotientBorel Q i
  rw [← he]
  exact cartanPanelMap_mem_borel Q i a

/-- Removing the two-part of the original Borel intersection proves surjectivity
onto an odd faithful two-point subgroup. -/
theorem cartanPanelMap_range_eq_pair (s : RootReflection Q split i)
    (hodd : Nat.Coprime 2 (Nat.card (panelCartanPair Q split i s))) :
    (cartanPanelMap Q i).range = panelCartanPair Q split i s := by
  apply le_antisymm (cartanPanelMap_range_le_pair Q split i s)
  intro x hx
  obtain ⟨b,hb,hbx⟩ := hx.1
  let n := rootReflectionEndpoint Q split i s
  let q := QuotientGroup.mk' (panelKernel Q i)
  have hbconj : (n : X ⧸ Q.D)*(b : X ⧸ Q.D)*(n : X ⧸ Q.D)⁻¹ ∈ Q.tits.B := by
    have hc : n*b*n⁻¹ ∈ (quotientBorel Q i).comap q := by
      change q (n*b*n⁻¹) ∈ quotientBorel Q i
      rw [map_mul, map_mul, map_inv, hbx]
      exact hx.2
    rwa [quotientBorel_comap] at hc
  have hbpair : (b : X ⧸ Q.D) ∈ Q.tits.B ⊓ rightConjugate Q.tits.B (s.val : X ⧸ Q.D) :=
    ⟨hb,hbconj⟩
  change (b : X ⧸ Q.D) ∈ ((Q.tits.B ⊓ rightConjugate Q.tits.B (s.val : X ⧸ Q.D) : Subgroup _) : Set _) at hbpair
  rw [borel_intersection_factorization split s.val] at hbpair
  obtain ⟨v,hv,a,ha,hva⟩ := hbpair
  let vP : Endpoint Q i := ⟨v,Q.tits.B_le_standardParabolic _ (split.U_le hv.1)⟩
  let aH : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := ⟨a,ha⟩
  have hp : q vP * cartanPanelMap Q i aH = x := by
    rw [cartanPanelMap_apply, ← map_mul, ← hbx]
    apply congrArg q
    exact Subtype.ext hva
  have hpv : q vP ∈ panelCartanPair Q split i s := by
    have he : q vP = x * (cartanPanelMap Q i aH)⁻¹ :=
      eq_mul_inv_iff_mul_eq.mpr hp
    rw [he]
    exact (panelCartanPair Q split i s).mul_mem hx
      ((panelCartanPair Q split i s).inv_mem (cartanPanelMap_range_le_pair Q split i s ⟨aH,rfl⟩))
  obtain ⟨k,hk⟩ := split.isTwo (⟨v,hv.1⟩ : split.U)
  have hvk : vP^(2^k) = 1 := Subtype.ext (congrArg (fun u : split.U => (u : X ⧸ Q.D)) hk)
  let z : panelCartanPair Q split i s := ⟨q vP,hpv⟩
  have hzk : z^(2^k) = 1 := by
    apply Subtype.ext
    change (q vP)^(2^k) = 1
    rw [← map_pow, hvk, map_one]
  have hz : z = 1 := (hodd.symm.pow_right k).pow_left_bijective.injective
    (hzk.trans (one_pow (2^k)).symm)
  have hqv : q vP = 1 := congrArg Subtype.val hz
  rw [hqv, one_mul] at hp
  exact ⟨aH,hp⟩


/-- Exact transport of the faithful two-point subgroup, using the same reflection. -/
theorem panelCartanPair_map {M : Type*} [Group M]
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M)
    (B : Subgroup M) (hB : (quotientBorel Q i).map μ.toMonoidHom = B)
    (s : RootReflection Q split i) :
    (panelCartanPair Q split i s).map μ.toMonoidHom = B ⊓ rightConjugate B
      (μ (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s))) := by
  have hb (x : Endpoint Q i ⧸ panelKernel Q i) : μ x ∈ B ↔ x ∈ quotientBorel Q i := by
    rw [← hB, mem_map_equiv, μ.symm_apply_apply]
  ext y
  rw [mem_map_equiv]
  change (μ.symm y ∈ quotientBorel Q i ∧
    (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s)) * μ.symm y *
      (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s))⁻¹ ∈ quotientBorel Q i) ↔
    (y ∈ B ∧ μ (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s)) * y *
      (μ (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s)))⁻¹ ∈ B)
  rw [← hb, ← hb, μ.apply_symm_apply, map_mul, map_mul, map_inv, μ.apply_symm_apply]

def panelCartanPairEquiv {M : Type*} [Group M]
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M)
    (B : Subgroup M) (hB : (quotientBorel Q i).map μ.toMonoidHom = B)
    (s : RootReflection Q split i) : panelCartanPair Q split i s ≃*
      (B ⊓ rightConjugate B
        (μ (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s))) : Subgroup M) :=
  (μ.subgroupMap _).trans (MulEquiv.subgroupCongr (panelCartanPair_map Q split i μ B hB s))

@[simp] theorem panelCartanPairEquiv_apply {M : Type*} [Group M]
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M)
    (B : Subgroup M) (hB : (quotientBorel Q i).map μ.toMonoidHom = B)
    (s : RootReflection Q split i) (x : panelCartanPair Q split i s) :
    (panelCartanPairEquiv Q split i μ B hB s x : M) = μ x := rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
