module

public import Theory.Representation.HexacodeAction.PairGeometry
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic.Cosets
public import Theory.Representation.BinaryOffender.EquivariantStabilizer

/-!
# The actual quotient at a weight-four hexacode point

Evaluation on the two zero coordinates identifies the quotient by a
double-zero point with two binary letters. Three explicit even words
induce a cubic on one letter, simultaneous scalar rotations, and an
interchange of the letters. These operations force every invariant
subspace to be zero or the whole quotient. Even coordinate conjugacy
transports the calculation to every pair.

Source: Aschbacher--Smith12.7.2(3), printed p.839. The literal hexacode,
coordinate lifts and letter maps are the attributed ATLAS constructions.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender BinaryPermutation.SixPairsQuadratic

private def firstPair : Pair := ⟨{0,1},by decide⟩
private def diagonal : HexEvenAutomorphisms := ⟨hexLift 2 * hexLift 3,by simp⟩
private def exchange : HexEvenAutomorphisms := ⟨hexLift 0 * hexLift 2,by simp⟩

private def evaluation : hexacode →ₗ[Bit] (K × K) :=
  (hexCoordinate (hexPos 0)).prod (hexCoordinate (hexPos 1))

private theorem evaluation_kernel : evaluation.ker = zeroPairPlane firstPair := by
  ext v
  change (v.val (hexPos 0),v.val (hexPos 1)) = (0,0) ↔
    ∀ i ∈ ({0,1} : Finset (Fin 6)), v.val (hexPos i) = 0
  simp only [Prod.mk.injEq,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]

private theorem evaluation_diagonal (v : hexacode) :
    evaluation (action diagonal.val v) = ((evaluation v).1,localKappa (evaluation v).2) := by
  change ((Monomial.act (hexLiftRaw 2 * hexLiftRaw 3) v.val) (hexPos 0),
    (Monomial.act (hexLiftRaw 2 * hexLiftRaw 3) v.val) (hexPos 1)) = _
  have hh : ∀ r s : K, (localU (localU r),localU (localW s)) = (r,localKappa s) := by decide
  exact hh _ _

private theorem evaluation_exchange (v : hexacode) :
    evaluation (action exchange.val v) =
      (localU (evaluation v).2,localU (evaluation v).1) := rfl

private theorem evaluation_scalar (v : hexacode) :
    evaluation (action hexZ v) =
      (localKappa (evaluation v).1,localKappa⁻¹ (evaluation v).2) := rfl

private theorem diagonal_stabilizes : diagonal.val ∈ subspaceStabilizer action (zeroPairPlane firstPair) :=
  (zeroPairPlane_stabilizer_iff _ _).mpr (by decide +kernel)

private theorem exchange_stabilizes : exchange.val ∈ subspaceStabilizer action (zeroPairPlane firstPair) :=
  (zeroPairPlane_stabilizer_iff _ _).mpr (by decide +kernel)

private theorem scalar_stabilizes : hexZ ∈ subspaceStabilizer action (zeroPairPlane firstPair) :=
  (zeroPairPlane_stabilizer_iff _ _).mpr (by decide +kernel)

private theorem letter_orbit (r u : K) (hr : r ≠ 0) :
    u = 0 ∨ u = r ∨ u = localKappa r ∨ u = localKappa (localKappa r) := by
  revert r u
  decide +kernel

private theorem letter_interval (B : Submodule Bit (K × K))
    (hd : ∀ v ∈ B, (v.1,localKappa v.2) ∈ B)
    (he : ∀ v ∈ B, (localU v.2,localU v.1) ∈ B)
    (hz : ∀ v ∈ B, (localKappa v.1,localKappa⁻¹ v.2) ∈ B) : B = ⊥ ∨ B = ⊤ := by
  by_cases hb : B = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hs : (0,v.2) ∈ B := by
    have hsum := B.add_mem (hd v hv) (hd _ (hd v hv))
    have hcalc : ∀ r s : K,
        (r,localKappa s) + (r,localKappa (localKappa s)) = (0,s) := by decide
    exact hcalc _ _ ▸ hsum
  have hr : (v.1,0) ∈ B := by
    have hsum := B.add_mem hv hs
    have hcalc : ∀ r s : K, (r,s) + (0,s) = (r,0) := by decide
    exact hcalc _ _ ▸ hsum
  have hseed : ∃ r : K, r ≠ 0 ∧ (r,0) ∈ B := by
    by_cases h1 : v.1 = 0
    · have h2 : v.2 ≠ 0 := fun he => hv0 (Prod.ext h1 he)
      refine ⟨localU v.2,fun hh => h2 (localU.map_eq_zero_iff.mp hh),?_⟩
      simpa only [map_zero] using he (0,v.2) hs
    · exact ⟨v.1,h1,hr⟩
  obtain ⟨r,hr0,hrB⟩ := hseed
  have ha (u : K) : (u,0) ∈ B := by
    rcases letter_orbit r u hr0 with rfl | rfl | rfl | rfl
    · exact B.zero_mem
    · exact hrB
    · simpa only [map_zero] using hz (r,0) hrB
    · have hh : (localKappa r,0) ∈ B := by simpa only [map_zero] using hz (r,0) hrB
      simpa only [map_zero] using hz (localKappa r,0) hh
  have hb (u : K) : (0,u) ∈ B := by
    have hh := he (localU.symm u,0) (ha (localU.symm u))
    simpa only [map_zero,LinearEquiv.apply_symm_apply] using hh
  apply top_unique
  intro v _
  have heq : (v.1,0) + (0,v.2) = v := by ext <;> simp
  exact heq ▸ B.add_mem (ha v.1) (hb v.2)

private theorem firstPair_interval (A : Submodule Bit hexacode)
    (hPA : zeroPairPlane firstPair ≤ A)
    (hA : ∀ g : HexEvenAutomorphisms,
      g.val ∈ subspaceStabilizer action (zeroPairPlane firstPair) →
      g.val ∈ subspaceStabilizer action A) : A = zeroPairPlane firstPair ∨ A = ⊤ := by
  let B := A.map evaluation
  have hd : ∀ v ∈ B, (v.1,localKappa v.2) ∈ B := by
    rintro v ⟨w,hw,rfl⟩
    exact ⟨action diagonal.val w,(hA diagonal diagonal_stabilizes w).mpr hw,evaluation_diagonal w⟩
  have he : ∀ v ∈ B, (localU v.2,localU v.1) ∈ B := by
    rintro v ⟨w,hw,rfl⟩
    exact ⟨action exchange.val w,(hA exchange exchange_stabilizes w).mpr hw,evaluation_exchange w⟩
  have hz : ∀ v ∈ B, (localKappa v.1,localKappa⁻¹ v.2) ∈ B := by
    rintro v ⟨w,hw,rfl⟩
    exact ⟨action hexZ w,(hA hexEvenZ scalar_stabilizes w).mpr hw,evaluation_scalar w⟩
  have hk : evaluation.ker ≤ A := evaluation_kernel ▸ hPA
  rcases letter_interval B hd he hz with hb | hb
  · left
    have hh := congrArg (Submodule.comap evaluation) hb
    rw [Submodule.comap_map_eq_self hk] at hh
    exact hh.trans evaluation_kernel
  · right
    have hh := congrArg (Submodule.comap evaluation) hb
    rw [Submodule.comap_map_eq_self hk,Submodule.comap_top] at hh
    exact hh

/-- The literal quotient by a double-zero field point is binary irreducible
under its actual even setwise stabilizer. -/
theorem zeroPairPlane_invariant_interval (s : Pair) (A : Submodule Bit hexacode)
    (hPA : zeroPairPlane s ≤ A)
    (hA : ∀ g : HexEvenAutomorphisms,
      g.val ∈ subspaceStabilizer action (zeroPairPlane s) →
      g.val ∈ subspaceStabilizer action A) :
    A = zeroPairPlane s ∨ A = ⊤ := by
  obtain ⟨p,hp⟩ := exists_even_pair_transport s firstPair
  obtain ⟨g,hg⟩ := hexEvenCoordinate_surjective p
  have hgP : (zeroPairPlane s).map (action g.val) = zeroPairPlane firstPair := by
    rw [zeroPairPlane_map]
    have hh : hexCoordinateSixHom g.val = p.val := congrArg Subtype.val hg
    rw [hh,hp]
  let e := hexAction g.val
  let B := A.map e.toLinearMap
  have hPB : zeroPairPlane firstPair ≤ B := by
    rw [←hgP]
    exact Submodule.map_mono hPA
  have hint (x : HexEvenAutomorphisms) (hx : x.val ∈ subspaceStabilizer action (zeroPairPlane firstPair)) :
      x.val ∈ subspaceStabilizer action B := by
    let y := g⁻¹*x*g
    have hc := mem_subspaceStabilizer_equivariant action action
      (MulAut.conj g.val) e (fun k v => by
        change action g.val (action k v) = action (g.val*k*g.val⁻¹) (action g.val v)
        rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
        congr 2
        group)
    have hy : y.val ∈ subspaceStabilizer action (zeroPairPlane s) := by
      apply (hc (zeroPairPlane s) y.val).mpr
      have hxy : MulAut.conj g.val y.val = x.val := by
        change g.val*(g⁻¹*x*g).val*g.val⁻¹=x.val
        simp only [Subgroup.coe_mul,Subgroup.coe_inv]
        group
      rw [hxy]
      change x.val ∈ subspaceStabilizer action ((zeroPairPlane s).map (action g.val))
      rw [hgP]
      exact hx
    have ha := (hc A y.val).mp (hA y hy)
    have hxy : MulAut.conj g.val y.val = x.val := by
      change g.val*(g⁻¹*x*g).val*g.val⁻¹=x.val
      simp only [Subgroup.coe_mul,Subgroup.coe_inv]
      group
    rw [hxy] at ha
    exact ha
  rcases firstPair_interval B hPB hint with hb | hb
  · left
    apply (Submodule.map_injective_of_injective e.injective)
    exact hb.trans hgP.symm
  · right
    apply (Submodule.map_injective_of_injective e.injective)
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr e.surjective]
    exact hb

end Representation.Hexacode
