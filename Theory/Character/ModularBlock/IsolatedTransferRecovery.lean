module
public import Theory.Character.ModularBlock.RelativeTransferRemainder
public import Mathlib.Algebra.CharP.Algebra

/-!
# Relative-transfer recovery at an isolated involution

In characteristic two, restriction to an isolated involution's centralizer
is a left inverse to relative transfer on central elements. Here isolation
is stated in representative form: if conjugation carries the involution
into its centralizer, then the conjugator belongs to that centralizer.

Left multiplication by the involution acts on the centralizer cosets.
Representative isolation makes the identity coset its only fixed point.
Conjugation by the involution leaves every centralizer-restricted coefficient
unchanged, so the nonidentity cosets pair into equal summands. Characteristic
two cancels each pair, leaving only the original embedded local element.
The final elementary lemma derives representative isolation from the usual
commuting-conjugates condition.

Ported from the exact-recovery section of
`Submission/ZStar/RelativeTransferBrauer.lean` at revision `c3503435`
of `public/lean-eval/glauberman_zStar`. No block-correspondence or
principal-primitivity hypothesis is used in this group-algebra identity.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.RelativeTransferBrauer
universe u v
attribute [local instance] Fintype.ofFinite

/-- Conjugating a subgroup-algebra element by `z * g` or by `g` has the same
restriction to `C_G(z)`. -/
lemma centralizerRestriction_conjugationMap_z_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z g : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    BrauerMap.centralizerRestriction R z
        (conjugationMap R (Subgroup.centralizer ({z} : Set G)) (z * g) b) =
      BrauerMap.centralizerRestriction R z
        (conjugationMap R (Subgroup.centralizer ({z} : Set G)) g b) := by
  rw [conjugationMap_apply, conjugationMap_apply]
  simp only [map_mul, mul_inv_rev]
  let a := MonoidAlgebra.of R G g *
    subgroupSubtypeMap R (Subgroup.centralizer ({z} : Set G)) b *
      MonoidAlgebra.of R G g⁻¹
  suffices hmain : BrauerMap.centralizerRestriction R z
      (MonoidAlgebra.of R G z * a * MonoidAlgebra.of R G z⁻¹) =
        BrauerMap.centralizerRestriction R z a by
    simpa only [a, mul_assoc] using hmain
  ext h
  have hh : (h : G) * z = z * (h : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp h.property
  change
    (MonoidAlgebra.of R G z * a * MonoidAlgebra.of R G z⁻¹).coeff (h : G) =
      a.coeff (h : G)
  rw [show MonoidAlgebra.of R G z⁻¹ =
      MonoidAlgebra.single z⁻¹ 1 by rfl,
    MonoidAlgebra.coeff_mul_single_apply,
    show MonoidAlgebra.of R G z = MonoidAlgebra.single z 1 by rfl,
    MonoidAlgebra.coeff_single_mul_apply]
  simp only [one_mul, mul_one]
  congr 1
  calc
    z⁻¹ * ((h : G) * (z⁻¹)⁻¹) = z⁻¹ * ((h : G) * z) := by simp
    _ = z⁻¹ * (z * (h : G)) := by rw [hh]
    _ = (h : G) := by simp

/-- Under the representative form of isolation, the only right centralizer
coset fixed by left multiplication by `z` is the identity coset. -/
lemma fixedCoset_eq_one_of_isolated
    {G : Type u} [Group G]
    (z : G) (hz : z * z = 1)
    (hiso : ∀ g : G,
      g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
        g ∈ Subgroup.centralizer ({z} : Set G))
    (q : G ⧸ Subgroup.centralizer ({z} : Set G))
    (hq : z • q = q) :
    q = (1 : G) := by
  let H := Subgroup.centralizer ({z} : Set G)
  have hmk : (z * q.out : G ⧸ H) = (q.out : G ⧸ H) := by
    calc
      (z * q.out : G ⧸ H) = z • q := by
        simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out H z q)
      _ = q := hq
      _ = (q.out : G ⧸ H) := (QuotientGroup.out_eq' q).symm
  have hmem : q.out⁻¹ * z * q.out ∈ H := by
    have hrel := QuotientGroup.eq.mp hmk
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    simpa [hzinv, mul_assoc] using hrel
  have hout : q.out ∈ H := hiso q.out hmem
  rw [← QuotientGroup.out_eq' q]
  apply (QuotientGroup.eq).2
  simpa using H.inv_mem hout

/-- For an isolated involution in characteristic two, restriction to its
centralizer is a left inverse to relative transfer on central elements. -/
theorem centralizerRestriction_relativeTransfer_eq_self_of_isolated
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hb : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))))
    (hiso : ∀ g : G,
      g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
        g ∈ Subgroup.centralizer ({z} : Set G)) :
    BrauerMap.centralizerRestriction R z
        (relativeTransfer R (Subgroup.centralizer ({z} : Set G)) b) = b := by
  classical
  let H := Subgroup.centralizer ({z} : Set G)
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let : CharP (MonoidAlgebra R H) 2 := charP_of_injective_algebraMap' R 2
  let q0 : G ⧸ H := (1 : G)
  have hzH : z ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hzq0 : z • q0 = q0 := by
    change (z * (1 : G) : G ⧸ H) = (1 : G)
    apply (QuotientGroup.eq).2
    simpa using hzH
  have hterm (q : G ⧸ H) :
      BrauerMap.centralizerRestriction R z
          (conjugationMap R H (z • q).out b) =
        BrauerMap.centralizerRestriction R z
          (conjugationMap R H q.out b) := by
    have hout : conjugationMap R H (z • q).out b =
        conjugationMap R H (z * q.out) b := by
      apply conjugationMap_out_eq_of_mk_eq H (z • q) (z * q.out)
      · simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out H z q)
      · exact hb
    rw [hout]
    exact centralizerRestriction_conjugationMap_z_mul z q.out b
  have hrem :
      BrauerMap.centralizerRestriction R z
          (relativeTransferRemainder R H b) = 0 := by
    rw [relativeTransferRemainder, map_sum]
    let s : Finset (G ⧸ H) := Finset.univ.erase q0
    have hsum : (∑ q ∈ s,
        BrauerMap.centralizerRestriction R z
          (conjugationMap R H q.out b)) = 0 := by
      refine Finset.sum_involution
        (g := fun q _hq => z • q)
        (hg₁ := ?_) (hg₃ := ?_) (g_mem := ?_) (hg₄ := ?_)
      · intro q hq
        rw [hterm]
        exact CharTwo.add_self_eq_zero _
      · intro q hq _hne hfix
        have hq0 : q = q0 := by
          exact fixedCoset_eq_one_of_isolated z hz (by simpa [H] using hiso)
            q hfix
        exact (Finset.mem_erase.mp hq).1 hq0
      · intro q hq
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro hq0
        have hrecover : q = z • (z • q) := by
          rw [← mul_smul, hz, one_smul]
        have hneq : q ≠ q0 := (Finset.mem_erase.mp hq).1
        apply hneq
        calc
          q = z • (z • q) := hrecover
          _ = z • q0 := by rw [hq0]
          _ = q0 := hzq0
      · intro q hq
        rw [← mul_smul, hz, one_smul]
    simpa only [s, q0] using hsum
  rw [centralizerRestriction_relativeTransfer_eq_add_remainder z b hb]
  change b + BrauerMap.centralizerRestriction R z
      (relativeTransferRemainder R H b) = b
  rw [hrem, add_zero]

/-- Glauberman's usual isolation condition implies the representative form
used by the transfer pairing. -/
theorem representativeIsolation_of_isolated
    {G : Type v} [Group G] (z : G)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z) :
    ∀ g : G, g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
      g ∈ Subgroup.centralizer ({z} : Set G) := by
  intro g hg
  have hcomm :
      (g⁻¹ * z * (g⁻¹)⁻¹) * z = z * (g⁻¹ * z * (g⁻¹)⁻¹) := by
    simpa using (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have heq : g⁻¹ * z * g = z := by
    simpa using hisolated g⁻¹ hcomm
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (fun x : G => g * x) heq
  simpa [mul_assoc] using h.symm

end ModularBlock.RelativeTransferBrauer

