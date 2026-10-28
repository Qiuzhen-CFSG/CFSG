module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.Control
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.MatrixTorus

/-!
# From the controlled torus to the original four-group commutator

Choose an odd prime-order unit and map its cyclic subgroup through the
concrete torus and the original inner coordinate conjugator. Diagonal
control makes the full C_T(A) normalize this actual image. The distinguished
involution inverts its generator, so its commutator is the generator's
square. Odd order recovers the generator itself inside [X,A]. Its explicit
SL₃ matrix has the required nonzero off-block entry.

Simultaneous four-group coordinates and the diagonal two-subgroup
centralizer calculation remain explicit independent inputs. This proves
the construction from those inputs, not their existence or the unconditional
source theorem. Source: Aschbacher--Smith E.1.2, E.1.5 and E.1.14(7),
printed pp.209--210,214; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus
variable (F : Type*) [Field F] [Finite F]

private theorem odd_inverted_mem_commutator {G : Type*} [Group G]
    (X A : Subgroup G) (z x : G) (hz : z ∈ A) (hx : x ∈ X)
    {r : ℕ} (hr : Odd r) (hpow : x ^ r = 1)
    (hinv : z * x * z⁻¹ = x⁻¹) : x ∈ ⁅X, A⁆ := by
  have hsq : x ^ 2 ∈ ⁅X, A⁆ := by
    have he : ⁅x,z⁆ = x ^ 2 := by
      calc
        ⁅x,z⁆ = x * (z*x*z⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
        _ = x ^ 2 := by rw [hinv, inv_inv, pow_two]
    rw [← he]
    exact commutator_mem_commutator hx hz
  obtain ⟨n, hn⟩ := exists_pow_eq_pow_two_mul hpow hr 1
  rw [pow_one, pow_mul] at hn
  rw [hn]
  exact pow_mem hsq n

/-- The matrix and arithmetic construction consumes simultaneous coordinates
and the independent diagonal centralizer calculation. It normalizes the
cyclic odd subgroup by the full original `C_T(A)`. -/
theorem fourGroupOddMixing_of_inputs {p : ℕ}
    (hp : p.Prime) (hbig : 3 < p) (hF : Nat.card F = p) (hp4 : p % 4 = 3)
    (hcoords : FourGroupCoordinates F) (hcontrol : DiagonalTwoControl F) :
    FourGroupOddMixing F := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    let := Fintype.ofFinite F
    let : Fact p.Prime := ⟨hp⟩
    let : CharP F p := charP_of_card_eq_prime
      (by simpa only [← Nat.card_eq_fintype_card] using hF)
    intro he
    have hd := (CharP.cast_eq_zero_iff F p 2).mp he
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  intro T A hAe hAc _hAT hAI z hz hzA _hTz
  obtain ⟨s, hs, hAs⟩ := hcoords A hAe hAc hAI z hz hzA
  let e := MulAut.conj (innerSL F s)
  let D : Subgroup (graphExtension F) :=
    (T : Subgroup (graphExtension F)) ⊓ centralizer (A : Set (graphExtension F))
  let D0 := D.map e.symm.toMonoidHom
  have hA0 : A.map e.symm.toMonoidHom = coordinateFour F := by
    have heq : MulAut.conj ((innerSL F s)⁻¹) = e.symm := by
      ext a
      simp only [MulAut.conj_apply, inv_inv, e, MulAut.conj_symm_apply]
    rwa [heq] at hAs
  have hD0 : IsPGroup 2 D0 := (T.isPGroup'.to_inf_left).map e.symm.toMonoidHom
  have hD0C : D0 ≤ centralizer (coordinateFour F : Set (graphExtension F)) := by
    rintro g ⟨v, hv, rfl⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    rw [← hA0] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    change e.symm b * e.symm v = e.symm v * e.symm b
    simpa only [map_mul] using
      congrArg e.symm (mem_centralizer_iff.mp hv.2 b hb)
  obtain ⟨k, hk⟩ := controlled_planeTorus F hF hp4 h2 D0 (hcontrol D0 hD0 hD0C)
  obtain ⟨r, hr, hor, u, hu⟩ := exists_odd_prime_unit F hbig hF hp4
  have hu2 : u ^ 2 ≠ 1 := by
    intro he
    have hd : r ∣ 2 := hu ▸ orderOf_dvd_of_pow_eq_one he
    have hr2 : r ≠ 2 := by rintro rfl; norm_num at hor
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim hr.ne_one hr2
  let f : Fˣ →* graphExtension F :=
    e.toMonoidHom.comp ((innerSL F).comp (planeTorus F h2 k))
  let y := f u
  let X := (zpowers u).map f
  have hXeq : X = zpowers y := MonoidHom.map_zpowers f u
  have hXp : IsPGroup r X := by
    apply IsPGroup.map
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hu, pow_one]
  have hyX : y ∈ X := mem_map_of_mem f (mem_zpowers u)
  have hypow : y ^ r = 1 := by
    change f u ^ r = 1
    rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  have hbase : standardInner F * innerSL F (planeTorus F h2 k u) * (standardInner F)⁻¹ =
      (innerSL F (planeTorus F h2 k u))⁻¹ := by
    simpa only [standardInner, map_mul, map_inv] using
      congrArg (innerSL F) (planeTorus_standard F h2 k u)
  have hyinv : z * y * z⁻¹ = y⁻¹ := by
    have hez : e (standardInner F) = z := hs
    simpa [y, f, hez] using congrArg e hbase
  have hnorm : D ≤ normalizer (X : Set (graphExtension F)) := by
    intro g hg
    have hg0 : e.symm g ∈ D0 := mem_map_of_mem e.symm.toMonoidHom hg
    have hgy : g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹ := by
      rcases hk u (e.symm g) hg0 with he | he
      · exact Or.inl (by simpa [y, f] using congrArg e he)
      · exact Or.inr (by simpa [y, f] using congrArg e he)
    rw [hXeq, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (g * y * g⁻¹) = zpowers y
    rcases hgy with he | he
    · rw [he]
    · rw [he, zpowers_inv]
  refine ⟨r, hr, hor, X, hXp, hnorm, s, hs, planeTorus F h2 k u,
    planeTorus_mixes F h2 k u hu2, ?_⟩
  exact odd_inverted_mem_commutator X A z y hzA hyX hor hypow hyinv

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus
