module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.Coordinates

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.Setup

/-!
# Transporting abelian outer-actor coordinates to the source configuration

Normalize an actual outer involution through the checked odd-prime PSU3
normalization theorem. The entire ambient action image retains its two-group
and commutativity properties and contains both the normalized outer action
and conjugation by the marked inner involution. A single intrinsic matrix
calculation then transports back to the literal `HasInvertedCoordinates`.

The second theorem applies this reduction to a conjugate of the whole
original elementary actor. Normality preserves outerness, and elementary
commutativity puts both marked involutions in its full Sylow centralizer.
The abelian reselection and intrinsic matrix calculation remain explicit
premises. Their separate producers must discharge them before the requested
unconditional placement, or E.1.14(7), can be claimed.

Source: Aschbacher--Smith E.1.1--2, E.1.5 and E.1.14(7), printed
pp.209--210,214, and the cited Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open InnerGeometry.SemidihedralTorus

variable {G : Type*} [Group G]

/-- Normalize the original outer involution, apply the intrinsic abelian
calculation once to the full action image, and transport its coordinate formulas. -/
theorem hasInvertedCoordinates_of_abelian_action
    (L R : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (hfaithful : centralizer (L : Set G) = ⊥)
    (hR : IsPGroup 2 R) [IsMulCommutative R]
    (t : G) (htR : t ∈ R) (htL : t ∉ L) (ht2 : t ^ 2 = 1)
    (z : L) (hzR : (z : G) ∈ R) (hz : orderOf z = 2)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU L 3 p)
    (hgeometry : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
      Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      J.form = !![0,0,1;0,1,0;1,0,0] → AbelianOuterCoordinateGeometry J) :
    HasInvertedCoordinates L R z p := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e₀⟩⟩ := hmodel
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e₀.symm.isSimpleGroup
  let a : MulAut L := MulAut.conjNormal t
  have ha2 : a ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hao : ¬ ∃ x : L, a = MulAut.conj x := by
    rintro ⟨x, hx⟩
    have he : t = (x : G) := MulAut.conjNormal_injective_of_centralizer_eq_bot L hfaithful
      (hx.trans MulAut.conjNormal_val.symm)
    exact htL (he ▸ x.property)
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hc))
  obtain ⟨J₀, d, hconj, hform, hentry⟩ :=
    HermitianForm.OddInvolutionNormalization.normalized_outer J hp ho hcard hfixed
      (MulAut.congr e₀ a) (by rw [← map_pow, ha2, map_one])
      (fun h => hao ((MulAut.congr_inner_iff e₀ a).mp h))
  let e := e₀.trans d
  let f : G →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut L)
  let U := R.map f
  have hU : IsPGroup 2 U := hR.map f
  have hcU : IsMulCommutative U := inferInstance
  have hγ : J₀.IsEntrywiseConjugation (f t) := hentry
  have hzU : MulAut.conj (e z) ∈ U := by
    have he : f (z : G) = MulAut.conj (e z) := by
      change MulAut.congr e (MulAut.conjNormal (z : G)) = _
      rw [MulAut.conjNormal_val, MulAut.congr_conj]
    rw [← he]
    exact mem_map_of_mem f hzR
  have hcz : ∀ x, J₀.conj x = x ^ p := by rw [hconj]; exact hc
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e.symm.isSimpleGroup
  obtain ⟨J', hconj', hroot | hrot⟩ :=
    hgeometry F J₀ inferInstance hcard hcz hform U hU hcU (f t) hγ
      (mem_map_of_mem f htR) (e z) ((e.orderOf_eq z).trans hz) hzU
  · obtain ⟨hJ', h2, b, hbz, hb⟩ := hroot
    refine ⟨F, inferInstance, inferInstance, J', hcard, ?_, Or.inl ?_⟩
    · rw [hconj']; exact hcz
    · refine ⟨hJ', h2, e.trans b, hbz, ?_⟩
      intro s hs
      obtain ⟨c, hc⟩ := hb (f s) (mem_map_of_mem f hs)
      exact ⟨c, hc⟩
  · obtain ⟨hJ', h2, b, hbz, hb⟩ := hrot
    refine ⟨F, inferInstance, inferInstance, J', hcard, ?_, Or.inr ?_⟩
    · rw [hconj']; exact hcz
    · refine ⟨hJ', h2, e.trans b, hbz, ?_⟩
      intro s hs
      obtain ⟨ε, hε⟩ := hb (f s) (mem_map_of_mem f hs)
      exact ⟨ε, hε⟩

variable [Finite G]

/-- Application to a conjugate of the whole original actor. Only abelian
reselection and the intrinsic coordinate calculation remain explicit. -/
theorem exists_positioned_inverted_coordinates_of_abelian_reselection
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hout : ¬ A ≤ generalizedFitting G)
    {z : G} (hzL : z ∈ generalizedFitting G) (hz : orderOf z = 2)
    (hselect : ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      IsMulCommutative ((T : Subgroup G) ⊓
        centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G))
    (hgeometry : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
      Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      J.form = !![0,0,1;0,1,0;1,0,0] → AbelianOuterCoordinateGeometry J) :
    ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      HasInvertedCoordinates (generalizedFitting G)
        ((T : Subgroup G) ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G))
        ⟨z, hzL⟩ p := by
  obtain ⟨g, hBT, hzB, hcomm⟩ := hselect
  let B := A.map (MulAut.conj g).toMonoidHom
  let R := (T : Subgroup G) ⊓ centralizer (B : Set G)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let : IsMulCommutative R := hcomm
  have hBR : B ≤ R := by
    intro b hb
    refine ⟨hBT hb, mem_centralizer_iff.mpr ?_⟩
    intro x hx
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : B) (⟨b, hb⟩ : B))
  have houtB : ¬ B ≤ generalizedFitting G := by
    intro h
    apply hout
    intro x hx
    have hconj := h (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
    have hback := (inferInstance : (generalizedFitting G).Normal).conj_mem
      (g * x * g⁻¹) hconj g⁻¹
    simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hback
  obtain ⟨t, htB, htL⟩ := SetLike.not_le_iff_exists.mp houtB
  refine ⟨g, hBT, hzB, hasInvertedCoordinates_of_abelian_action _ R
    (SimpleSocle.centralizer_eq_bot (nonabelian_of_model hp ho hmodel))
    (T.isPGroup'.to_le inf_le_left) t (hBR htB) htL
    (elemPow_eq_one_of_isElementaryAbelian t htB) ⟨z, hzL⟩ (hBR hzB) ?_ hp ho hmodel hgeometry⟩
  simpa only [orderOf_mk] using hz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
