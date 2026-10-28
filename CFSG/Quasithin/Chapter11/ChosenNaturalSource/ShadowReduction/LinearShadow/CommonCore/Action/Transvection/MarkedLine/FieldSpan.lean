module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.MarkedLine.Source
public import Theory.FieldTheory.MultiplicativeSpan
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The full additive span of the binary odd Cartan part

For odd field degree the unit group is prime to three. In even degree 2m,
put r=2^m. When m is even the three-residual contains a subgroup of order
r+1; when m is odd it contains one of order r-1 and the cubic omega factor
supplies a further factor three. Thus the Cartan part has at least r elements.
The additive-span subfield argument forces its span to be the whole field.
This retains the necessary cubic factor also at q=4 and q=64.

The final theorem discharges this input in the original doubled-line consumer.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource

private theorem exists_unit_order (F : BinaryField) {d : ℕ}
    (hd : d ∣ Nat.card F.Carrier - 1) : ∃ x : F.Carrierˣ, orderOf x = d := by
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F.Carrierˣ)
  refine ⟨x ^ (orderOf x / d), orderOf_pow_orderOf_div ?_ ?_⟩
  · rw [hx]; exact Nat.card_pos.ne'
  · simpa only [hx,Nat.card_units] using hd

private theorem coprime_dvd_card_torus (F : BinaryField) {d : ℕ}
    (hd : d ∣ Nat.card F.Carrier - 1) (hc : Nat.Coprime 3 d) :
    d ∣ Nat.card (torusCartanPart F) := by
  obtain ⟨x,hx⟩ := exists_unit_order F hd
  have hmem : x ∈ torusCartanPart F :=
    (show pResidual 3 F.Carrierˣ ≤ torusCartanPart F from le_sup_left) (mem_pResidual_of_orderOf_coprime (hx.symm ▸ hc))
  have h := orderOf_dvd_natCard (⟨x,hmem⟩ : torusCartanPart F)
  simpa only [← Subgroup.orderOf_coe,hx] using h

private theorem three_dvd_card_torus (F : BinaryField)
    (hd : 3 ∣ Nat.card F.Carrier - 1) : 3 ∣ Nat.card (torusCartanPart F) := by
  obtain ⟨x,hx⟩ := exists_unit_order F hd
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hx,pow_one])
  have hcore : x ∈ pCore 3 F.Carrierˣ :=
    (le_sSup (show zpowers x ∈ {K : Subgroup F.Carrierˣ | K.Normal ∧ IsPGroup 3 K}
      from ⟨inferInstance,hp⟩)) (mem_zpowers x)
  have homega : (⟨x,hcore⟩ : pCore 3 F.Carrierˣ) ∈ omega₁ (pCore 3 F.Carrierˣ) (p := 3) := by
    apply Subgroup.subset_closure
    change (⟨x,hcore⟩ : pCore 3 F.Carrierˣ) ^ (3 ^ 1) = 1
    apply Subtype.ext
    simpa only [pow_one,Subgroup.coe_pow,Subgroup.coe_one,← hx] using pow_orderOf_eq_one x
  have hmem : x ∈ torusCartanPart F := (show (omega₁ (pCore 3 F.Carrierˣ) (p := 3)).map (pCore 3 F.Carrierˣ).subtype ≤ torusCartanPart F from le_sup_right) (mem_map_of_mem _ homega)
  have h := orderOf_dvd_natCard (⟨x,hmem⟩ : torusCartanPart F)
  simpa only [← Subgroup.orderOf_coe,hx] using h

private theorem square_torus_card_lower (F : BinaryField) {m : ℕ}
    (hm : 0 < m) (hcard : Nat.card F.Carrier = (2 ^ m) ^ 2) :
    2 ^ m ≤ Nat.card (torusCartanPart F) := by
  let r := 2 ^ m
  have hr : 2 ≤ r := by
    exact Nat.le_pow hm
  have hfactor : Nat.card F.Carrier - 1 = (r - 1) * (r + 1) := by
    rw [hcard]
    dsimp [r]
    have h := Nat.sq_sub_sq (2 ^ m) 1
    simpa only [one_pow,mul_comm] using h
  have hmod := Nat.BinaryTorusParity.two_pow_mod_three m
  by_cases he : m % 2 = 0
  · have hc : Nat.Coprime 3 (r+1) := Nat.prime_three.coprime_iff_not_dvd.mpr (by
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      simp only [he,if_true] at hmod
      dsimp [r] at hz
      omega)
    have hd := coprime_dvd_card_torus F (d := r+1) (by rw [hfactor]; exact dvd_mul_left _ _) hc
    exact (by omega : r ≤ r+1).trans (Nat.le_of_dvd Nat.card_pos hd)
  · have hc : Nat.Coprime 3 (r-1) := Nat.prime_three.coprime_iff_not_dvd.mpr (by
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      simp only [he,if_false] at hmod
      dsimp [r] at hz
      have := pow_pos (by decide : 0 < (2 : ℕ)) m
      omega)
    have hd := coprime_dvd_card_torus F (d := r-1) (by rw [hfactor]; exact dvd_mul_right _ _) hc
    have h3 : 3 ∣ Nat.card F.Carrier - 1 := by
      rw [hfactor]
      apply dvd_mul_of_dvd_right
      apply Nat.dvd_of_mod_eq_zero
      simp only [he,if_false] at hmod
      dsimp [r]
      omega
    have hmul := hc.mul_dvd_of_dvd_of_dvd (three_dvd_card_torus F h3) hd
    have hle := Nat.le_of_dvd Nat.card_pos hmul
    omega

/-- The three-residual together with the cubic omega factor spans the binary field. -/
theorem torusScalarSet_additive_closure (F : BinaryField) :
    AddSubgroup.closure (torusScalarSet F) = ⊤ := by
  rcases Nat.even_or_odd F.degree with he | ho
  · obtain ⟨m,hm⟩ := he
    have hmpos : 0 < m := by have := F.degree_pos; omega
    have hcard : Nat.card F.Carrier = (2 ^ m) ^ 2 := by
      rw [F.card_eq,hm,← two_mul m,mul_comm 2 m,pow_mul]
    exact FiniteField.MultiplicativeSpan.additive_span_eq_top_of_large_units
      (torusCartanPart F) hcard (square_torus_card_lower F hmpos hcard)
  · have hcop : Nat.Coprime 3 (Nat.card F.Carrierˣ) := by
      rw [Nat.card_units,F.card_eq]
      exact Nat.BinaryTorusParity.coprime_three_sub_one ho
    apply top_unique
    intro x _
    by_cases hx : x = 0
    · simpa only [hx] using (AddSubgroup.closure (torusScalarSet F)).zero_mem
    · apply AddSubgroup.subset_closure
      let u := Units.mk0 x hx
      have hu : u ∈ torusCartanPart F :=
        (show pResidual 3 F.Carrierˣ ≤ torusCartanPart F from le_sup_left) (mem_pResidual_of_orderOf_coprime (hcop.of_dvd_right (orderOf_dvd_natCard u)))
      exact ⟨⟨u,hu⟩,rfl⟩

open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The finite-field span is discharged in the original doubled-line consumer.
The spectrum of the actual Hall action remains explicit. -/
theorem source_doubled_marked_line_of_hall_spectrum
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hSL : ∃ e, c = Coordinates.sl3 e)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (s : Hypothesis1131At D S U₁ H) (hcounter : ¬ Proposition1132At D S U₁ H)
    (g : G) (cK : NaturalQuotientMarking T H S.field) (hm : cK.multiplicity = 2)
    (hfixedL : V ⊓ centralizer (L : Set G) = ⊥)
    (hfixedK : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))]
    (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (P : Sylow 2 (residualStar T H))
    (hP : (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H))
    (D_H X : Subgroup G)
    (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hDKL : oddCartanPart D_H ≤ outsideResidual H ⊓ L)
    (hX : IsCartan T L X) (hDX : oddCartanPart D_H ≤ X)
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcomm : D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆)
    (hspectrum : ∀ b : SL(2,S.field.Carrier),
      (∀ k : outsideResidual H, (k : G) ∈ oddCartanPart D_H →
        (b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val 1 0 = 0) →
      torusScalarSet S.field ⊆ cartanScalarSet cK b (oddCartanPart D_H)) :
    ∃ (b : SL(2,S.field.Carrier))
      (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 2)
      (E : Submodule S.field.Carrier (Fin 2 → Fin 2 → S.field.Carrier)),
      Module.finrank S.field.Carrier E = 1 ∧ E ≤ n.fixedSpace ∧
      n.liftSpace E = D.centralQuotientPreimage U₁ ∧
      (∀ (k : outsideResidual H) (v : omegaClosure T H) (i : Fin 2),
        (n.coordinates (residualAction T H k v)).toAdd i =
          (b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val *ᵥ
            (n.coordinates v).toAdd i) ∧
      ∃ u : omegaClosure T H,
        (u : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
        ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (u : G)⁆ = D.centralQuotientPreimage U₁ := by
  exact source_doubled_marked_line_of_torus_spectrum c f hSL hline s hcounter
    g cK hm hfixedL hfixedK hAH P hP D_H X hDH hHall hDKL hX hDX hcontain hcomm
    (torusScalarSet_additive_closure S.field) hspectrum

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
