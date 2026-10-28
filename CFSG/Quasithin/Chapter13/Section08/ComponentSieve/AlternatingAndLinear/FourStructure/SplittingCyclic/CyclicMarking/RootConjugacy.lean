module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.FlagTransport
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.SpecificGroups.BinaryLinear.SylowCenters

/-!
# Normalizing the cyclic actor to the marked Sylow center

For an incident line--plane--hyperplane flag in the actual four-dimensional
binary space, an order-two transvection subgroup in the plane radical is
conjugate to the ambient image of the intrinsic Sylow center. The conjugator
stabilizes the plane and hence preserves radical containment of larger actors.

The transvection's image line and fixed hyperplane form another full flag
through the same plane. Adapted bases align these two flags. The conjugated
transvection lies in both end-node radicals, which are centralized by the
middle parabolic; the Sylow-center order bound then gives subgroup equality.
The source-group transport retains the explicit adjusted left conjugator
`eH.symm k * g₀`. A natural fixed-codimension-one calculation supplies the
transvection hypothesis via rank-nullity.

This is the conditional intrinsic calculation for Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March 2004,
13.8.25, printed p.962 (PDF p.979). The source actor identification and marked
commutator-vector assembly remain with the parent CyclicMarking development.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootConjugacy
open Subgroup BinaryLinear BinaryLinear.MiddleParabolic BinaryLinear.OuterCyclic

private theorem flag_alignment (L P F J K : Submodule (ZMod 2) V)
    (hLP : L ≤ P) (hPF : P ≤ F) (hJP : J ≤ P) (hPK : P ≤ K)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (hJ : Module.finrank (ZMod 2) J = 1)
    (hK : Module.finrank (ZMod 2) K = 3) :
    ∃ k : BinaryLinear.GL V, k ∈ parabolic P ∧ J.map k.toLinearMap = L ∧ K.map k.toLinearMap = F := by
  obtain ⟨e, heL, heP, heF⟩ := exists_flag_equiv L P F hLP hPF hL hP hF
  obtain ⟨d, hdJ, hdP, hdK⟩ := exists_flag_equiv J P K hJP hPK hJ hP hK
  let k := e * d.symm
  have hc : k.toLinearMap.comp d.toLinearMap = e.toLinearMap := by
    ext v
    simp [k]
  have hkP : P.map k.toLinearMap = P := by
    nth_rw 1 [← hdP]
    rw [← Submodule.map_comp, hc, heP]
  refine ⟨k, ?_, ?_, ?_⟩
  · intro v
    nth_rw 1 [← hkP]
    rw [Submodule.mem_map_equiv]
    simp
  · rw [← hdJ, ← Submodule.map_comp, hc, heL]
  · rw [← hdK, ← Submodule.map_comp, hc, heF]

/-- A transvection in the plane radical can be moved into the intrinsic Borel
center by an element stabilizing the same plane. -/
theorem transvection_conjugate_mem_center
    (L P F : Submodule (ZMod 2) V)
    (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    {t : BinaryLinear.GL V} (htP : t ∈ radical P) (ht : IsTransvection t) :
    ∃ k : BinaryLinear.GL V, k ∈ parabolic P ∧
      MulAut.conj k t ∈ (center (borel L P F)).map (borel L P F).subtype := by
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := ht
  have hPK : P ≤ f.ker := by
    intro v hv
    have he := htP.1 v hv
    change v + f v • w = v at he
    exact (smul_eq_zero.mp (add_eq_left.mp he)).resolve_right hw
  obtain ⟨v, hv⟩ := LinearMap.surjective hf (1 : ZMod 2)
  have hwP : w ∈ P := by
    have hd := htP.2 v
    change v + f v • w - v ∈ P at hd
    simpa [hv] using hd
  let J := Submodule.span (ZMod 2) {w}
  have hJP : J ≤ P := Submodule.span_le.mpr (by simpa using hwP)
  have hJ : Module.finrank (ZMod 2) J = 1 := finrank_span_singleton hw
  have hK : Module.finrank (ZMod 2) f.ker = 3 := by
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    have hV : Module.finrank (ZMod 2) V = 4 := by simp [V]
    omega
  obtain ⟨k, hkP, hkJ, hkK⟩ := flag_alignment L P F J f.ker hLP hPF hJP hPK hL hP hF hJ hK
  have htJ : transvection w f hfw ∈ radical J :=
    transvection_mem (Submodule.mem_span_singleton_self w)
      (Submodule.span_le.mpr (by simpa using hfw))
  have htK : transvection w f hfw ∈ radical f.ker := transvection_mem hfw le_rfl
  have hzL : MulAut.conj k (transvection w f hfw) ∈ radical L := by
    rw [← hkJ, ← radical_map_conj]
    exact ⟨_, htJ, rfl⟩
  have hzF : MulAut.conj k (transvection w f hfw) ∈ radical F := by
    rw [← hkK, ← radical_map_conj]
    exact ⟨_, htK, rfl⟩
  have hRS : radical L ≤ borel L P F :=
    le_inf (le_inf (radical_le_parabolic L) (radical_le_nested_parabolic (hLP.trans hPF)))
      (radical_le_nested_parabolic hLP)
  refine ⟨k, hkP, ⟨⟨_, hRS hzL⟩, ?_, rfl⟩⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  have hc := mem_centralizer_iff.mp
    (middle_centralizes_radical_inf hL (by simpa [V] using hF) x.property.1)
    _ ⟨hzL, hzF⟩
  exact hc.symm

/-- Normalize an order-two transvection subgroup to the ambient image of the
intrinsic Sylow center. The same conjugator preserves containment of every
subgroup in the plane radical, in particular any larger source actor. -/
theorem order_two_transvection_conjugate_center
    (L P F : Submodule (ZMod 2) V)
    (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (S : Sylow 2 (BinaryLinear.GL V)) (hS : (S : Subgroup (BinaryLinear.GL V)) = borel L P F)
    (A : Subgroup (BinaryLinear.GL V)) (hA : Nat.card A = 2) (hAP : A ≤ radical P)
    (ht : ∃ t ∈ A, IsTransvection t) :
    ∃ k : BinaryLinear.GL V, k ∈ parabolic P ∧
      A.map (MulAut.conj k).toMonoidHom = (center S).map (S : Subgroup (BinaryLinear.GL V)).subtype ∧
      ∀ B : Subgroup (BinaryLinear.GL V), B ≤ radical P →
        B.map (MulAut.conj k).toMonoidHom ≤ radical P := by
  let : Finite (BinaryLinear.GL V) :=
    Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨t, htA, ht⟩ := ht
  obtain ⟨k, hk, hkt⟩ := transvection_conjugate_mem_center L P F hLP hPF hL hP hF (hAP htA) ht
  have hkt' : MulAut.conj k t ∈ (center S).map (S : Subgroup (BinaryLinear.GL V)).subtype := by
    rw [hS]
    exact hkt
  have hle : A.map (MulAut.conj k).toMonoidHom ≤
      (center S).map (S : Subgroup (BinaryLinear.GL V)).subtype := by
    obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
    rintro _ ⟨a, ha, rfl⟩
    by_cases ha1 : a = 1
    · simp [ha1]
    have hat : a = t := by
      have ha' : (⟨a, ha⟩ : A) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
      have ht' : (⟨t, htA⟩ : A) ≠ 1 := fun h => ht.ne_one (congrArg Subtype.val h)
      exact congrArg Subtype.val ((huniq _ ha').trans (huniq _ ht').symm)
    simpa [hat] using hkt'
  refine ⟨k, hk, Subgroup.eq_of_le_of_card_ge hle ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (K := A) (MulAut.conj k).injective, hA,
      Subgroup.card_map_of_injective (S : Subgroup (BinaryLinear.GL V)).subtype_injective]
    exact linear_sylow_center_card_le_two (by decide) S
  · intro B hB x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact (Subgroup.le_set_normalizer_iff.mp (parabolic_le_normalizer P) k hk) b (hB hb)

/-- Left conjugation by the adjusted source element corresponds to first conjugating
by `g₀`, then conjugating its linear image by `k`. -/
theorem map_conj_adjusted {H : Type*} [Group H]
    (eH : H ≃* BinaryLinear.GL V) (g₀ : H) (k : BinaryLinear.GL V) (A : Subgroup H) :
    (A.map (MulAut.conj (eH.symm k * g₀)).toMonoidHom).map eH.toMonoidHom =
      ((A.map (MulAut.conj g₀).toMonoidHom).map eH.toMonoidHom).map
        (MulAut.conj k).toMonoidHom := by
  simp only [Subgroup.map_map]
  apply congrArg (fun f : H →* BinaryLinear.GL V => A.map f)
  apply MonoidHom.ext
  intro a
  change eH ((eH.symm k * g₀) * a * (eH.symm k * g₀)⁻¹) =
    k * eH (g₀ * a * g₀⁻¹) * k⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, mul_inv_rev]
  group

/-- Normalize the order-two source actor while retaining both its larger actor and
its specified group coordinates. The new source conjugator is `eH.symm k * g₀`. -/
theorem exists_adjusted_conjugator {H : Type*} [Group H]
    (eH : H ≃* BinaryLinear.GL V) (g₀ : H)
    (L P F : Submodule (ZMod 2) V)
    (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (S : Sylow 2 (BinaryLinear.GL V))
    (hS : (S : Subgroup (BinaryLinear.GL V)) = borel L P F)
    (A B : Subgroup H) (hAB : A ≤ B) (hA : Nat.card A = 2)
    (hBP : (B.map (MulAut.conj g₀).toMonoidHom).map eH.toMonoidHom ≤ radical P)
    (ht : ∃ a ∈ A, IsTransvection (eH (MulAut.conj g₀ a))) :
    ∃ k : BinaryLinear.GL V, k ∈ parabolic P ∧
      (A.map (MulAut.conj (eH.symm k * g₀)).toMonoidHom).map eH.toMonoidHom =
        (center S).map (S : Subgroup (BinaryLinear.GL V)).subtype ∧
      (B.map (MulAut.conj (eH.symm k * g₀)).toMonoidHom).map eH.toMonoidHom ≤ radical P := by
  let A₀ := (A.map (MulAut.conj g₀).toMonoidHom).map eH.toMonoidHom
  have hA₀ : Nat.card A₀ = 2 := by
    dsimp [A₀]
    rw [Subgroup.card_map_of_injective eH.injective,
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hA]
  have hA₀P : A₀ ≤ radical P :=
    (Subgroup.map_mono (Subgroup.map_mono hAB)).trans hBP
  have ht₀ : ∃ t ∈ A₀, IsTransvection t := by
    obtain ⟨a, ha, ht⟩ := ht
    exact ⟨eH (MulAut.conj g₀ a), ⟨_, ⟨a, ha, rfl⟩, rfl⟩, ht⟩
  obtain ⟨k, hk, hcenter, hrad⟩ := order_two_transvection_conjugate_center
    L P F hLP hPF hL hP hF S hS A₀ hA₀ hA₀P ht₀
  refine ⟨k, hk, ?_, ?_⟩
  · rw [map_conj_adjusted]
    exact hcenter
  · rw [map_conj_adjusted]
    exact hrad _ hBP

/-- An actor in a plane radical with a fixed hyperplane is a genuine rank-one
transvection, with a nonzero image vector and a nonzero linear form. -/
theorem isTransvection_of_radical_fixed_codimension_one
    (P : Submodule (ZMod 2) V) {t : BinaryLinear.GL V} (htP : t ∈ radical P)
    (hfix : Module.finrank (ZMod 2) (LinearMap.ker (t.toLinearMap - LinearMap.id)) = 3) :
    IsTransvection t := by
  let d := t.toLinearMap - LinearMap.id
  have hd : Module.finrank (ZMod 2) d.range = 1 := by
    have hn := d.finrank_range_add_finrank_ker
    have hV : Module.finrank (ZMod 2) V = 4 := by simp [V]
    change Module.finrank (ZMod 2) d.ker = 3 at hfix
    omega
  have hd0 : d.range ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hd
    omega
  obtain ⟨w, hwR, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd0
  have heR : d.range = Submodule.span (ZMod 2) {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hd hwR hw
  have hwP : w ∈ P := by
    obtain ⟨v, rfl⟩ := hwR
    exact htP.2 v
  have htline : t ∈ radical (Submodule.span (ZMod 2) {w}) := by
    constructor
    · intro v hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, htP.1 w hwP]
    · intro v
      rw [← heR]
      exact ⟨v, rfl⟩
  have ht1 : t ≠ 1 := by
    intro he
    have hz : d = 0 := by ext v; simp [d, he]
    apply hd0
    rw [hz, LinearMap.range_zero]
  obtain ⟨f, hf, hfw, ht⟩ := exists_transvection_of_mem_line_radical hw htline ht1
  exact ⟨w, f, hw, hf, hfw, LinearEquiv.ext ht⟩

/-- For an order-two subgroup the common fixed hyperplane is the fixed hyperplane
of its unique nonidentity element. This supplies the transvection input above. -/
theorem exists_transvection_of_order_two_fixed_codimension_one
    (P : Submodule (ZMod 2) V) (A : Subgroup (BinaryLinear.GL V))
    (hA : Nat.card A = 2) (hAP : A ≤ radical P)
    (hfix : Module.finrank (ZMod 2) (BinaryLinear.fixedSpace A) = 3) :
    ∃ t ∈ A, IsTransvection t := by
  obtain ⟨t, ht1, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  refine ⟨t.val, t.property, isTransvection_of_radical_fixed_codimension_one P (hAP t.property) ?_⟩
  have he : LinearMap.ker (t.val.toLinearMap - LinearMap.id) = BinaryLinear.fixedSpace A := by
    ext v
    change (t.val v - v = 0) ↔ ∀ a ∈ A, a v = v
    constructor
    · intro hv a ha
      by_cases ha1 : a = 1
      · simp [ha1]
      have ha' : (⟨a, ha⟩ : A) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
      have hat : a = t.val := congrArg Subtype.val (huniq _ ha')
      rw [hat]
      exact sub_eq_zero.mp hv
    · intro hv
      exact sub_eq_zero.mpr (hv t.val t.property)
  rw [he, hfix]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootConjugacy
