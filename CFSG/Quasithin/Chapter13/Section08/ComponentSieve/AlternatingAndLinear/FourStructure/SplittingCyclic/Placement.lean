module

public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.Representation.BinaryOffender.FixedGenerator
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.PlaneTransport

/-!
# Excluding A₁ from the natural irreducible submodule

A nonidentity two-subgroup normalized by the actual point parabolic has a
nonzero proper fixed space. The rigidity of the binary subspace stabilizer
forces that space to be the point itself. It therefore cannot also fix the
marked two-space. This supplies the A₁-placement contradiction directly from
concrete parabolic geometry. No abstract radical-irreducibility certificate
is assumed.

The representation on I is identified equivariantly with the actual binary
four-space. The last theorem transports the marked radical through the given
γ-to-α conjugator. The source application must obtain the normalization
premise from H = G₁ and Vγ normal in N_G(A₁); this file does not prove those
earlier source conclusions or identify an arbitrary quotient action with them.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.961 (PDF p.978).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

open BinaryLinear
local notation "Vec" => (Fin 4 → ZMod 2)

/-- A nonidentity two-subgroup normalized by a point parabolic cannot fix a
plane. This is a direct fixed-space form of the point-radical obstruction. -/
theorem point_parabolic_cannot_normalize_plane_fixer
    (L P : Submodule (ZMod 2) Vec)
    (hL : Module.finrank (ZMod 2) L = 1) (hP : Module.finrank (ZMod 2) P = 2)
    (B : Subgroup (BinaryLinear.GL Vec)) (hB : B ≠ ⊥) (hBtwo : IsPGroup 2 B)
    (hfix : P ≤ BinaryLinear.fixedSpace B)
    (hnorm : parabolic L ≤ Subgroup.normalizer (B : Set (BinaryLinear.GL Vec))) : False := by
  have hcard : 2 ∣ Nat.card Vec := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    norm_num
  have hF0 := BinaryLinear.fixedSpace_ne_bot hcard hBtwo
  have hFt := BinaryLinear.fixedSpace_ne_top hB
  have he : L = BinaryLinear.fixedSpace B :=
    FourParabolicAction.parabolic_le_imp_eq hF0 hFt
      (hnorm.trans (normalizer_le_parabolic_fixedSpace B))
  have hd := Submodule.finrank_mono hfix
  rw [← he, hL, hP] at hd
  omega

private theorem fixes_binary_point {L : Submodule (ZMod 2) Vec}
    (hL : Module.finrank (ZMod 2) L = 1) {g : BinaryLinear.GL Vec}
    (hg : g ∈ parabolic L) {v : Vec} (hv : v ∈ L) : g v = v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hL hv hv0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ (hg v).mpr hv)
  have hc0 : c ≠ 0 := by
    intro hz
    exact hv0 (g.map_eq_zero_iff.mp (by simpa [hz] using hc.symm))
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- The A₁-placement contradiction on the actual subrepresentation I.
The source's H = G₁ supplies `hnorm`: elements fixing A₁ normalize Vγ*.
The marked line parabolic is represented by its genuine two-dimensional
subspace P and its radical, and the action on I is identified equivariantly. -/
theorem A1_not_le_natural_submodule
    (A : Submodule (ZMod 2) U) (hA : Module.finrank (ZMod 2) A = 1)
    (I : Subrepresentation ρ)
    (eH : H ≃* BinaryLinear.GL Vec) (eI : I.toSubmodule ≃ₗ[ZMod 2] Vec)
    (heI : ∀ g v, eI (I.toRepresentation g v) = eH g (eI v))
    (V : Subgroup H) (hV : V ≠ ⊥) (hVtwo : IsPGroup 2 V)
    (hnorm : ∀ g : H, (∀ a ∈ A, ρ g a = a) →
      g ∈ Subgroup.normalizer (V : Set H))
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2)
    (hrad : V.map eH.toMonoidHom ≤ radical P) : ¬ A ≤ I.toSubmodule := by
  intro hAI
  let AI := A.comap I.toSubmodule.subtype
  let L := AI.map eI.toLinearMap
  have hAI_dim : Module.finrank (ZMod 2) AI = 1 := by
    rw [← Submodule.finrank_map_subtype_eq I.toSubmodule AI]
    have he : AI.map I.toSubmodule.subtype = A := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hAI]
    rw [he, hA]
  have hL : Module.finrank (ZMod 2) L = 1 :=
    (LinearEquiv.finrank_map_eq eI AI).trans hAI_dim
  let B := V.map eH.toMonoidHom
  have hB : B ≠ ⊥ := by
    intro hb
    apply hV
    apply bot_unique
    intro v hv
    have hm : eH v ∈ B := Subgroup.mem_map_of_mem _ hv
    rw [hb] at hm
    exact eH.injective (by simpa using hm)
  apply point_parabolic_cannot_normalize_plane_fixer L P hL hP B hB
    (hVtwo.map eH.toMonoidHom)
  · intro p hp b hb
    exact (hrad hb).1 p hp
  · rw [Subgroup.le_normalizer_iff]
    intro g hg b hb
    let k := eH.symm g
    have hk : k ∈ Subgroup.normalizer (V : Set H) := by
      apply hnorm
      intro a ha
      let ai : I.toSubmodule := ⟨a, hAI ha⟩
      have hai : eI ai ∈ L := ⟨ai, ha, rfl⟩
      have hf : eH k (eI ai) = eI ai := by
        simpa only [k, eH.apply_symm_apply] using fixes_binary_point hL hg hai
      have he : I.toRepresentation k ai = ai := eI.injective ((heI k ai).trans hf)
      exact congrArg Subtype.val he
    obtain ⟨v, hv, rfl⟩ := hb
    refine Subgroup.mem_map.mpr ⟨k * v * k⁻¹, (hk v).mp hv, ?_⟩
    simp [k]

/-- The same placement obstruction retains the actual γ-to-α conjugator.
The inverse image of the marked plane is used for the γ action. -/
theorem A1_not_le_natural_submodule_of_conjugate_radical
    (A : Submodule (ZMod 2) U) (hA : Module.finrank (ZMod 2) A = 1)
    (I : Subrepresentation ρ)
    (eH : H ≃* BinaryLinear.GL Vec) (eI : I.toSubmodule ≃ₗ[ZMod 2] Vec)
    (heI : ∀ g v, eI (I.toRepresentation g v) = eH g (eI v))
    (V : Subgroup H) (hV : V ≠ ⊥) (hVtwo : IsPGroup 2 V)
    (hnorm : ∀ g : H, (∀ a ∈ A, ρ g a = a) →
      g ∈ Subgroup.normalizer (V : Set H))
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2)
    (g : H)
    (hrad : (V.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤ radical P) :
    ¬ A ≤ I.toSubmodule := by
  apply A1_not_le_natural_submodule ρ A hA I eH eI heI V hV hVtwo hnorm
    (P.map (eH g⁻¹).toLinearMap)
  · exact (LinearEquiv.finrank_map_eq (eH g⁻¹) P).trans hP
  · exact le_radical_of_conjugate eH P V g hrad

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
