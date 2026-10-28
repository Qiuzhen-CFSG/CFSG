module

public import Theory.Representation.BinaryPermutation.EightPointSylow
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation


/-!
# Rigidity of the binary A₈ point-Sylow fixed space

The commuting involutions (01)(23)(45)(67) and (46)(57) generate a
two-subgroup of the stabilizer of the word supported on {0,1}. Their
coordinate orbits have sizes 2, 2, 4, so their fixed space is spanned by
the first two orbit indicators and the constant word. Its only weight-two
words are the two orbit indicators.

Transport this subgroup into any Sylow of a weight-two stabilizer.
An additive equivalence preserving weight two, the marked word, the
constant word and the Sylow fixed space must fix that space pointwise.
The proof only needs containment in the three-space; it does not assert
equality with the Sylow fixed space.

Source: Aschbacher--Smith, 12.2.16, printed p.800, the point-fixed
comparison in the corrected central-omega decomposition.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.EightPointRigidity
private abbrev Ω := Fin 8
private abbrev A8 := alternatingGroup Ω
private abbrev B := core Ω
private abbrev K4 := Multiplicative (ZMod 2 × ZMod 2)
private def v0 : B := ⟨![1,1,0,0,0,0,0,0], by rw [mem_core]; decide⟩
private def u0 : B := ⟨![0,0,1,1,0,0,0,0], by rw [mem_core]; decide⟩
private def c0 : B := ⟨allOne Ω, by rw [mem_core]; decide⟩
private def x : A8 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7,
  by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def y : A8 := ⟨Equiv.swap 4 6 * Equiv.swap 5 7,
  by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def klein : K4 →* A8 where
  toFun a := (if a.toAdd.1 = 0 then 1 else x) * (if a.toAdd.2 = 0 then 1 else y)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
private theorem klein_fixes : ∀ a : K4, alternatingCoreRepresentation Ω (klein a) v0 = v0 := by
  decide +kernel
private theorem klein_two : IsPGroup 2 K4 := by
  intro a
  exact ⟨1, (by decide : ∀ a : K4, a ^ 2 = 1) a⟩

private theorem shape (w : B)
    (hx : alternatingCoreRepresentation Ω x w = w)
    (hy : alternatingCoreRepresentation Ω y w = w) :
    ∃ a : ZMod 2, ∃ b : ZMod 2, ∃ d : ZMod 2,
      w = a • v0 + b • u0 + d • c0 := by
  have h01 := congrArg (fun t : B => t.val 0) hx
  have h23 := congrArg (fun t : B => t.val 2) hx
  have h45 := congrArg (fun t : B => t.val 4) hx
  have h67 := congrArg (fun t : B => t.val 6) hx
  have h46 := congrArg (fun t : B => t.val 4) hy
  change w.val 1 = w.val 0 at h01
  change w.val 3 = w.val 2 at h23
  change w.val 5 = w.val 4 at h45
  change w.val 7 = w.val 6 at h67
  change w.val 6 = w.val 4 at h46
  refine ⟨w.val 0 + w.val 4, w.val 2 + w.val 4, w.val 4, ?_⟩
  apply Subtype.ext
  funext i
  change w.val i = (w.val 0 + w.val 4) * v0.val i +
    (w.val 2 + w.val 4) * u0.val i + w.val 4 * 1
  fin_cases i <;>
    simp [v0, u0, h01, h23, h45, h67, h46,
      add_assoc, CharTwo.add_self_eq_zero]

private theorem weight_two_shape : ∀ a b d : ZMod 2,
    wordWeight (a • v0 + b • u0 + d • c0).val = 2 →
      a • v0 + b • u0 + d • c0 = v0 ∨ a • v0 + b • u0 + d • c0 = u0 := by
  decide +kernel


private abbrev ρ := alternatingCoreRepresentation Ω
private theorem act_inv (g : A8) (w : B) : ρ g (ρ g⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
private theorem inv_act (g : A8) (w : B) : ρ g⁻¹ (ρ g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
private theorem act_constant (g : A8) : ρ g c0 = c0 := by
  apply Subtype.ext
  exact permute_allOne Ω g.val
private theorem conjugate_fixed (g a : A8) (w : B)
    (hw : ρ (g * a * g⁻¹) w = w) : ρ a (ρ g⁻¹ w) = ρ g⁻¹ w := by
  have hh := congrArg (ρ g⁻¹) hw
  simpa only [map_mul, Module.End.mul_apply, inv_act] using hh

private theorem sylow_shape (v : B) (hv : wordWeight v.val = 2)
    (P : Sylow 2 (EightPointSylow.stabilizer v.val)) :
    ∃ u : B, wordWeight u.val = 2 ∧ u ≠ v ∧
      (∀ w ∈ fixedSpace ρ ((P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype),
        ∃ a b d : ZMod 2, w = a • v + b • u + d • c0) ∧
      (∀ w ∈ fixedSpace ρ ((P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype),
        wordWeight w.val = 2 → w = v ∨ w = u) := by
  obtain ⟨k,hk'⟩ := exists_even_permutation_of_weight (by decide : 3 ≤ Fintype.card Ω)
    v0.val v.val (by rw [hv]; decide)
  have hk : ρ k v0 = v := Subtype.ext hk'
  let f₀ : K4 →* A8 := (MulAut.conj k).toMonoidHom.comp klein
  have hf (a : K4) : f₀ a ∈ EightPointSylow.stabilizer v.val := by
    have hh : ρ (k * klein a * k⁻¹) v = v := by
      rw [← hk]
      simp only [map_mul, Module.End.mul_apply, inv_act, klein_fixes]
    exact congrArg Subtype.val hh
  let f : K4 →* EightPointSylow.stabilizer v.val := f₀.codRestrict _ hf
  have hp : IsPGroup 2 f.range := klein_two.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (EightPointSylow.stabilizer v.val) Q P
  let s : A8 := g.val * k
  have hs : ρ s v0 = v := by
    change ρ (g.val * k) v0 = v
    rw [map_mul, Module.End.mul_apply, hk]
    exact Subtype.ext g.property
  have hc (a : K4) : s * klein a * s⁻¹ ∈
      (P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype := by
    have ha : g * f a * g⁻¹ ∈ (P : Subgroup _) := by
      rw [← hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ ⟨a,rfl⟩)
    have hh := mem_map_of_mem (EightPointSylow.stabilizer v.val).subtype ha
    simpa [s, f, f₀, MulAut.conj_apply, mul_assoc] using hh
  have hsmall (w : B)
      (hw : w ∈ fixedSpace ρ ((P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype))
      (a : K4) : ρ (klein a) (ρ s⁻¹ w) = ρ s⁻¹ w :=
    conjugate_fixed s (klein a) w (hw ⟨_,hc a⟩)
  have hshape (w : B)
      (hw : w ∈ fixedSpace ρ ((P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype)) :
      ∃ a b d : ZMod 2, ρ s⁻¹ w = a • v0 + b • u0 + d • c0 := by
    apply shape
    · simpa only [show klein (Multiplicative.ofAdd (1,0)) = x by decide] using
        hsmall w hw (Multiplicative.ofAdd (1,0))
    · simpa only [show klein (Multiplicative.ofAdd (0,1)) = y by decide] using
        hsmall w hw (Multiplicative.ofAdd (0,1))
  refine ⟨ρ s u0, ?_, ?_, ?_, ?_⟩
  · exact (wordWeight_permute s.val u0.val).trans (by decide)
  · intro he
    have hh := congrArg (ρ s⁻¹) (he.trans hs.symm)
    simp only [inv_act] at hh
    exact (by decide : u0 ≠ v0) hh
  · intro w hw
    obtain ⟨a,b,d,he⟩ := hshape w hw
    have hh := congrArg (ρ s) he
    simp only [act_inv, map_add, map_smul, hs, act_constant] at hh
    exact ⟨a,b,d,hh⟩
  · intro w hw hw2
    obtain ⟨a,b,d,he⟩ := hshape w hw
    have hw2' : wordWeight (ρ s⁻¹ w).val = 2 :=
      (wordWeight_permute s⁻¹.val w.val).trans hw2
    rw [he] at hw2'
    rcases weight_two_shape a b d hw2' with hh | hh
    · have ht := congrArg (ρ s) (he.trans hh)
      simpa only [act_inv, hs] using Or.inl ht
    · have ht := congrArg (ρ s) (he.trans hh)
      exact Or.inr (by simpa only [act_inv] using ht)

private theorem shape_rigidity (F : Submodule (ZMod 2) B) (v u c : B)
    (hvF : v ∈ F) (hcF : c ∈ F) (hu : wordWeight u.val = 2) (huv : u ≠ v)
    (hs : ∀ w ∈ F, ∃ a b d : ZMod 2, w = a • v + b • u + d • c)
    (h2 : ∀ w ∈ F, wordWeight w.val = 2 → w = v ∨ w = u)
    (e : B ≃+ B) (he2 : ∀ w : B, wordWeight w.val = 2 → wordWeight (e w).val = 2)
    (hev : e v = v) (hec : e c = c) (heF : ∀ w ∈ F, e w ∈ F) :
    ∀ w ∈ F, e w = w := by
  have he_sm (a : ZMod 2) (b : B) : e (a • b) = a • e b := ZMod.map_smul e a b
  have he_u (huF : u ∈ F) : e u = u := by
    rcases h2 (e u) (heF u huF) (he2 u hu) with hh | hh
    · exact (huv (e.injective (hh.trans hev.symm))).elim
    · exact hh
  intro w hw
  obtain ⟨a,b,d,rfl⟩ := hs w hw
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
  · simp only [zero_smul, add_zero, map_add, he_sm, hev, hec]
  · have huF : u ∈ F := by
      have hh := F.sub_mem (F.sub_mem hw (F.smul_mem a hvF)) (F.smul_mem d hcF)
      have he : a • v + (1 : ZMod 2) • u + d • c - a • v - d • c = u := by
        simp only [one_smul]
        abel
      rwa [he] at hh
    simp only [one_smul, map_add, he_sm, hev, hec, he_u huF]

/-- Rigidity of the fixed space of a point-stabilizer Sylow in the binary A₈ core. -/
theorem fixedSpace_rigidity (v c : core (Fin 8)) (hv : wordWeight v.val = 2)
    (hc : ∀ i, c.val i = 1) (P : Sylow 2 (EightPointSylow.stabilizer v.val))
    (e : core (Fin 8) ≃+ core (Fin 8)) (he2 : ∀ w : core (Fin 8), wordWeight w.val = 2 → wordWeight (e w).val = 2)
    (hev : e v = v) (hec : e c = c)
    (heF : ∀ w ∈ fixedSpace (alternatingCoreRepresentation (Fin 8)) ((P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype),
      e w ∈ fixedSpace (alternatingCoreRepresentation (Fin 8)) ((P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype)) :
    ∀ w ∈ fixedSpace (alternatingCoreRepresentation (Fin 8)) ((P : Subgroup _).map (EightPointSylow.stabilizer v.val).subtype),
      e w = w := by
  have hcc : c = c0 := Subtype.ext (funext hc)
  subst c
  obtain ⟨u,hu,huv,hs,h2⟩ := sylow_shape v hv P
  apply shape_rigidity _ v u c0 ?_ ?_ hu huv hs h2 e he2 hev hec heF
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb,rfl⟩ := ha
    exact Subtype.ext b.property
  · intro a
    exact act_constant a.val
end BinaryPermutation.EightPointRigidity
