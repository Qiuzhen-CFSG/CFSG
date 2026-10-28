module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry
public import Theory.AtlasPort.LinearGroups.G2.BinaryException

/-!
# Generation of the derived G₂ model by its restricted parabolics

For G₂(2), the common positive short-root element supplements the derived
subgroup in both full parabolics. It normalizes both intersections, so their
join is normal; the common cyclic supplement then proves that the restricted
parabolics generate the derived subgroup. No distribution of intersection
over subgroup join is used. Coefficientwise field transport treats every
field of order two, and perfectness handles the larger finite fields.

Source: the parabolic generation used in Aschbacher–Smith 2.3.9(7), p.526.
The binary sign and root calculations come from the licensed ATLAS modules
imported here; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.DerivedParabolicGeneration

open Subgroup
open scoped Pointwise

private theorem restricted_pair_generate {G : Type*} [Group G]
    (D P Q : Subgroup G) [D.Normal]
    (hgen : P ⊔ Q = ⊤) (t : G) (htP : t ∈ P) (htQ : t ∈ Q)
    (hfactor : ∀ x : G, x ∈ D ∨ x * t⁻¹ ∈ D) :
    (P ⊓ D) ⊔ (Q ⊓ D) = D := by
  let K := (P ⊓ D) ⊔ (Q ⊓ D)
  have htK : t ∈ normalizer (K : Set G) := by
    apply normalizer_inf_normalizer_le_normalizer_sup (P ⊓ D) (Q ⊓ D)
    exact ⟨inf_normalizer_le_normalizer_inf
      ⟨P.le_normalizer htP, by simp only [normalizer_eq_top]; trivial⟩,
      inf_normalizer_le_normalizer_inf
      ⟨Q.le_normalizer htQ, by simp only [normalizer_eq_top]; trivial⟩⟩
  have hDK : K ≤ D := sup_le inf_le_right inf_le_right
  have hN : (⊤ : Subgroup G) ≤ normalizer (K : Set G) := by
    rw [← hgen]
    apply sup_le
    · intro x hx
      rcases hfactor x with hd | hd
      · exact K.le_normalizer (mem_sup_left ⟨hx, hd⟩)
      · have hk : x * t⁻¹ ∈ K := mem_sup_left ⟨P.mul_mem hx (P.inv_mem htP), hd⟩
        simpa only [inv_mul_cancel_right] using
          (normalizer (K : Set G)).mul_mem (K.le_normalizer hk) htK
    · intro x hx
      rcases hfactor x with hd | hd
      · exact K.le_normalizer (mem_sup_right ⟨hx, hd⟩)
      · have hk : x * t⁻¹ ∈ K := mem_sup_right ⟨Q.mul_mem hx (Q.inv_mem htQ), hd⟩
        simpa only [inv_mul_cancel_right] using
          (normalizer (K : Set G)).mul_mem (K.le_normalizer hk) htK
  have : K.Normal := normalizer_eq_top_iff.mp (top_unique hN)
  have htop : K ⊔ closure {t} = ⊤ := by
    apply top_unique
    rw [← hgen]
    have ht : t ∈ K ⊔ closure {t} := mem_sup_right (subset_closure (by simp))
    apply sup_le
    · intro x hx
      rcases hfactor x with hd | hd
      · exact mem_sup_left (mem_sup_left ⟨hx, hd⟩)
      · have hk : x * t⁻¹ ∈ K := mem_sup_left ⟨P.mul_mem hx (P.inv_mem htP), hd⟩
        simpa only [inv_mul_cancel_right] using (K ⊔ closure {t}).mul_mem
          (mem_sup_left hk) ht
    · intro x hx
      rcases hfactor x with hd | hd
      · exact mem_sup_left (mem_sup_right ⟨hx, hd⟩)
      · have hk : x * t⁻¹ ∈ K := mem_sup_right ⟨Q.mul_mem hx (Q.inv_mem htQ), hd⟩
        simpa only [inv_mul_cancel_right] using (K ⊔ closure {t}).mul_mem
          (mem_sup_left hk) ht
  exact le_antisymm hDK (by
    intro x hx
    have hx' : x ∈ K ⊔ closure {t} := htop.symm ▸ mem_top x
    obtain ⟨k, hk, a, ha, rfl⟩ := mem_sup_of_normal_left.mp hx'
    have haD : a ∈ D := by simpa using D.mul_mem (D.inv_mem (hDK hk)) hx
    have haP : a ∈ P := ((closure_le P).mpr (by simpa using htP)) ha
    exact K.mul_mem hk (mem_sup_left ⟨haP, haD⟩))

open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.BinaryParabolicPair

theorem binary_restricted_pair_generate : (parabolic₁ (F := ZMod 2) ⊓ commutator (Model (ZMod 2))) ⊔
    (parabolic₂ ⊓ commutator (Model (ZMod 2))) = commutator (Model (ZMod 2)) := by
  apply restricted_pair_generate _ _ _ parabolics_generate shortRoot
    (borel_le_parabolic₁ (mem_sup_left shortRoot_mem_unipotent))
    (borel_le_parabolic₂ (mem_sup_left shortRoot_mem_unipotent))
  intro x
  have hmem (y : Model (ZMod 2)) (hy : Binary.lineSign y = 1) :
      y ∈ commutator (Model (ZMod 2)) := by
    rw [commutator_eq_longRootClosure, ← BinaryException.lineSign_kernel]
    exact hy
  rcases Int.units_eq_one_or (Binary.lineSign x) with hx | hx
  · exact Or.inl (hmem x hx)
  · apply Or.inr
    apply hmem
    rw [map_mul, map_inv, hx, shortRoot, Binary.lineSign_rootF_one]
    exact mul_inv_cancel _

variable {F K : Type*} [Field F] [Field K]

private theorem map_unipotent (e : F ≃+* K) :
    (unipotent (K := F)).map (fieldEquiv e).toMonoidHom = unipotent := by
  ext g
  simp only [mem_map, unipotent_eq_range]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨e ∘ t, (long_field_unipotentProduct e t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨unipotentProduct (e.symm ∘ t), ⟨_, rfl⟩, ?_⟩
    change fieldEquiv e (unipotentProduct (e.symm ∘ t)) = _
    rw [long_field_unipotentProduct]
    congr 1
    funext i
    exact e.apply_symm_apply _

private theorem map_weylS (e : F ≃+* K) : fieldEquiv e weylS = weylS := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [fieldEquiv, Atlas.SplitOctonion.transportAutomorphism,
    Atlas.SplitOctonion.transportLinear, Atlas.SplitOctonion.mapCoefficients,
    weylS, weylSEquiv, weylSLinear, weylSApply]

private theorem map_weylR (e : F ≃+* K) : fieldEquiv e weylR = weylR := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [fieldEquiv, Atlas.SplitOctonion.transportAutomorphism,
    Atlas.SplitOctonion.transportLinear, Atlas.SplitOctonion.mapCoefficients,
    weylR, weylREquiv, weylRLinear, weylRApply]

/-- Coefficient transport identifies both full parabolics over any field of
order two with the concrete binary pair. -/
theorem map_binary_parabolics [Finite F] (hq : Nat.card F = 2) :
    let e := fieldEquiv (binaryFieldEquiv hq)
    (parabolic₁ (F := F)).map e.toMonoidHom = parabolic₁ ∧
      (parabolic₂ (F := F)).map e.toMonoidHom = parabolic₂ := by
  dsimp only
  change (borel ⊔ closure {weylS}).map _ = borel ⊔ closure {weylS} ∧
    (borel ⊔ closure {weylR}).map _ = borel ⊔ closure {weylR}
  rw [borel_eq_unipotent_of_card_two hq, borel_binary]
  simp only [Subgroup.map_sup, map_unipotent, MonoidHom.map_closure, Set.image_singleton]
  change unipotent ⊔ closure {fieldEquiv (binaryFieldEquiv hq) weylS} = _ ∧
    unipotent ⊔ closure {fieldEquiv (binaryFieldEquiv hq) weylR} = _
  rw [map_weylS, map_weylR]
  exact ⟨rfl, rfl⟩

/-- The two parabolics still generate after restriction to the derived group. -/
theorem restricted_parabolics_generate [Finite F] :
    (parabolic₁ (F := F) ⊓ commutator (Model F)) ⊔
      (parabolic₂ ⊓ commutator (Model F)) = commutator (Model F) := by
  by_cases hq : Nat.card F = 2
  · let e := fieldEquiv (binaryFieldEquiv hq)
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have he : (commutator (Model F)).map e.toMonoidHom =
        commutator (Model (ZMod 2)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    rw [Subgroup.map_sup, map_inf _ _ _ e.injective, map_inf _ _ _ e.injective,
      he, (map_binary_parabolics hq).1, (map_binary_parabolics hq).2]
    exact binary_restricted_pair_generate
  · have : Group.IsPerfect (Model F) := isPerfect (by
      have := Finite.one_lt_card (α := F)
      omega)
    rw [Group.IsPerfect.commutator_eq_top, inf_top_eq, inf_top_eq, parabolics_generate]

end Atlas.G2.DerivedParabolicGeneration

end
