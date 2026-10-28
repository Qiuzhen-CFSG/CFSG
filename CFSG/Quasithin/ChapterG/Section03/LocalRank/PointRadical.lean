module

public import CFSG.Quasithin.ChapterG.Section03.LocalRank.Geometry
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness

/-!
# Point radicals in the local rank argument

The stabilizer of a nonzero binary vector is transitive on the nonidentity
members of its point radical. Indeed, for two nonzero forms vanishing on the
vector, a transvection interchanges the forms and fixes the vector. Thus a
nontrivial invariant subgroup is the whole radical, the irreducibility step in
G.3.1. The radical is also in bijection with the annihilator of the center line.

Source: Aschbacher--Smith, G.3.1, printed p. 337, second proof paragraph.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03.LocalRank
open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_scalar {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem form_one {f : V →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) :
    ∃ v, f v = 1 := by
  have hh : ∃ v, f v ≠ 0 := by
    by_contra! hh
    exact hf (LinearMap.ext hh)
  obtain ⟨v, hv⟩ := hh
  exact ⟨v, binary_scalar hv⟩

private theorem forms_common_one {f k : V →ₗ[ZMod 2] ZMod 2}
    (hf : f ≠ 0) (hk : k ≠ 0) : ∃ v, f v = 1 ∧ k v = 1 := by
  obtain ⟨a, ha⟩ := form_one hf
  by_cases hka : k a = 0
  · obtain ⟨b, hb⟩ := form_one hk
    by_cases hfb : f b = 0
    · exact ⟨a + b, by simp [ha, hfb], by simp [hka, hb]⟩
    · exact ⟨b, binary_scalar hfb, hb⟩
  · exact ⟨a, ha, binary_scalar hka⟩

private theorem radical_as_transvection {x : V} (hx : x ≠ 0)
    {t : GL V} (ht : t ∈ radical (centerLine x)) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, ∃ hfx : f x = 0,
      t = transvection x f hfx := by
  obtain ⟨_, f, hfx, he⟩ := (mem_rootGroup_iff (G := ⊤) hx).mp ⟨Subgroup.mem_top _, ht⟩
  exact ⟨f, hfx, he⟩

/-- A point stabilizer is transitive on the nonidentity elements of its radical. -/
theorem point_radical_conjugacy {x : V} (hx : x ≠ 0)
    {s t : GL V} (hs : s ∈ radical (centerLine x)) (ht : t ∈ radical (centerLine x))
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    ∃ e : GL V, e x = x ∧ e * s * e⁻¹ = t := by
  obtain ⟨f, hfx, rfl⟩ := radical_as_transvection hx hs
  obtain ⟨k, hkx, rfl⟩ := radical_as_transvection hx ht
  have hf : f ≠ 0 := by
    intro hh
    apply hs1
    ext v
    simp [transvection, hh]
  have hk : k ≠ 0 := by
    intro hh
    apply ht1
    ext v
    simp [transvection, hh]
  obtain ⟨a, hfa, hka⟩ := forms_common_one hf hk
  have hsum : (f + k) a = 0 := by
    simp only [LinearMap.add_apply, hfa, hka]
    decide
  let e := transvection a (f + k) hsum
  have hex : e x = x := by simp [e, transvection, hfx, hkx]
  have hef (v : V) : f (e v) = k v := by
    change f (v + (f + k) v • a) = k v
    simp only [map_add, map_smul, LinearMap.add_apply, hfa, smul_eq_mul, mul_one]
    have hh : f v + f v = 0 :=
      (by decide : ∀ a : ZMod 2, a + a = 0) (f v)
    rw [← add_assoc, hh, zero_add]
  refine ⟨e, hex, ?_⟩
  ext v
  change e ((e⁻¹ v) + f (e⁻¹ v) • x) = v + k v • x
  rw [map_add, map_smul, hex]
  have hei (v : V) : e⁻¹ v = e v := rfl
  rw [hei, hef]
  change e (e v) + k v • x = v + k v • x
  rw [show e (e v) = v from e.apply_symm_apply v]

/-- A nontrivial subgroup of the radical invariant under the point stabilizer is full. -/
theorem point_radical_eq_of_invariant {x : V} (hx : x ≠ 0)
    (H : Subgroup (GL V)) (hH : H ≤ radical (centerLine x)) (hH0 : H ≠ ⊥)
    (hinv : ∀ e : GL V, e x = x → ∀ s ∈ H, e * s * e⁻¹ ∈ H) :
    H = radical (centerLine x) := by
  apply le_antisymm hH
  obtain ⟨s, hs, hs1⟩ := H.bot_or_exists_ne_one.resolve_left hH0
  intro t ht
  by_cases ht1 : t = 1
  · simpa only [ht1] using H.one_mem
  obtain ⟨e, hex, he⟩ := point_radical_conjugacy hx (hH hs) ht hs1 ht1
  rw [← he]
  exact hinv e hex s hs

/-- The lifted stabilizer normalizes the image of the actual root group. -/
theorem rootAction_range_invariant {G : Subgroup (GL V)} {Δ : Set V}
    (hfull : FullAction G Δ) (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val)
    (e : GL (blockSpace G Δ i))
    (hex : e ⟨x, Submodule.subset_span hx⟩ = ⟨x, Submodule.subset_span hx⟩) :
    ∀ s ∈ (rootAction i hx).range, e * s * e⁻¹ ∈ (rootAction i hx).range := by
  obtain ⟨g, rfl⟩ := hfull.surjective i e
  have hgx : g.val x = x := congrArg Subtype.val hex
  rintro _ ⟨t, rfl⟩
  have hmem : g.val * t.val * g.val⁻¹ ∈ rootGroup G x := by
    simpa only [hgx] using
      conjugate_mem_rootGroup (generated_le G i.val g.property) t.property
  refine ⟨⟨g.val * t.val * g.val⁻¹, hmem⟩, ?_⟩
  ext v
  rfl

/-- Recognition of the restriction image, once its nontriviality is known. -/
theorem rootAction_range_eq_radical {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hfull : FullAction G Δ) (i : OrbitBlock G Δ)
    {x : V} (hx : x ∈ i.val) (himage : (rootAction i hx).range ≠ ⊥) :
    (rootAction i hx).range = radical (centerLine
      (⟨x, Submodule.subset_span hx⟩ : blockSpace G Δ i)) := by
  apply point_radical_eq_of_invariant
    (fun he => h.nonzero x (block_subset h i hx) (congrArg Subtype.val he))
    _ (rootAction_range_le_radical i hx) himage
  exact rootAction_range_invariant hfull i hx

/-- The point radical has one binary parameter for each complementary dimension. -/
theorem point_radical_card [FiniteDimensional (ZMod 2) V] {x : V} (hx : x ≠ 0) :
    Nat.card (radical (centerLine x)) = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  let L := centerLine x
  let F := L.dualAnnihilator
  have hfx (f : F) : f.val x = 0 :=
    (Submodule.mem_dualAnnihilator (W := L) f.val).mp f.property x (Submodule.mem_span_singleton_self x)
  let φ : F → radical L := fun f =>
    ⟨transvection x f.val (hfx f), transvection_mem
      (Submodule.mem_span_singleton_self x)
      ((Submodule.mem_dualAnnihilator (W := L) f.val).mp f.property)⟩
  have hi : Function.Injective φ := by
    intro f k he
    apply Subtype.ext
    ext v
    have hv := congrArg (fun t : radical L => t.val v) he
    change v + f.val v • x = v + k.val v • x at hv
    exact (smul_left_injective (ZMod 2) hx) (add_left_cancel hv)
  have hs : Function.Surjective φ := by
    intro t
    obtain ⟨f, hfx', hf⟩ := radical_as_transvection hx t.property
    have hfF : f ∈ F := by
      apply (Submodule.mem_dualAnnihilator (W := L) f).mpr
      intro v hv
      rcases (mem_centerLine_iff x v).mp hv with rfl | rfl
      · exact f.map_zero
      · exact hfx'
    exact ⟨⟨f, hfF⟩, Subtype.ext hf.symm⟩
  have hdim : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) V - 1 := by
    have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq L
    have hL : Module.finrank (ZMod 2) L = 1 := finrank_span_singleton hx
    dsimp [F]
    omega
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hi, hs⟩)]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]

end CFSG.Quasithin.ChapterG.Section03.LocalRank
