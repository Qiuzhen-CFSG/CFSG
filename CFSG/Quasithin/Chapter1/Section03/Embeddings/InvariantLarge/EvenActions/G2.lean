module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Kernel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.FieldPowers
public import Theory.AtlasPort.LinearGroups.G2.Borel
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction

/-!
# Cartan field actions in the actual octonion G₂ model

The two unit parameters of the split torus act by diagonal octonion weights.
Coefficient transport acts on these parameters, hence by a common Frobenius
power on the torus. The concrete Borel decomposition and disjointness of
its unipotent and torus factors prove that the inner factor of a normalizing
Borel–field automorphism centralizes B. The resulting identity descends to
B/Φ(B) for any action realized by these actual automorphisms.

The final theorem retains the Borel–field realization as an explicit premise.
Deriving that realization from the raw almost-simple Sylow/Cartan setup of
A.3.15(5), including alignment of the source Cartan, remains a separate
obligation. No full abstract automorphism coverage is asserted here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511. The octonion matrices, torus and coefficient
transport are from the licensed ATLAS modules imported above; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2
open Atlas.G2 Atlas.SplitOctonion

/-- Coefficient transport applies the field automorphism to both actual octonion torus parameters. -/
theorem field_torus {F : Type*} [Field F] (σ : F ≃+* F) (l m : Fˣ) :
    fieldEquiv σ (torus l m) =
      torus (Units.map σ.toMonoidHom l) (Units.map σ.toMonoidHom m) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [fieldEquiv, transportAutomorphism, transportLinear, mapCoefficients,
      torus, torusEquiv, torusLinear, torusWeights]

/-- The genuine field action is a uniform power map on the entire split torus. -/
theorem field_torus_power {F : Type*} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) :
    ∃ k : ℕ, ∀ t ∈ splitTorus (K := F), fieldEquiv σ t = t ^ (2 ^ k) := by
  obtain ⟨k, hk⟩ := binary_field_power σ
  refine ⟨k, ?_⟩
  rintro t ⟨⟨l, m⟩, rfl⟩
  have hu (x : Fˣ) : Units.map σ.toMonoidHom x = x ^ (2 ^ k) := by
    apply Units.ext
    exact hk x
  change fieldEquiv σ (torus l m) = torusHom (l, m) ^ (2 ^ k)
  rw [field_torus, hu, hu, ← map_pow]
  rfl

/-- The image of the two unit parameters is abelian. -/
theorem torus_commutes {F : Type*} [Field F] {a b : Model F}
    (ha : a ∈ splitTorus) (hb : b ∈ splitTorus) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm x y]

/-- The actual octonion Borel normalizer of a torus subgroup centralizes it. -/
theorem borel_kernel {F : Type*} [Field F] (B : Subgroup (Model F))
    (hB : B ≤ splitTorus) :
    borel ⊓ normalizer B ≤ centralizer (B : Set (Model F)) := by
  intro d hd
  obtain ⟨⟨u, h⟩, he⟩ := borelProductEquiv.surjective ⟨d, hd.1⟩
  have he' : (u : Model F) * (h : Model F) = d := congrArg Subtype.val he
  let _ : IsMulCommutative (splitTorus (K := F)) :=
    ⟨⟨fun a b => Subtype.ext (torus_commutes a.property b.property)⟩⟩
  have hn : splitTorus (K := F) ≤ normalizer (unipotent (K := F) : Set (Model F)) := by
    apply le_normalizer_iff.mpr
    exact fun t ht u hu => torus_normalizes_unipotent ht hu
  rw [← he']
  exact borel_centralizes unipotent splitTorus B unipotent_disjoint_torus hn hB
    u.property h.property (he'.symm ▸ hd.2)

/-- Every subgroup of the split torus is invariant under each field automorphism. -/
theorem field_preserves_subgroup {F : Type*} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) (B : Subgroup (Model F)) (hB : B ≤ splitTorus) :
    B.map (fieldEquiv σ).toMonoidHom = B := by
  obtain ⟨k, hk⟩ := field_torus_power σ
  obtain ⟨l, hl⟩ := field_torus_power σ.symm
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change fieldEquiv σ a ∈ B
    rw [hk a (hB ha)]
    exact B.pow_mem ha _
  · intro hb
    refine ⟨fieldEquiv σ.symm b, ?_, ?_⟩
    · rw [hl b (hB hb)]
      exact B.pow_mem hb _
    · exact (fieldEquiv σ).apply_symm_apply b

/-- For a torus subgroup, a normalizing Borel–field automorphism has its inner factor in the action kernel. -/
theorem borel_field_power {F : Type*} [Field F] [Finite F] [CharP F 2]
    (B : Subgroup (Model F)) (hB : B ≤ splitTorus)
    (a : MulAut (Model F)) (haB : B.map a.toMonoidHom = B)
    (d : Model F) (hd : d ∈ borel) (σ : F ≃+* F)
    (ha : a = MulAut.conj d * fieldEquiv σ) :
    ∃ k : ℕ, ∀ b ∈ B, a b = b ^ (2 ^ k) := by
  have hdB : d ∈ normalizer B := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [ha] at haB
    change B.map ((MulAut.conj d).toMonoidHom.comp (fieldEquiv σ).toMonoidHom) = B at haB
    rw [← map_map, field_preserves_subgroup σ B hB] at haB
    exact haB
  have hc := borel_kernel B hB (show d ∈ borel ⊓ normalizer B from ⟨hd, hdB⟩)
  obtain ⟨k, hk⟩ := field_torus_power σ
  refine ⟨k, fun b hb => ?_⟩
  have hφb : fieldEquiv σ b ∈ B := by
    rw [hk b (hB hb)]
    exact B.pow_mem hb _
  calc
    a b = d * fieldEquiv σ b * d⁻¹ := by rw [ha]; rfl
    _ = fieldEquiv σ b := by
      rw [← mem_centralizer_iff.mp hc _ hφb, mul_inv_cancel_right]
    _ = b ^ (2 ^ k) := hk b (hB hb)

/-- An action realized by Borel–field automorphisms acts by powers on the actual Frattini quotient. The realization remains an explicit input. -/
theorem frattini_borel_field_power {F A : Type*} [Field F] [Finite F] [CharP F 2]
    [Group A] (B : Subgroup (Model F)) (hB : B ≤ splitTorus)
    (ρ : A →* MulAut B)
    (hρ : ∀ s : A, ∃ (d : Model F) (σ : F ≃+* F), d ∈ borel ∧
      ∀ b : B, (ρ s b : Model F) = (MulAut.conj d * fieldEquiv σ) (b : Model F)) :
    ∀ (s : A) (v : B ⧸ frattini B),
      quotientAut (frattini B) (ρ s) v ∈ zpowers v := by
  intro s v
  obtain ⟨d, σ, hd, he⟩ := hρ s
  let a : MulAut (Model F) := MulAut.conj d * fieldEquiv σ
  have haB : B.map a.toMonoidHom = B := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (he ⟨c, hc⟩).symm ▸ (ρ s ⟨c, hc⟩).property
    · intro hb
      obtain ⟨c, hc⟩ := (ρ s).surjective ⟨b, hb⟩
      refine ⟨c, c.property, ?_⟩
      exact (he c).symm.trans (congrArg Subtype.val hc)
  obtain ⟨k, hk⟩ := borel_field_power B hB a haB d hd σ rfl
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (frattini B) v
  have hb : ρ s b = b ^ (2 ^ k) :=
    Subtype.ext ((he b).trans (hk b b.property))
  rw [quotientAut_apply_mk, hb, map_pow]
  exact pow_mem (mem_zpowers _) _

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2
