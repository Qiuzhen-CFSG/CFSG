module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalCoordinates.Marking
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalPreimage.Coordinates
public import Theory.Representation.TensorFunctionCoordinates

/-!
# From the natural tensor section to marked parabolic coordinates

A finite basis of the multiplicity space converts the natural tensor
model into functions with values in the binary augmentation plane.
The section kernel pulls its fixed space back to W. Conjugating by the
internal representative gives the second marked line X = Wᵍ, with the
original right-conjugation convention. The construction includes zero
multiplicity and keeps the literal ambient action.

Source: Aschbacher–Smith, Lemma 12.8.9(2–3), printed p.853.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise TensorProduct
open InvertedCubicTensor
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem imageSpace_coordinates_iff {H S E : Subgroup G}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) H M}
    (d : Representation.BinaryConjugationSection H S E ρ)
    (B : Subgroup G) (hEB : E ≤ B) (s : S) :
    (d.coordinates s).toAdd ∈ d.imageSpace B ↔ (s : G) ∈ B := by
  constructor
  · intro hs
    obtain ⟨b, hb, he⟩ := (d.mem_imageSpace_iff B _).mp hs
    have he' : d.coordinates b = d.coordinates s := Multiplicative.toAdd.injective he
    have hk : ((b⁻¹ * s : S) : G) ∈ E := (d.coordinates_eq_one_iff _).mp (by
      simp only [map_mul, map_inv, he', inv_mul_cancel])
    simpa using B.mul_mem hb (hEB hk)
  · intro hs
    exact (d.mem_imageSpace_iff B _).mpr ⟨s, hs, rfl⟩

private theorem marked_core_line : ∀ p : Equiv.Perm (Fin 3),
    p⁻¹ * Equiv.swap 1 2 * p = Equiv.swap 0 2 →
    ∀ v : Fin 3 → ZMod 2, (∑ i, v i) = 0 →
      (v (p.symm 0) = 0 ↔ v 1 = 0) := by decide

/-- Convert a marked natural tensor section to the literal action record.
The next source theorem constructs every input to this coordinate bridge. -/
theorem parabolic_natural_module_of_tensor (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hEcomm : ⁅F.E g, F.I₂ L⁆ = F.Vi 2)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    (u h : F.I₂ L) (hu : (u : G) ∈ F.U) (huw : (u : G) ∉ F.W)
    (hX : F.X (h : G) = F.X g)
    (hmarkU : ∀ v : F.I₂ L, (v : G) ∈ F.U → (v : G) ∉ F.W →
      F.binaryCoreProjection L e v = Equiv.swap 1 2)
    (hmarkX : F.binaryCoreProjection L e (h⁻¹ * u * h) = Equiv.swap 0 2)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) S₃ M)
    (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
      (F.E g) (σ.comp (F.binaryCoreProjection L e)))
    [Finite (multiplicitySpace σ)]
    (j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] M)
    (hj : ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
      (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
        σ a (j z))
    (hfixed : LinearMap.ker (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W) :
    ∃ m : ℕ, Nonempty (F.ParabolicNaturalModule L g (Fin m)) := by
  classical
  let π := F.binaryCoreProjection L e
  let q := Representation.tensorFunctionCoordinates j
  let m := Module.finrank (ZMod 2) (multiplicitySpace σ)
  let r : ↥(F.W ⊔ F.X g) ≃* ↥((F.I₂ L).pCoreIn 2) :=
    MulEquiv.subgroupCongr hsplit.symm
  let qm := q.toAddEquiv.toMultiplicative
  let c : ↥(F.W ⊔ F.X g) →* Multiplicative (Fin m → BinaryPermutation.core (Fin 3)) :=
    qm.toMonoidHom.comp (d.coordinates.comp r.toMonoidHom)
  have hq (a : S₃) (v : M) (i : Fin m) :
      q (σ a v) i = BinaryPermutation.coreRepresentation (Fin 3) a (q v i) :=
    Representation.tensorFunctionCoordinates_equivariant _ σ j hj a v i
  have hc (s : ↥(F.W ⊔ F.X g)) : (c s).toAdd = q (d.coordinates (r s)).toAdd := rfl
  have hW (s : ↥((F.I₂ L).pCoreIn 2)) :
      (s : G) ∈ F.W ↔ ∀ i : Fin m, (q (d.coordinates s).toAdd i).val 0 = 0 := by
    rw [← imageSpace_coordinates_iff d F.W inf_le_left s, ← hfixed]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [← q.injective.eq_iff, funext_iff]
    simp only [hq, hmarkU u hu huw]
    apply forall_congr'
    intro i
    have hf := ParabolicNaturalModule.natural_displacement_eq_zero_iff (q (d.coordinates s).toAdd i)
    rw [sub_eq_zero] at hf
    exact eq_comm.trans hf
  have hconj (i : F.I₂ L) (s t : ↥((F.I₂ L).pCoreIn 2))
      (ht : (t : G) = (i : G) * s * (i : G)⁻¹) :
      (d.coordinates t).toAdd = σ (π i) (d.coordinates s).toAdd := by
    have he : t = ⟨(i : G) * s * (i : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized i.property) s).mp s.property⟩ :=
      Subtype.ext ht
    rw [he]
    exact d.equivariant i s
  refine ⟨m, ⟨{
    generation := hgen
    core_eq := hsplit
    E_commutator := hEcomm
    quotient := e
    coordinates := c
    onto := qm.surjective.comp (d.onto.comp r.surjective)
    kernel := ?_
    equivariant := ?_
    W_marking := ?_
    X_marking := ?_
    U_marking := ?_
  }⟩⟩
  · ext s
    change qm (d.coordinates (r s)) = 1 ↔ (s : G) ∈ F.E g
    rw [← qm.map_one, qm.injective.eq_iff, d.coordinates_eq_one_iff]
    rfl
  · intro i s t ht k
    rw [hc, hc, hconj i (r s) (r t) ht, hq]
    rw [show π i = e (QuotientGroup.mk' (pCore 2 (F.I₂ L)) i) from
      F.binaryCoreProjection_apply L e i]
  · intro s
    exact hW (r s)
  · intro s
    let s' : ↥((F.I₂ L).pCoreIn 2) :=
      ⟨(h : G) * s * (h : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized h.property) (s : G)).mp (r s).property⟩
    have hs : (s : G) ∈ F.X g ↔ (s' : G) ∈ F.W := by
      have hm : (s : G) ∈ F.X g ↔ (s : G) ∈ F.X (h : G) :=
        Iff.of_eq (congrArg (fun B : Subgroup G => (s : G) ∈ B) hX.symm)
      rw [hm]
      constructor
      · rintro ⟨w, hw, he⟩
        have he' : (h : G)⁻¹ * w * h = (s : G) := by simpa using he
        change (h : G) * s * (h : G)⁻¹ ∈ F.W
        rw [← he']
        simpa [mul_assoc] using hw
      · intro hw
        refine ⟨s', hw, ?_⟩
        change (h : G)⁻¹ * ((h : G) * s * (h : G)⁻¹) * ((h : G)⁻¹)⁻¹ = (s : G)
        group
    rw [hs, hW s']
    have heq : (d.coordinates s').toAdd = σ (π h) (d.coordinates (r s)).toAdd :=
      hconj h (r s) s' rfl
    have hp : (π h)⁻¹ * Equiv.swap 1 2 * π h = Equiv.swap 0 2 := by
      simpa only [map_mul, map_inv, hmarkU u hu huw] using hmarkX
    apply forall_congr'
    intro i
    rw [heq, hq, hc]
    exact marked_core_line (π h) hp _ (q (d.coordinates (r s)).toAdd i).property
  · intro v hv
    simpa only [F.binaryCoreProjection_apply] using
      hmarkU ⟨v, le_conjugateSpanBy F.U (F.P L) v.property⟩ v.property hv
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
