module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.ActionFacts
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.Contracts
public import Theory.Representation.NormalInvariants
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
public import Theory.Representation.Quotient

/-!
# Natural coordinates for a supplied local quotient marking

The literal seed quotient V/V₂ is a binary plane with a fixed-point-free
L₂ actor. A nonzero invariant subspace must therefore be the whole plane:
a binary line admits only the identity automorphism. The two-core has a
nonzero fixed vector, and normality makes its fixed space invariant, so it
acts trivially. The actual conjugation representation consequently descends
through the supplied I₂/O₂(I₂) marking.

The marked cubic has no nonzero fixed vectors. The inverted-cubic tensor
equivalence has a one-dimensional multiplicity space and gives natural
coordinates intertwining the entire marked S₃ action. The final construction
copies the supplied group equivalence and both subgroup-image proofs.
Construction of that group marking is a separate obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4(2),(6), printed p.916, and the seed action in 13.8.6, printed p.948.
-/

public section

open Subgroup Module Representation
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking.SeedCoordinates
open EarlierCore RankDoubling.SourceAction InvertedCubicTensor

private theorem invariant_eq_top {A W : Type*} [Group A] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] (ρ : Representation F A W)
    (hd : finrank F W = 2) (a : A) (ha : ∀ w, ρ a w = w → w = 0)
    (S : Subrepresentation ρ) (hS : S.toSubmodule ≠ ⊥) : S.toSubmodule = ⊤ := by
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  have hp := finrank_pos (R := F) (M := S.toSubmodule)
  have hb := S.toSubmodule.finrank_le
  have hn : finrank F S.toSubmodule ≠ 1 := by
    intro hdim
    obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hv (S.toRepresentation a v)
    have hc0 : c ≠ 0 := by
      intro he
      rw [he, zero_smul] at hc
      have hh := congrArg (S.toRepresentation a⁻¹) hc
      simp only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply] at hh
      exact hv hh.symm
    have hc1 : c = 1 := by
      have h : ∀ c : F, c ≠ 0 → c = 1 := by decide
      exact h c hc0
    have hfix : ρ a v.val = v.val := by
      simpa [hc1, Subrepresentation.toRepresentation] using (congrArg Subtype.val hc).symm
    exact hv (Subtype.ext (ha v.val hfix))
  apply Submodule.eq_top_of_finrank_eq
  omega

private theorem plane_core_kernel {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F A W) (hd : finrank F W = 2)
    (a : A) (ha : ∀ w, ρ a w = w → w = 0) : pCore 2 A ≤ ρ.ker := by
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank F W)
  let S := fixedSubrepresentationOfNormal ρ (pCore 2 A)
  obtain ⟨v, hv, hf⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
    (ρ.comp (pCore 2 A).subtype) pCore_isPGroup
  have hS : S.toSubmodule ≠ ⊥ := by
    intro he
    have hm : v ∈ S.toSubmodule := hf
    rw [he, Submodule.mem_bot] at hm
    exact hv hm
  have ht := invariant_eq_top ρ hd a ha S hS
  intro n hn
  rw [MonoidHom.mem_ker]
  ext w
  have hw : w ∈ S.toSubmodule := ht ▸ Submodule.mem_top
  exact hw ⟨n, hn⟩

private theorem exists_plane_equiv {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (σ : Representation F S₃ W)
    (hd : finrank F W = 2) (hf : ∀ w, σ cubic w = w → w = 0) :
    ∃ e : W ≃ₗ[F] NaturalPlane, ∀ g w,
      e (σ g w) = BinaryPermutation.coreRepresentation (Fin 3) g (e w) := by
  have hdim := (pairEquiv σ hf).finrank_eq
  rw [Module.finrank_prod, hd] at hdim
  have hi : finrank F (multiplicitySpace σ) = 1 := by omega
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hi
  let f : NaturalPlane ≃ₗ[F] W := (TensorProduct.lid F NaturalPlane).symm.trans
    ((TensorProduct.congr e (LinearEquiv.refl F NaturalPlane)).trans (tensorEquiv σ hf))
  have he (n : NaturalPlane) : f n = tensorEquiv σ hf (e 1 ⊗ₜ[F] n) := by
    simp [f, TensorProduct.lid_symm_apply]
  have heq (g : S₃) (n : NaturalPlane) :
      f (BinaryPermutation.coreRepresentation (Fin 3) g n) = σ g (f n) := by
    rw [he, he, tensorEquiv_symmetric]
  refine ⟨f.symm, ?_⟩
  intro g w
  obtain ⟨n, rfl⟩ := f.surjective w
  rw [← heq, f.symm_apply_apply, f.symm_apply_apply]

noncomputable section
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H L V V₁ V₂ V₃ : Subgroup G}
  [IsElementaryAbelian 2 V]
  (s : NaturalSetup T L V V₁ V₂ V₃)

/-- The intrinsic two-core acts trivially on the literal seed quotient. -/
theorem seed_twoCore_le_ker : pCore 2 (localI L V₁ V₂) ≤ (seedRepresentation s).ker := by
  obtain ⟨l, hl⟩ := exists_seed_fixedFree_actor s
  exact plane_core_kernel (seedRepresentation s) (quotient_finrank s)
    (inclusion le_sup_right l) hl

variable (q : QuotientMarking L V₁ V₂)

/-- Descend the actual conjugation action using the supplied group marking. -/
def markedRepresentation : Representation F S₃ (Additive (SeedQuotient V V₂)) :=
  (Representation.quotientOfLEKer (seedRepresentation s) (pCore 2 (localI L V₁ V₂))
    (seed_twoCore_le_ker s)).comp q.localEquiv.symm.toMonoidHom

theorem markedRepresentation_projection (i : localI L V₁ V₂) :
    markedRepresentation s q (q.localEquiv (QuotientGroup.mk' (pCore 2 (localI L V₁ V₂)) i)) =
      seedRepresentation s i := by
  simp only [markedRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Representation.quotientOfLEKer_apply]

/-- The marked cubic has no nonzero fixed vectors, with its orientation retained. -/
theorem marked_cubic_fixedFree (x : Additive (SeedQuotient V V₂))
    (hx : markedRepresentation s q cubic x = x) : x = 0 := by
  obtain ⟨l, hl⟩ := exists_seed_fixedFree_actor s
  let i : localI L V₁ V₂ := inclusion le_sup_right l
  let c := q.localEquiv (QuotientGroup.mk' (pCore 2 (localI L V₁ V₂)) i)
  have hc : c ∈ zpowers cubic := by
    rw [← q.cubic_image]
    exact mem_map_of_mem _ l.property
  obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr hc
  have hpow : ∀ n : ℕ, markedRepresentation s q (cubic ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ, map_mul, Module.End.mul_apply, hx, ih]
  apply hl
  change seedRepresentation s i x = x
  rw [← markedRepresentation_projection s q i]
  change markedRepresentation s q c x = x
  rw [← hn]
  exact hpow n

/-- Natural coordinates on the literal V/V₂, equivariant for the supplied marking. -/
theorem exists_coordinates :
    ∃ e : Additive (SeedQuotient V V₂) ≃ₗ[F] NaturalPlane,
      ∀ (i : localI L V₁ V₂) x,
        e (seedRepresentation s i x) = BinaryPermutation.coreRepresentation (Fin 3)
          (q.localEquiv (QuotientGroup.mk' (pCore 2 (localI L V₁ V₂)) i)) (e x) := by
  obtain ⟨e, he⟩ := exists_plane_equiv (markedRepresentation s q)
    (quotient_finrank s) (marked_cubic_fixedFree s q)
  refine ⟨e, ?_⟩
  intro i x
  rw [← markedRepresentation_projection s q i]
  exact he _ x

variable (d : LocalData H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂))

/-- Complete the given quotient marking with coordinates on the actual seed quotient. -/
def compatibleMarking : CompatibleMarking H V V₁ V₂ V₃
    (localI L V₁ V₂) (localResidual L V₂) d where
  localEquiv := q.localEquiv
  cubic_image := q.cubic_image
  inverter_image := q.inverter_image
  planeEquiv := (exists_coordinates s q).choose
  equivariant := by
    intro l b
    have h := (exists_coordinates s q).choose_spec
      (inclusion d.L2_le_I2 l) (seedClass V V₂ b)
    rw [seedRepresentation_mk] at h
    exact h

/-- The construction retains the supplied group coordinates exactly. -/
theorem compatibleMarking_localEquiv : (compatibleMarking s q d).localEquiv = q.localEquiv := by
  rfl

include s q in
/-- Existence of compatible seed coordinates is conditional only on the supplied
quotient marking and the actual earlier local data. -/
theorem nonempty_compatibleMarking : Nonempty (CompatibleMarking H V V₁ V₂ V₃
    (localI L V₁ V₂) (localResidual L V₂) d) := ⟨compatibleMarking s q d⟩

end
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking.SeedCoordinates
