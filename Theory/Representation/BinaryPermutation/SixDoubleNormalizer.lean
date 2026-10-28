module
public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer
public import Theory.Representation.BinaryAlternatingSixModels.Schur
public import Theory.Representation.BinaryPermutation.ThreeTensorDisplacement

/-!
# The full normalizer of two natural binary A₆ modules

A twisted intertwiner on two natural A₆ copies induces a natural S₆
automorphism, by the existing constituent normalizer theorem. After removing
that operator, the scalar commutant makes the four blocks binary scalars;
invertibility identifies their matrix with the natural S₃ action.
Consequently the ambient faithful action embeds in the actual S₆ × S₃
tensor action, retaining the original component marking and module coordinates.

The low-rank G.11.2 consumer uses this embedding to exclude the doubled A₆
branch. The tensor centralizer calculation follows the five-letter proof in
`FiveTensorNormalizer`, using the proved six-letter scalar commutant.
Source: Aschbacher--Smith G.11.7--8, printed pp.366--368.
-/

public section
open TensorProduct Representation Subgroup
namespace BinaryPermutation.SixDoubleNormalizer
open BinaryPermutation
private theorem pair_coefficients : ∀ a b c d : ZMod 2,
    (∀ x y : ZMod 2, a*x+b*y = 0 → c*x+d*y = 0 → x = 0 ∧ y = 0) →
    ∃ h : Equiv.Perm (Fin 3), ∀ n : Full (Fin 3), (∑ i, n i) = 0 →
      n (h.symm 0) = a * n 0 + b * n 1 ∧
      n (h.symm 1) = c * n 0 + d * n 1 := by
  decide +kernel

/-- The four blocks of an A₆-equivariant map on two copies are binary scalars. -/
private theorem pair_commuting_blocks
    (f : (natural (Fin 6) × natural (Fin 6)) →ₗ[ZMod 2] (natural (Fin 6) × natural (Fin 6)))
    (hf : ∀ (g : alternatingGroup (Fin 6)) (u v : natural (Fin 6)),
      f (alternatingNaturalRepresentation (Fin 6) g u,
        alternatingNaturalRepresentation (Fin 6) g v) =
      (alternatingNaturalRepresentation (Fin 6) g (f (u,v)).1,
        alternatingNaturalRepresentation (Fin 6) g (f (u,v)).2)) :
    ∃ a b c d : ZMod 2, ∀ u v, f (u,v) = (a • u + b • v, c • u + d • v) := by
  let p := LinearMap.fst (ZMod 2) (natural (Fin 6)) (natural (Fin 6))
  let q := LinearMap.snd (ZMod 2) (natural (Fin 6)) (natural (Fin 6))
  let i := LinearMap.inl (ZMod 2) (natural (Fin 6)) (natural (Fin 6))
  let j := LinearMap.inr (ZMod 2) (natural (Fin 6)) (natural (Fin 6))
  obtain ⟨a, ha⟩ := BinaryAlternatingSix.Schur.natural_commuting_scalar (p.comp (f.comp i)) (by
    intro g v
    simpa [p, i] using congrArg Prod.fst (hf g v 0))
  obtain ⟨b, hb⟩ := BinaryAlternatingSix.Schur.natural_commuting_scalar (p.comp (f.comp j)) (by
    intro g v
    simpa [p, j] using congrArg Prod.fst (hf g 0 v))
  obtain ⟨c, hc⟩ := BinaryAlternatingSix.Schur.natural_commuting_scalar (q.comp (f.comp i)) (by
    intro g v
    simpa [q, i] using congrArg Prod.snd (hf g v 0))
  obtain ⟨d, hd⟩ := BinaryAlternatingSix.Schur.natural_commuting_scalar (q.comp (f.comp j)) (by
    intro g v
    simpa [q, j] using congrArg Prod.snd (hf g 0 v))
  refine ⟨a, b, c, d, fun u v => ?_⟩
  have hadd : f (u,v) = f (u,0) + f (0,v) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using f.map_add (u,0) (0,v)
  rw [hadd]
  exact Prod.ext (congrArg₂ (· + ·) (ha u) (hb v))
    (congrArg₂ (· + ·) (hc u) (hd v))

/-- Every invertible map commuting with A₆ on the first tensor factor is a
three-point permutation on the second factor. -/
private theorem tensor_centralizer
    (f : (natural (Fin 6) ⊗[ZMod 2] core (Fin 3)) ≃ₗ[ZMod 2]
      (natural (Fin 6) ⊗[ZMod 2] core (Fin 3)))
    (hf : ∀ (g : alternatingGroup (Fin 6)) v,
      f (ThreeTensor.action (naturalRepresentation (Fin 6)) (g.val,1) v) =
        ThreeTensor.action (naturalRepresentation (Fin 6)) (g.val,1) (f v)) :
    ∃ h : Equiv.Perm (Fin 3), ∀ v,
      f v = ThreeTensor.action (naturalRepresentation (Fin 6)) (1,h) v := by
  let e := ThreeTensor.pairEquiv (V := natural (Fin 6))
  let F := e.symm.trans (f.trans e)
  have hF (g : alternatingGroup (Fin 6)) (u v : natural (Fin 6)) :
      F (alternatingNaturalRepresentation (Fin 6) g u,
        alternatingNaturalRepresentation (Fin 6) g v) =
      (alternatingNaturalRepresentation (Fin 6) g (F (u,v)).1,
        alternatingNaturalRepresentation (Fin 6) g (F (u,v)).2) := by
    have he := ThreeTensor.pairEquiv_equivariant (naturalRepresentation (Fin 6)) g.val
      (e.symm (u,v))
    change e (ThreeTensor.action (naturalRepresentation (Fin 6)) (g.val,1) (e.symm (u,v))) =
      ((naturalRepresentation (Fin 6)).prod (naturalRepresentation (Fin 6))) g.val
        (e (e.symm (u,v))) at he
    rw [e.apply_symm_apply] at he
    change e (ThreeTensor.action (naturalRepresentation (Fin 6)) (g.val,1) (e.symm (u,v))) =
      (alternatingNaturalRepresentation (Fin 6) g u,
        alternatingNaturalRepresentation (Fin 6) g v) at he
    change e (f (e.symm _)) = _
    rw [← he, e.symm_apply_apply, hf]
    exact ThreeTensor.pairEquiv_equivariant (naturalRepresentation (Fin 6)) g.val _
  obtain ⟨a,b,c,d,hblocks⟩ := pair_commuting_blocks F.toLinearMap hF
  change ∀ u v, F (u,v) = (a • u + b • v, c • u + d • v) at hblocks
  let : Nontrivial (natural (Fin 6)) := Module.nontrivial_of_finrank_pos (by
    rw [finrank_natural_even (Fin 6) (by decide)]; decide)
  obtain ⟨u,hu⟩ := exists_ne (0 : natural (Fin 6))
  have hker (x y : ZMod 2) (hxy : a*x+b*y = 0) (hxy' : c*x+d*y = 0) :
      x = 0 ∧ y = 0 := by
    have hh : F (x • u, y • u) = F 0 := by
      rw [hblocks, map_zero]
      simp only [smul_smul, ← add_smul, hxy, hxy', zero_smul, Prod.zero_eq_mk]
    have hzero := F.injective hh
    exact ⟨(smul_eq_zero.mp (congrArg Prod.fst hzero)).resolve_right hu,
      (smul_eq_zero.mp (congrArg Prod.snd hzero)).resolve_right hu⟩
  obtain ⟨h, hh⟩ := pair_coefficients a b c d hker
  refine ⟨h, fun v => ?_⟩
  apply e.injective
  have hFe (v) : e (f v) = F (e v) := by simp only [F, LinearEquiv.trans_apply,
    e.symm_apply_apply]
  rw [hFe]
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u n =>
    rw [ThreeTensor.action_tmul]
    simp only [map_one, Module.End.one_apply]
    change F (ThreeTensor.pairEquiv (u ⊗ₜ[ZMod 2] n)) =
      ThreeTensor.pairEquiv (u ⊗ₜ[ZMod 2] coreRepresentation (Fin 3) h n)
    rw [ThreeTensor.pairEquiv_tmul, ThreeTensor.pairEquiv_tmul]
    change F (n.val 0 • u, n.val 1 • u) =
      ((coreRepresentation (Fin 3) h n).val 0 • u,
        (coreRepresentation (Fin 3) h n).val 1 • u)
    rw [hblocks]
    obtain ⟨h0,h1⟩ := hh n.val n.property
    change (a • n.val 0 • u + b • n.val 1 • u,
      c • n.val 0 • u + d • n.val 1 • u) = (n.val (h.symm 0) • u, n.val (h.symm 1) • u)
    rw [h0, h1]
    simp only [smul_smul, add_smul]
  | add u v hu hv => simpa only [map_add] using congrArg₂ (· + ·) hu hv

theorem tensor_faithful :
    Function.Injective (ThreeTensor.action (naturalRepresentation (Fin 6))) := by
  let ρ := ThreeTensor.action (naturalRepresentation (Fin 6))
  apply (injective_iff_map_eq_one ρ).mpr
  intro g hg
  have hz : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) = 0 := by
    rw [show ρ g = LinearMap.id from hg,sub_self,LinearMap.range_zero]
    simp
  have h3 : g.2 = 1 := by
    by_contra h3
    have hh := ThreeTensor.dimension_le_displacement (naturalRepresentation (Fin 6)) g h3
    rw [show Module.finrank (ZMod 2) (natural (Fin 6)) = 4 from
      (by simpa using finrank_natural_even (Fin 6) (by decide))] at hh
    change 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) at hh
    omega
  have he : g = (g.1,1) := Prod.ext rfl h3
  rw [he,ThreeTensor.displacement_first] at hz
  have hr : Module.finrank (ZMod 2)
      (LinearMap.range (naturalRepresentation (Fin 6) g.1 - LinearMap.id)) = 0 := by omega
  have h1 : naturalRepresentation (Fin 6) g.1 = 1 :=
    sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hr))
  exact Prod.ext ((naturalRepresentation_injective (Fin 6) (by decide))
    (h1.trans (map_one _).symm)) h3

private theorem tensor_coordinates_unique (p q : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 3))
    (h : ∀ v, ThreeTensor.action (naturalRepresentation (Fin 6)) p v =
      ThreeTensor.action (naturalRepresentation (Fin 6)) q v) : p = q :=
  tensor_faithful (LinearMap.ext h)

/-- An automorphism normalizing the marked tensor A₆ action is a pair of
coordinate permutations. The given twisted intertwiner forces its A₆
automorphism into the natural S₆ subgroup; full equivariance is retained. -/
theorem tensor_normalizer
    (f : (natural (Fin 6) ⊗[ZMod 2] core (Fin 3)) ≃ₗ[ZMod 2]
      (natural (Fin 6) ⊗[ZMod 2] core (Fin 3)))
    (φ : MulAut (alternatingGroup (Fin 6)))
    (hf : ∀ (g : alternatingGroup (Fin 6)) v,
      f (ThreeTensor.action (naturalRepresentation (Fin 6)) (g.val,1) v) =
        ThreeTensor.action (naturalRepresentation (Fin 6)) ((φ g).val,1) (f v)) :
    ∃ p : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 3), ∀ v,
      f v = ThreeTensor.action (naturalRepresentation (Fin 6)) p v := by
  let ρ := ThreeTensor.action (naturalRepresentation (Fin 6))
  let e := ThreeTensor.pairEquiv (V := natural (Fin 6))
  have hn := Representation.BinaryAlternatingSixNaturalNormalizer.natural_of_pair_intertwiner
    φ (e.symm.trans (f.trans e)) (by
      intro g v
      have he := ThreeTensor.pairEquiv_equivariant (naturalRepresentation (Fin 6))
        g.val (e.symm v)
      rw [e.apply_symm_apply] at he
      change e (ThreeTensor.action (naturalRepresentation (Fin 6)) (g.val,1) (e.symm v)) =
        ((alternatingNaturalRepresentation (Fin 6)).prod
          (alternatingNaturalRepresentation (Fin 6))) g v at he
      change e (f (e.symm _)) = _
      rw [← he,e.symm_apply_apply,hf]
      exact ThreeTensor.pairEquiv_equivariant (naturalRepresentation (Fin 6)) (φ g).val _)
  obtain ⟨σ, hσ⟩ := hn
  let t : _ ≃ₗ[ZMod 2] _ := LinearEquiv.ofBijective (ρ (σ⁻¹,1)) (ρ.apply_bijective _)
  let F := f.trans t
  have hconj (g : alternatingGroup (Fin 6)) : (φ g).val = σ * g.val * σ⁻¹ := by
    exact congrArg (fun a : MulAut (alternatingGroup (Fin 6)) => (a g).val) hσ.symm
  have hF (g : alternatingGroup (Fin 6)) v :
      F (ρ (g.val,1) v) = ρ (g.val,1) (F v) := by
    change ρ (σ⁻¹,1) (f (ρ (g.val,1) v)) = ρ (g.val,1) (ρ (σ⁻¹,1) (f v))
    rw [hf, hconj]
    change ρ (σ⁻¹,1) (ρ (σ * g.val * σ⁻¹,1) (f v)) =
      ρ (g.val,1) (ρ (σ⁻¹,1) (f v))
    simp only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [mul_assoc, inv_mul_cancel_left]
  obtain ⟨h, hh⟩ := tensor_centralizer F hF
  refine ⟨(σ,h), fun v => ?_⟩
  have he := congrArg (ρ (σ,1)) (hh v)
  change ρ (σ,1) (ρ (σ⁻¹,1) (f v)) = ρ (σ,1) (ρ (1,h) v) at he
  simpa only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel,
    one_mul, mul_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply] using he

abbrev TensorSpace := natural (Fin 6) ⊗[ZMod 2] core (Fin 3)
abbrev TensorGroup := Equiv.Perm (Fin 6) × Equiv.Perm (Fin 3)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A faithful action whose restriction to a normal A₆ is two natural
copies embeds in the actual tensor normalizer, with the same coordinates. -/
theorem exists_tensor_embedding
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (H : Subgroup G) [H.Normal] (e : H ≃* alternatingGroup (Fin 6))
    (f : V ≃ₗ[ZMod 2] TensorSpace)
    (he : ∀ (h : H) v, f (ρ h v) =
      ThreeTensor.action (naturalRepresentation (Fin 6)) ((e h).val,1) (f v)) :
    ∃ j : G →* TensorGroup, Function.Injective j ∧
      (∀ g v, f (ρ g v) = ThreeTensor.action (naturalRepresentation (Fin 6)) (j g) (f v)) ∧
      ∀ h : H, j h = ((e h).val,1) := by
  classical
  let τ := ThreeTensor.action (naturalRepresentation (Fin 6))
  have exists_coordinates (g : G) : ∃ p : TensorGroup,
      ∀ v, f (ρ g v) = τ p (f v) := by
    let φ : MulAut (alternatingGroup (Fin 6)) :=
      e.symm.trans ((MulAut.conjNormal g).trans e)
    let t : TensorSpace ≃ₗ[ZMod 2] TensorSpace :=
      f.symm.trans ((LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)).trans f)
    have ht (a : alternatingGroup (Fin 6)) (w : TensorSpace) :
        t (τ (a.val,1) w) = τ ((φ a).val,1) (t w) := by
      obtain ⟨v,rfl⟩ := f.surjective w
      let h := e.symm a
      have hh : (e h).val = a.val := congrArg Subtype.val (e.apply_symm_apply a)
      change f (ρ g (f.symm (τ (a.val,1) (f v)))) = _
      rw [← hh, ← he h v, f.symm_apply_apply]
      have hc : e (MulAut.conjNormal g h) = φ a := rfl
      rw [show τ ((φ a).val,1) (t (f v)) =
          f (ρ (MulAut.conjNormal g h : H) (ρ g v)) by
        simpa only [t, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
          f.symm_apply_apply, hc] using (he (MulAut.conjNormal g h) (ρ g v)).symm]
      simp only [MulAut.conjNormal_apply, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    obtain ⟨p,hp⟩ := tensor_normalizer t φ ht
    exact ⟨p, fun v => by simpa only [t, LinearEquiv.trans_apply,
      LinearEquiv.ofBijective_apply, f.symm_apply_apply] using hp (f v)⟩
  choose p hp using exists_coordinates
  have unique (a b : TensorGroup) (hh : ∀ v, τ a (f v) = τ b (f v)) : a = b := by
    apply tensor_coordinates_unique
    intro w
    obtain ⟨v,rfl⟩ := f.surjective w
    exact hh v
  let j : G →* TensorGroup := {
    toFun := p
    map_one' := unique _ _ (fun v => by rw [← hp,map_one,map_one]; rfl)
    map_mul' := fun a b => unique _ _ (fun v => by
      rw [← hp,map_mul,Module.End.mul_apply,hp,hp,map_mul,Module.End.mul_apply]) }
  have hj (g : G) (v : V) : f (ρ g v) = τ (j g) (f v) := hp g v
  refine ⟨j,?_,hj,?_⟩
  · intro a b hab
    apply hf
    ext v
    apply f.injective
    rw [hj,hj,hab]
  · intro h
    apply unique
    intro v
    rw [← hj,he]

/-- Two constituent coordinates give the tensor coordinates used in the
normalizer theorem, retaining the component isomorphism. -/
theorem exists_tensor_embedding_of_double
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (H : Subgroup G) [H.Normal] (e : H ≃* alternatingGroup (Fin 6))
    (f : V ≃ₗ[ZMod 2] (natural (Fin 6) × natural (Fin 6)))
    (he : ∀ (h : H) v, f (ρ h v) =
      (alternatingNaturalRepresentation (Fin 6) (e h) (f v).1,
       alternatingNaturalRepresentation (Fin 6) (e h) (f v).2)) :
    ∃ j : G →* TensorGroup, ∃ t : V ≃ₗ[ZMod 2] TensorSpace,
      Function.Injective j ∧
      (∀ g v, t (ρ g v) = ThreeTensor.action (naturalRepresentation (Fin 6)) (j g) (t v)) ∧
      ∀ h : H, j h = ((e h).val,1) := by
  let t := f.trans ThreeTensor.pairEquiv.symm
  have ht (h : H) (v : V) : t (ρ h v) =
      ThreeTensor.action (naturalRepresentation (Fin 6)) ((e h).val,1) (t v) := by
    apply ThreeTensor.pairEquiv.injective
    change ThreeTensor.pairEquiv (ThreeTensor.pairEquiv.symm (f (ρ h v))) = _
    rw [ThreeTensor.pairEquiv.apply_symm_apply,ThreeTensor.pairEquiv_equivariant]
    dsimp only [t,LinearEquiv.trans_apply]
    rw [ThreeTensor.pairEquiv.apply_symm_apply]
    exact he h v
  obtain ⟨j,hj,hjt,hje⟩ := exists_tensor_embedding ρ hf H e t ht
  exact ⟨j,t,hj,hjt,hje⟩

end BinaryPermutation.SixDoubleNormalizer
