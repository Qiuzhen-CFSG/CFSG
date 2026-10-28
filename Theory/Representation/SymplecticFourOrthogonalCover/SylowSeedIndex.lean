module
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticSeed
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Elementary actors on a normalized full Sylow seed

The natural fixed space of a full symplectic Sylow is a field line.
An involution with trivial field twist preserving this line fixes it
pointwise. It consequently lies in the actual symplectic component, and
fixed-point lifting fixes the full cover seed, including its central kernel.
Thus the action on the seed factors through the field automorphism group.

This supplies the first star comparison in MS93 (3.4), p.868, directly from
its elementary endpoint intersection, without a quadraticity assumption on
the entire vertex module.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover
variable {F G W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The kernel of the actual field-twist homomorphism fixes the complete
normalized Sylow cover seed for an actor of exponent two. -/
theorem exists_twist_fixing_sylow_seed
    (hF : 2 < Nat.card F) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (e : B ≃* L (K := F))
    (ρ : Representation (ZMod 2) G W)
    (τ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ v, τ (b : G) v = binaryNatural (e b) v)
    (p : Representation.IntertwiningMap (ρ.comp (B.subtype.comp e.symm.toMonoidHom))
      (binaryNatural (K := F))) (hp : IsCover p)
    (hproj : ∀ g w, p (ρ g w) = τ g (p w))
    (hsemi : ∀ g, ∃ σ : F ≃+* F, ∀ c v, τ g (c • v) = σ c • τ g v)
    (P : Sylow 2 (L (K := F))) (A : Subgroup G)
    (hsquare : ∀ a ∈ A, a * a = 1)
    (hn : ∀ a ∈ A, ∀ w ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
      (P : Subgroup (L (K := F))).subtype),
      ρ a w ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
        (P : Subgroup (L (K := F))).subtype)) :
    ∃ ξ : A →* (F ≃+* F), ∀ a : A, ξ a = 1 →
      ∀ w ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
        (P : Subgroup (L (K := F))).subtype), ρ (a : G) w = w := by
  classical
  choose key hk using fun a : A => hsemi (a : G)
  have unique (a : A) (σ κ : F ≃+* F)
      (hσ : ∀ c v, τ (a : G) (c • v) = σ c • τ (a : G) v)
      (hκ : ∀ c v, τ (a : G) (c • v) = κ c • τ (a : G) v) : σ = κ := by
    obtain ⟨v,hv⟩ := exists_ne (0 : Vector F)
    have hav : τ (a : G) v ≠ 0 := by
      intro hh
      apply hv
      exact (τ.apply_bijective (a : G)).injective (hh.trans (map_zero _).symm)
    apply RingEquiv.ext
    intro c
    exact (smul_left_injective F hav) ((hσ c v).symm.trans (hκ c v))
  let ξ : A →* (F ≃+* F) :=
    { toFun := key
      map_one' := unique 1 (key 1) 1 (hk 1) (by intro c v; simp)
      map_mul' := fun a b => unique (a*b) (key (a*b)) (key a * key b) (hk (a*b)) (by
        intro c v
        change τ ((a : G)*(b : G)) (c • v) = key a (key b c) • τ ((a : G)*(b : G)) v
        rw [map_mul]
        change τ (a : G) (τ (b : G) (c • v)) = key a (key b c) • τ (a : G) (τ (b : G) v)
        rw [hk b,hk a]) }
  refine ⟨ξ,?_⟩
  intro a ha w hw
  have hlin (c : F) (v : Vector F) : τ (a : G) (c • v) = c • τ (a : G) v := by
    have he : key a = 1 := ha
    have hh := hk a c v
    rw [he] at hh
    exact hh
  obtain ⟨g,hg⟩ := SylowFlag.exists_marking P
  let N := SylowFlag.movedLine g
  have hdim : Module.finrank F N = 1 := SylowFlag.movedLine_finrank g
  have hN : fixed ((binaryNatural (K := F)).comp (P : Subgroup (L (K := F))).subtype) =
      N.restrictScalars (ZMod 2) := by
    rw [hg]
    ext v
    change (∀ a : SylowFlag.movedSylow g, binaryNatural a.val v=v) ↔ v ∈ N
    exact SetLike.ext_iff.mp (SylowFlag.movedLine_fixed g) v
  have hNb : N ≠ ⊥ := by intro hh; rw [hh] at hdim; simp at hdim
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNb
  have hspan : N = F ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hv0
  have hvfix : τ (a : G) v ∈ N := by
    obtain ⟨u,hu⟩ := hp.1 v
    have hufix : u ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
        (P : Subgroup (L (K := F))).subtype) := by
      rw [cover_fixed_preimage p hp,hN]
      change p u ∈ N
      rwa [hu]
    have hh := hn a a.property u hufix
    rw [cover_fixed_preimage p hp,hN] at hh
    change p (ρ (a : G) u) ∈ N at hh
    rwa [hproj,hu] at hh
  rw [hspan] at hvfix
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hvfix
  have hinv : τ (a : G) (τ (a : G) v) = v := by
    rw [←Module.End.mul_apply,←map_mul,hsquare a a.property,map_one]
    rfl
  have hr2 : r*r = 1 := by
    apply smul_left_injective F hv0
    change (r*r) • v = (1 : F) • v
    rw [mul_smul,one_smul,hr,←hlin,hr]
    exact hinv
  have hr1 : r = 1 := by
    have hz : (r-1)^2 = 0 := by
      rw [sub_sq,pow_two,hr2]
      simp only [show (2 : F)=0 from CharP.cast_eq_zero F 2,zero_mul,sub_zero,one_pow]
      simpa only [one_add_one_eq_two] using (show (2 : F)=0 from CharP.cast_eq_zero F 2)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hfix (c : F) : τ (a : G) (c • v) = c • v := by
    rw [hlin,←hr,hr1,one_smul]
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans Subgroup.topEquiv
  have haB : (a : G) ∈ B :=
    SymplecticNaturalNormalizer.mem_component_of_fixes_field_line B hcent hF
      (e.trans d) τ hB a v hv0 hfix
  have hpw : p w ∈ N := by
    rw [cover_fixed_preimage p hp,hN] at hw
    exact hw
  rw [hspan] at hpw
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hpw
  have hpf : binaryNatural (e ⟨a,haB⟩) (p w) = p w := by
    rw [←hB ⟨a,haB⟩,←hc,hfix]
  have hh := cover_fixed_of_projection_fixed p hp (e ⟨a,haB⟩) w hpf
  change ρ (e.symm (e ⟨a,haB⟩)) w = w at hh
  simpa only [e.symm_apply_apply] using hh

end Representation.SymplecticFourOrthogonalCover
