module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Complement
public import Mathlib.Data.Fintype.Prod

/-!
# Factor sets for extensions with abelian kernel

A normalized section of an extension produces a factor set. Its crossed
multiplication on the product of the kernel and quotient reconstructs the
original group. Changing a factor set by a normalized one-cochain gives an
explicit multiplicative equivalence preserving the kernel and quotient.

These elementary extension constructions support the independent finite
extension step in Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
They assert no classification of factor sets or comparison with a permutation
model. The results are stated for arbitrary abelian kernels and quotients.
-/

@[expose] public section

namespace Theory.GroupTheory.AbelianExtension

universe u v w
variable {N : Type u} {Q : Type v} [CommGroup N] [Group Q]

structure FactorSet (α : Q →* MulAut N) where
  toFun : Q → Q → N
  one_left : ∀ q, toFun 1 q = 1
  one_right : ∀ q, toFun q 1 = 1
  cocycle : ∀ q r s, toFun q r * toFun (q * r) s =
    α q (toFun r s) * toFun q (r * s)

namespace FactorSet
variable {α : Q →* MulAut N} (c : FactorSet α)

@[ext] structure Extension (c : FactorSet α) where
  vector : N
  quotient : Q
deriving DecidableEq

/-- The crossed product retains the underlying product of sets. -/
def equivProd : c.Extension ≃ N × Q where
  toFun x := (x.vector, x.quotient)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite N] [Finite Q] : Finite c.Extension :=
  Finite.of_equiv (N × Q) c.equivProd.symm

instance [Fintype N] [Fintype Q] : Fintype c.Extension :=
  Fintype.ofEquiv (N × Q) c.equivProd.symm

instance : One c.Extension := ⟨⟨1, 1⟩⟩
instance : Mul c.Extension := ⟨fun x y =>
  ⟨x.vector * α x.quotient y.vector * c.toFun x.quotient y.quotient,
    x.quotient * y.quotient⟩⟩
instance : Inv c.Extension := ⟨fun x =>
  ⟨(α x.quotient⁻¹ x.vector * c.toFun x.quotient⁻¹ x.quotient)⁻¹,
    x.quotient⁻¹⟩⟩

instance : Group c.Extension where
  mul_assoc x y z := by
    apply Extension.ext
    · change (x.vector * α x.quotient y.vector * c.toFun x.quotient y.quotient) *
        α (x.quotient * y.quotient) z.vector *
        c.toFun (x.quotient * y.quotient) z.quotient =
        x.vector * α x.quotient
          (y.vector * α y.quotient z.vector * c.toFun y.quotient z.quotient) *
        c.toFun x.quotient (y.quotient * z.quotient)
      simp only [map_mul, MulAut.mul_apply]
      calc
        _ = (x.vector * α x.quotient y.vector * α x.quotient (α y.quotient z.vector)) *
            (c.toFun x.quotient y.quotient *
              c.toFun (x.quotient * y.quotient) z.quotient) := by ac_rfl
        _ = _ := by rw [c.cocycle]; ac_rfl
    · exact mul_assoc _ _ _
  one_mul x := by
    apply Extension.ext
    · change 1 * α 1 x.vector * c.toFun 1 x.quotient = x.vector
      simp [c.one_left]
    · exact one_mul _
  mul_one x := by
    apply Extension.ext
    · change x.vector * α x.quotient 1 * c.toFun x.quotient 1 = x.vector
      simp [c.one_right]
    · exact mul_one _
  inv_mul_cancel x := by
    apply Extension.ext
    · change (α x.quotient⁻¹ x.vector * c.toFun x.quotient⁻¹ x.quotient)⁻¹ *
        α x.quotient⁻¹ x.vector * c.toFun x.quotient⁻¹ x.quotient = 1
      group
    · exact inv_mul_cancel _

def inl : N →* c.Extension where
  toFun n := ⟨n, 1⟩
  map_one' := rfl
  map_mul' n m := by
    apply Extension.ext
    · change n * m = n * α 1 m * c.toFun 1 1
      simp [c.one_left]
    · exact (one_mul 1).symm

def projection : c.Extension →* Q where
  toFun := Extension.quotient
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inl_injective : Function.Injective c.inl :=
  fun _ _ h => congrArg Extension.vector h

theorem range_inl_eq_ker : c.inl.range = c.projection.ker := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    rfl
  · intro hx
    exact ⟨x.vector, Extension.ext rfl hx.symm⟩

def groupExtension : GroupExtension N c.Extension Q where
  inl := c.inl
  rightHom := c.projection
  inl_injective := c.inl_injective
  range_inl_eq_ker_rightHom := c.range_inl_eq_ker
  rightHom_surjective q := ⟨⟨1, q⟩, rfl⟩

def trivial (α : Q →* MulAut N) : FactorSet α where
  toFun _ _ := 1
  one_left _ := rfl
  one_right _ := rfl
  cocycle _ _ _ := by simp

def Equivalent (c d : FactorSet α) : Prop :=
  ∃ b : Q → N, b 1 = 1 ∧ ∀ q r,
    c.toFun q r * b (q * r) = b q * α q (b r) * d.toFun q r

/-- A factor set is cohomologous to itself by the constant identity cochain. -/
theorem equivalent_refl : c.Equivalent c := by
  exact ⟨fun _ => 1, rfl, fun _ _ => by simp⟩

/-- Cochain corrections compose by pointwise multiplication. -/
theorem Equivalent.trans {c d e : FactorSet α}
    (hcd : c.Equivalent d) (hde : d.Equivalent e) : c.Equivalent e := by
  obtain ⟨b, hb, hbd⟩ := hcd
  obtain ⟨a, ha, hae⟩ := hde
  refine ⟨fun q => b q * a q, by dsimp only; rw [hb, ha, mul_one], fun q r => ?_⟩
  dsimp only
  calc
    c.toFun q r * (b (q * r) * a (q * r)) =
        (c.toFun q r * b (q * r)) * a (q * r) := (mul_assoc _ _ _).symm
    _ = (b q * α q (b r)) * (d.toFun q r * a (q * r)) := by rw [hbd]; ac_rfl
    _ = _ := by rw [hae, map_mul]; ac_rfl

/-- Inverting a correction reverses its equivalence. -/
theorem Equivalent.symm {c d : FactorSet α} (hcd : c.Equivalent d) : d.Equivalent c := by
  obtain ⟨b, hb, h⟩ := hcd
  refine ⟨fun q => (b q)⁻¹, by dsimp only; rw [hb, inv_one], fun q r => ?_⟩
  dsimp only
  have hh := h q r
  rw [map_inv]
  calc
    d.toFun q r * (b (q * r))⁻¹ =
        ((b q)⁻¹ * b q) * ((α q (b r))⁻¹ * α q (b r)) *
          d.toFun q r * (b (q * r))⁻¹ := by simp
    _ =
        (b q)⁻¹ * (α q (b r))⁻¹ *
          (b q * α q (b r) * d.toFun q r) * (b (q * r))⁻¹ := by ac_rfl
    _ = _ := by rw [← hh]; group

def equivalenceOfCorrection (d : FactorSet α) (b : Q → N) (_hb : b 1 = 1)
    (h : ∀ q r, c.toFun q r * b (q * r) = b q * α q (b r) * d.toFun q r) :
    c.Extension ≃* d.Extension where
  toFun x := ⟨x.vector * b x.quotient, x.quotient⟩
  invFun x := ⟨x.vector * (b x.quotient)⁻¹, x.quotient⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    apply Extension.ext
    · change (x.vector * α x.quotient y.vector * c.toFun x.quotient y.quotient) *
        b (x.quotient * y.quotient) =
        (x.vector * b x.quotient) * α x.quotient (y.vector * b y.quotient) *
          d.toFun x.quotient y.quotient
      rw [mul_assoc (x.vector * α x.quotient y.vector), h, map_mul]
      ac_rfl
    · rfl

theorem equivalenceOfCorrection_inl (d : FactorSet α) (b : Q → N) (hb : b 1 = 1)
    (h : ∀ q r, c.toFun q r * b (q * r) = b q * α q (b r) * d.toFun q r) (n : N) :
    c.equivalenceOfCorrection d b hb h (c.inl n) = d.inl n := by
  apply Extension.ext
  · change n * b 1 = n
    rw [hb, mul_one]
  · rfl

/-- A cochain correction leaves the quotient coordinate unchanged. -/
theorem equivalenceOfCorrection_projection (d : FactorSet α) (b : Q → N)
    (hb : b 1 = 1)
    (h : ∀ q r, c.toFun q r * b (q * r) = b q * α q (b r) * d.toFun q r)
    (x : c.Extension) :
    d.projection (c.equivalenceOfCorrection d b hb h x) = c.projection x := rfl

/-- The trivial factor set has the evident homomorphic section. -/
def trivialSection (α : Q →* MulAut N) : Q →* (trivial α).Extension where
  toFun q := ⟨1, q⟩
  map_one' := rfl
  map_mul' q r := by
    apply Extension.ext
    · change 1 = 1 * α q 1 * 1
      simp
    · rfl

/-- A factor set cohomologous to the trivial one has a homomorphic section. -/
theorem exists_section_of_equivalent_trivial (h : c.Equivalent (trivial α)) :
    ∃ s : Q →* c.Extension, ∀ q, c.projection (s q) = q := by
  obtain ⟨b, hb, h⟩ := h
  let e := c.equivalenceOfCorrection (trivial α) b hb h
  refine ⟨e.symm.toMonoidHom.comp (trivialSection α), fun q => ?_⟩
  exact congrArg Extension.quotient (e.apply_symm_apply (trivialSection α q))

/-- A homomorphic section trivializes the factor set by its inverse vector
coordinate. The quotient coordinate must be the specified projection. -/
theorem equivalent_trivial_of_section
    (s : Q →* c.Extension) (hs : ∀ q, c.projection (s q) = q) :
    c.Equivalent (trivial α) := by
  refine ⟨fun q => (s q).vector⁻¹, ?_, ?_⟩
  · change (s 1).vector⁻¹ = 1
    rw [map_one]
    exact inv_one
  · intro q r
    have hmul := congrArg Extension.vector (s.map_mul q r)
    change (s (q * r)).vector =
      (s q).vector * α (s q).quotient (s r).vector *
        c.toFun (s q).quotient (s r).quotient at hmul
    have hq : (s q).quotient = q := hs q
    have hr : (s r).quotient = r := hs r
    rw [hq, hr] at hmul
    change c.toFun q r * (s (q * r)).vector⁻¹ =
      (s q).vector⁻¹ * α q ((s r).vector⁻¹) * 1
    rw [hmul, map_inv]
    group
    exact mul_comm _ _

end FactorSet

/-- A homomorphic section complements the kernel of its projection. -/
theorem isComplement_ker_range_of_section {E : Type w} [Group E]
    (p : E →* Q) (s : Q →* E) (hs : ∀ q, p (s q) = q) :
    p.ker.IsComplement' s.range := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have hy : y = y' := by
      apply Subtype.ext
      obtain ⟨q, hq⟩ := y.property
      obtain ⟨r, hr⟩ := y'.property
      have hp := congrArg p h
      have hx : p x = 1 := x.property
      have hx' : p x' = 1 := x'.property
      have hqr : q = r := by
        simpa only [map_mul, hx, hx', one_mul, ← hq, ← hr, hs] using hp
      exact hq.symm.trans (hqr ▸ hr)
    subst y'
    exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
  · intro e
    refine ⟨(⟨e * (s (p e))⁻¹, ?_⟩, ⟨s (p e), ⟨p e, rfl⟩⟩), ?_⟩
    · change p (e * (s (p e))⁻¹) = 1
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    · exact inv_mul_cancel_right _ _

/-- Triviality of a factor set gives a complement to its specified kernel. -/
theorem FactorSet.exists_complement_of_equivalent_trivial {α : Q →* MulAut N}
    (c : FactorSet α) (h : c.Equivalent (FactorSet.trivial α)) :
    ∃ K : Subgroup c.Extension, c.projection.ker.IsComplement' K := by
  obtain ⟨s, hs⟩ := c.exists_section_of_equivalent_trivial h
  exact ⟨s.range, isComplement_ker_range_of_section c.projection s hs⟩

/-- Restricting a surjective homomorphism to a complement of its kernel is an
isomorphism, whose inverse gives a homomorphic section. -/
theorem exists_section_of_isComplement_ker {E : Type w} [Group E]
    (p : E →* Q) (hp : Function.Surjective p)
    (K : Subgroup E) (hK : p.ker.IsComplement' K) :
    ∃ s : Q →* E, ∀ q, p (s q) = q := by
  let f : K →* Q := p.comp K.subtype
  have hf : Function.Bijective f := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro k hk
      have hk' : (k : E) ∈ p.ker ⊓ K := ⟨hk, k.property⟩
      have h1 : (k : E) = 1 := by
        simpa only [hK.disjoint.eq_bot, Subgroup.mem_bot] using hk'
      exact Subtype.ext h1
    · intro q
      obtain ⟨e, rfl⟩ := hp q
      obtain ⟨⟨n, k⟩, rfl⟩ := hK.2 e
      exact ⟨k, by change p k = p (n * k); rw [map_mul, n.property, one_mul]⟩
  let e := MulEquiv.ofBijective f hf
  refine ⟨K.subtype.comp e.symm.toMonoidHom, ?_⟩
  intro q
  exact e.apply_symm_apply q

/-- A factor set is trivial exactly when its specified kernel has a complement. -/
theorem FactorSet.equivalent_trivial_iff_exists_complement {α : Q →* MulAut N}
    (c : FactorSet α) :
    c.Equivalent (FactorSet.trivial α) ↔
      ∃ K : Subgroup c.Extension, c.projection.ker.IsComplement' K := by
  constructor
  · exact c.exists_complement_of_equivalent_trivial
  · rintro ⟨K, hK⟩
    obtain ⟨s, hs⟩ := exists_section_of_isComplement_ker c.projection
      c.groupExtension.rightHom_surjective K hK
    exact c.equivalent_trivial_of_section s hs

variable {E : Type w} [Group E] (S : GroupExtension N E Q)

noncomputable def normalizedSection : S.Section := by
  classical
  exact {
    toFun := fun q => if q = 1 then 1 else S.surjInvRightHom q
    rightInverse_rightHom := fun q => by
      dsimp
      split_ifs with h
      · simp [h]
      · exact S.surjInvRightHom.rightHom_section q }

theorem normalizedSection_one : (normalizedSection S) 1 = 1 := by
  simp [normalizedSection]

noncomputable def sectionDefect (σ : S.Section) (q r : Q) : N :=
  (MonoidHom.ofInjective S.inl_injective).symm
    ⟨σ q * σ r * (σ (q * r))⁻¹, σ.mul_mul_mul_inv_mem_range_inl q r⟩

theorem inl_sectionDefect (σ : S.Section) (q r : Q) :
    S.inl ((sectionDefect S) σ q r) = σ q * σ r * (σ (q * r))⁻¹ := by
  exact MonoidHom.apply_ofInjective_symm _ _

noncomputable def sectionFactorSet (α : Q →* MulAut N)
    (hact : ∀ (e : E) (n : N), S.inl (α (S.rightHom e) n) = e * S.inl n * e⁻¹)
    (σ : S.Section) (hσ : σ 1 = 1) : FactorSet α where
  toFun := (sectionDefect S) σ
  one_left q := by
    apply S.inl_injective
    rw [(inl_sectionDefect S), hσ, one_mul, one_mul, mul_inv_cancel, map_one]
  one_right q := by
    apply S.inl_injective
    rw [(inl_sectionDefect S), hσ, mul_one, mul_one, mul_inv_cancel, map_one]
  cocycle q r s := by
    apply S.inl_injective
    simp only [map_mul, (inl_sectionDefect S)]
    rw [show S.inl (α q ((sectionDefect S) σ r s)) =
      σ q * S.inl ((sectionDefect S) σ r s) * (σ q)⁻¹ from
        by simpa only [σ.rightHom_section] using hact (σ q) ((sectionDefect S) σ r s)]
    rw [(inl_sectionDefect S), mul_assoc q r s]
    group

def sectionEval (σ : S.Section) : N × Q → E := fun x => S.inl x.1 * σ x.2

theorem sectionEval_bijective (σ : S.Section) : Function.Bijective ((sectionEval S) σ) := by
  constructor
  · rintro ⟨n, q⟩ ⟨m, r⟩ h
    have hq : q = r := by
      have hp := congrArg S.rightHom h
      simpa only [sectionEval, map_mul, S.rightHom_inl, σ.rightHom_section, one_mul] using hp
    subst r
    exact Prod.ext (S.inl_injective (mul_right_cancel h)) rfl
  · intro e
    have hm : e * (σ (S.rightHom e))⁻¹ ∈ S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
        σ.rightHom_section, mul_inv_cancel]
    obtain ⟨n, hn⟩ := hm
    exact ⟨(n, S.rightHom e), by simp only [sectionEval, hn, inv_mul_cancel_right]⟩

noncomputable def sectionEquiv (α : Q →* MulAut N)
    (hact : ∀ (e : E) (n : N), S.inl (α (S.rightHom e) n) = e * S.inl n * e⁻¹)
    (σ : S.Section) (hσ : σ 1 = 1) : ((sectionFactorSet S) α hact σ hσ).Extension ≃* E := by
  let f : ((sectionFactorSet S) α hact σ hσ).Extension →* E :=
    { toFun := fun x => S.inl x.vector * σ x.quotient
      map_one' := by change S.inl 1 * σ 1 = 1; rw [map_one, hσ, one_mul]
      map_mul' := fun x y => by
        change S.inl (x.vector * α x.quotient y.vector * (sectionDefect S) σ x.quotient y.quotient) *
          σ (x.quotient * y.quotient) =
          (S.inl x.vector * σ x.quotient) * (S.inl y.vector * σ y.quotient)
        simp only [map_mul, (inl_sectionDefect S)]
        rw [show S.inl (α x.quotient y.vector) =
          σ x.quotient * S.inl y.vector * (σ x.quotient)⁻¹ from
            by simpa only [σ.rightHom_section] using hact (σ x.quotient) y.vector]
        group }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    have hp := ((sectionEval_bijective S) σ).injective
      (show (sectionEval S) σ (x.vector, x.quotient) = (sectionEval S) σ (y.vector, y.quotient) from h)
    exact FactorSet.Extension.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)
  · intro e
    obtain ⟨⟨n, q⟩, h⟩ := ((sectionEval_bijective S) σ).surjective e
    exact ⟨⟨n, q⟩, h⟩

/-- Reconstruction identifies the distinguished kernel inclusions. -/
theorem sectionEquiv_inl (α : Q →* MulAut N)
    (hact : ∀ (e : E) (n : N), S.inl (α (S.rightHom e) n) = e * S.inl n * e⁻¹)
    (σ : S.Section) (hσ : σ 1 = 1) (n : N) :
    sectionEquiv S α hact σ hσ ((sectionFactorSet S α hact σ hσ).inl n) = S.inl n := by
  change S.inl n * σ 1 = S.inl n
  rw [hσ, mul_one]

/-- Reconstruction also identifies the specified quotient maps. -/
theorem sectionEquiv_projection (α : Q →* MulAut N)
    (hact : ∀ (e : E) (n : N), S.inl (α (S.rightHom e) n) = e * S.inl n * e⁻¹)
    (σ : S.Section) (hσ : σ 1 = 1) (x : (sectionFactorSet S α hact σ hσ).Extension) :
    S.rightHom (sectionEquiv S α hact σ hσ x) = x.quotient := by
  change S.rightHom (S.inl x.vector * σ x.quotient) = x.quotient
  rw [map_mul, S.rightHom_inl, σ.rightHom_section, one_mul]

end Theory.GroupTheory.AbelianExtension
