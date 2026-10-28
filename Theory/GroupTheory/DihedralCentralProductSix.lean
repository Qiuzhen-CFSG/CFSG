module
public import Theory.GroupTheory.DihedralCentralProductSix.Model

/-!
# Marked recognition of a sixfold dihedral central product

Six generating hyperbolic pairs give a homomorphism from D₈⁶. The five specified
central identifications lie in its kernel. The explicit binary-coordinate
calculation in `Model` gives the quotient order 2¹³, so a target of that order
makes the induced surjection an isomorphism. This proves the exact kernel,
not just the isomorphism type, and preserves both generators of every factor.
Each factor is faithful because every nontrivial normal subgroup of D₈ meets
its central involution; a small eight-element certificate proves that fact.

This is the reusable recognition step for Aschbacher–Smith 16.1.5(9), p.1172.
The actual J₄ application and the rest of its centralizer are separate results.
-/

namespace DihedralCentralProductSix
open DihedralGroup
open scoped BigOperators

/-- The local relations for six orthogonal hyperbolic involution pairs. -/
public structure Relations {G : Type*} [Group G] (z : G) (u : Fin 6 → Bool → G) : Prop where
  central : z ∈ Subgroup.center G
  order : orderOf z = 2
  square : ∀ i b, u i b ^ 2 = 1
  twist : ∀ i, u i false * u i true = u i true * u i false * z
  commute : ∀ i j, i ≠ j → ∀ a b, Commute (u i a) (u j b)

variable {G : Type*} [Group G] {z : G} {u : Fin 6 → Bool → G}

public theorem Relations.z_square (h : Relations z u) : z ^ 2 = 1 :=
  h.order ▸ pow_orderOf_eq_one z

public theorem Relations.z_ne_one (h : Relations z u) : z ≠ 1 := by
  intro he
  have ho := h.order
  simp [he] at ho

/-- The ith marked dihedral factor map. -/
public noncomputable def factorMap (h : Relations z u) (i : Fin 6) : DihedralGroup 4 →* G :=
  pairMap (u i false) (u i true) z (h.square i false) (h.square i true)
    h.z_square (h.twist i)

@[simp] public theorem factorMap_r_one (h : Relations z u) (i : Fin 6) :
    factorMap h i (.r 1) = u i false * u i true := pairMap_r_one ..
@[simp] public theorem factorMap_sr_zero (h : Relations z u) (i : Fin 6) :
    factorMap h i (.sr 0) = u i false := pairMap_sr_zero ..
@[simp] public theorem factorMap_r_two (h : Relations z u) (i : Fin 6) :
    factorMap h i (.r 2) = z := pairMap_r_two ..

@[simp] public theorem factorMap_sr_one (h : Relations z u) (i : Fin 6) :
    factorMap h i (.sr 1) = u i true := by
  change pairMap _ _ _ _ _ _ _ (.sr 1) = _
  rw [pairMap_sr]
  rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]
  rw [← mul_assoc, ← pow_two, h.square, one_mul]

public theorem factorMap_commute (h : Relations z u) :
    Pairwise fun i j => ∀ x y, Commute (factorMap h i x) (factorMap h j y) := by
  intro i j hij x y
  exact pairMap_commute (u i false) (u i true) z
    (h.square i false) (h.square i true) h.z_square (h.twist i)
    (u j false) (u j true) (h.square j false) (h.square j true) (h.twist j)
    (h.commute i j hij false false) (h.commute i j hij false true)
    (h.commute i j hij true false) (h.commute i j hij true true) x y

/-- The map from the concrete direct product, with all six markings fixed. -/
public noncomputable def phi (h : Relations z u) : D →* G :=
  MonoidHom.noncommPiCoprod (factorMap h) (factorMap_commute h)

@[simp] public theorem phi_single (h : Relations z u) (i : Fin 6) (x : DihedralGroup 4) :
    phi h (Pi.mulSingle i x) = factorMap h i x :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

@[simp] public theorem phi_r_one (h : Relations z u) (i : Fin 6) :
    phi h (Pi.mulSingle i (.r 1)) = u i false * u i true := by simp
@[simp] public theorem phi_sr_zero (h : Relations z u) (i : Fin 6) :
    phi h (Pi.mulSingle i (.sr 0)) = u i false := by simp
@[simp] public theorem phi_r_two (h : Relations z u) (i : Fin 6) :
    phi h (Pi.mulSingle i (.r 2)) = z := by simp

public theorem phi_surjective (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤) :
    Function.Surjective (phi h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, b⟩, rfl⟩
  cases b
  · exact ⟨Pi.mulSingle i (.sr 0), phi_sr_zero h i⟩
  · exact ⟨Pi.mulSingle i (.sr 1), by simp⟩

public theorem Delta_le_ker (h : Relations z u) : Delta ≤ (phi h).ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change phi h (c 0 * c i.succ) = 1
  simpa [c, ← pow_two] using h.z_square

/-- The homomorphism out of the explicit central-product quotient. -/
public noncomputable def quotientMap (h : Relations z u) : Model →* G :=
  QuotientGroup.lift Delta (phi h) (Delta_le_ker h)

@[simp] public theorem quotientMap_mk (h : Relations z u) (x : D) :
    quotientMap h (QuotientGroup.mk x) = phi h x := by
  rfl

public theorem quotientMap_surjective (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤) :
    Function.Surjective (quotientMap h) := by
  intro g
  obtain ⟨x, hx⟩ := phi_surjective h hgen g
  exact ⟨QuotientGroup.mk x, hx⟩

/-- The actual equivalence, retaining the specified maps on the six factors. -/
public noncomputable def recognition [Finite G] (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤)
    (hcard : Nat.card G = 2 ^ 13) : Model ≃* G :=
  MulEquiv.ofBijective (quotientMap h)
    ((quotientMap_surjective h hgen).bijective_of_nat_card_le (by rw [Model_card, hcard]))

@[simp] public theorem recognition_mk [Finite G] (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤)
    (hcard : Nat.card G = 2 ^ 13) (x : D) :
    recognition h hgen hcard (QuotientGroup.mk x) = phi h x := by rfl

public theorem ker_phi [Finite G] (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤)
    (hcard : Nat.card G = 2 ^ 13) : (phi h).ker = Delta := by
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply (recognition h hgen hcard).injective
    have hx' : phi h x = 1 := hx
    simpa only [recognition_mk, map_one] using hx'
  · exact Delta_le_ker h

/-- An explicit description of every overlap in the marked map's kernel. -/
public theorem phi_eq_one_iff [Finite G] (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤)
    (hcard : Nat.card G = 2 ^ 13) (x : D) : phi h x = 1 ↔
      ∃ v : Fin 5 → Bit, x 0 = bit (∏ i, v i) ∧ ∀ i, x i.succ = bit (v i) := by
  change x ∈ (phi h).ker ↔ _
  rw [ker_phi h hgen hcard, mem_Delta_iff]

/-- A D₈ map which retains the central involution is faithful. -/
public theorem injective_of_r_two_ne_one (f : DihedralGroup 4 →* G)
    (hf : f (.r 2) ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  have hx' : f x = 1 := hx
  have cases8 : ∀ x : DihedralGroup 4,
      x = 1 ∨ x = .r 2 ∨ x ^ 2 = .r 2 ∨
        x * .r 1 * x⁻¹ * (.r 1)⁻¹ = .r 2 := by decide
  rcases cases8 x with h1 | h2 | h2 | hc
  · exact h1
  · exact (hf (h2 ▸ hx')).elim
  · have hh := congrArg f h2
    rw [map_pow, hx', one_pow] at hh
    exact (hf hh.symm).elim
  · have hh := congrArg f hc
    simp only [map_mul, map_inv, hx', one_mul, inv_one, mul_one, mul_inv_cancel] at hh
    exact (hf hh.symm).elim

public theorem factorMap_injective (h : Relations z u) (i : Fin 6) :
    Function.Injective (factorMap h i) :=
  injective_of_r_two_ne_one _ (by rw [factorMap_r_two]; exact h.z_ne_one)

@[simp] public theorem recognition_r_one [Finite G] (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤)
    (hcard : Nat.card G = 2 ^ 13) (i : Fin 6) :
    recognition h hgen hcard (QuotientGroup.mk (Pi.mulSingle i (.r 1))) =
      u i false * u i true := by simp

@[simp] public theorem recognition_sr_zero [Finite G] (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤)
    (hcard : Nat.card G = 2 ^ 13) (i : Fin 6) :
    recognition h hgen hcard (QuotientGroup.mk (Pi.mulSingle i (.sr 0))) = u i false := by simp

@[simp] public theorem recognition_r_two [Finite G] (h : Relations z u)
    (hgen : Subgroup.closure (Set.range (fun p : Fin 6 × Bool => u p.1 p.2)) = ⊤)
    (hcard : Nat.card G = 2 ^ 13) (i : Fin 6) :
    recognition h hgen hcard (QuotientGroup.mk (Pi.mulSingle i (.r 2))) = z := by simp

end DihedralCentralProductSix
