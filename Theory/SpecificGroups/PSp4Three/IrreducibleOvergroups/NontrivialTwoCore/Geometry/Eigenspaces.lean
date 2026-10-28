module

public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.LinearAlgebra.Projection

/-!
# Commuting involutions on small alternating spaces

The sign spaces of an involutory isometry are orthogonal and nondegenerate.
Their even dimensions force an involution on an alternating plane to be a
scalar sign. A nonscalar involution in dimension four splits the space into
two such planes; every commuting involution is determined by its two signs.
This gives the elementary-rank bound used for the two-core in Sp₄(3).

The eigenspace decomposition and restriction proofs are adapted from Gerald
Höhn, ATLAS, `Atlas/LinearAlgebra/InvolutionEigenspaces.lean` and
`Atlas/LinearAlgebra/InvolutionEigenspaceRestrictions.lean`, prerequisites of
`SymplecticInvolutionConjugacy.lean`. Covered adaptations retain the ATLAS
Research and Attribution License 1.0 (`LICENSES/ATLAS.txt`; citation:
`LICENSES/ATLAS-CITATION.cff`). Changes: CFSG module boundaries and namespace;
the plane and commuting-family bounds are added here.
-/

@[expose] public section

noncomputable section
namespace Matrix.PSp4Three.NontrivialTwoCore.Geometry.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

def plus (t : V →ₗ[F] V) : Submodule F V := LinearMap.ker (t - LinearMap.id)
def minus (t : V →ₗ[F] V) : Submodule F V := LinearMap.ker (t + LinearMap.id)

@[simp] theorem mem_plus (t : V →ₗ[F] V) (x : V) : x ∈ plus t ↔ t x = x := by
  simp [plus,LinearMap.mem_ker,sub_eq_zero]
@[simp] theorem mem_minus (t : V →ₗ[F] V) (x : V) : x ∈ minus t ↔ t x = -x := by
  simp [minus,LinearMap.mem_ker,add_eq_zero_iff_eq_neg]

theorem isCompl (t : V →ₗ[F] V) (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    IsCompl (plus t) (minus t) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    rw [mem_plus] at hx
    rw [mem_minus] at hy
    have he : x = -x := hx.symm.trans hy
    have hz : (2 : F) • x = 0 := by
      calc
        _ = x + x := two_smul F x
        _ = x + -x := congrArg (fun z => x + z) he
        _ = 0 := add_neg_cancel x
    exact (smul_eq_zero.mp hz).resolve_left h2
  · rw [codisjoint_iff,eq_top_iff]
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨(2 : F)⁻¹ • (x + t x), ?_, (2 : F)⁻¹ • (x - t x), ?_, ?_⟩
    · rw [mem_plus]
      simp only [map_smul,map_add,ht x]
      rw [add_comm]
    · rw [mem_minus]
      simp only [map_smul,map_sub,ht x]
      rw [← smul_neg, neg_sub]
    · rw [← smul_add]
      have he : (x + t x) + (x - t x) = (2 : F) • x := by rw [two_smul]; abel
      rw [he,smul_smul,inv_mul_cancel₀ h2,one_smul]

/-- Addition gives the actual direct-sum coordinates of the involution. -/
def decomposition (t : V →ₗ[F] V) (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    (plus t × minus t) ≃ₗ[F] V := Submodule.prodEquivOfIsCompl _ _ (isCompl t ht h2)

theorem orthogonal (b : LinearMap.BilinForm F V) (t : V →ₗ[F] V)
    (hb : ∀ x y, b (t x) (t y) = b x y) (h2 : (2 : F) ≠ 0)
    (x : plus t) (y : minus t) : b x.val y.val = 0 := by
  have hx := (mem_plus t x.val).mp x.prop
  have hy := (mem_minus t y.val).mp y.prop
  have he := hb x.val y.val
  rw [hx,hy,map_neg] at he
  have hz : (2 : F) * b x.val y.val = 0 := by
    rw [two_mul]
    exact (congrArg (fun z => b x.val y.val + z) he.symm).trans (add_neg_cancel _)
  exact (mul_eq_zero.mp hz).resolve_left h2

theorem decomposition_action (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (h2 : (2 : F) ≠ 0) (x : plus t × minus t) :
    t (decomposition t ht h2 x) = x.1.val - x.2.val := by
  change t (x.1.val + x.2.val) = _
  rw [map_add,(mem_plus _ _).mp x.1.prop,(mem_minus _ _).mp x.2.prop,sub_eq_add_neg]
end Matrix.PSp4Three.NontrivialTwoCore.Geometry.LinearInvolution

end
noncomputable section
namespace Matrix.PSp4Three.NontrivialTwoCore.Geometry.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private theorem restriction_nondegenerate (b : LinearMap.BilinForm F V)
    (hn : b.Nondegenerate) (P R : Submodule F V) (hc : IsCompl P R)
    (hpr : ∀ x : P, ∀ y : R, b x.val y.val = 0)
    (hrp : ∀ y : R, ∀ x : P, b y.val x.val = 0) :
    (b.restrict P).Nondegenerate := by
  let e := Submodule.prodEquivOfIsCompl P R hc
  constructor
  · intro x hx
    apply Subtype.ext
    apply hn.1 x.val
    intro z
    obtain ⟨⟨p,r⟩,rfl⟩ := e.surjective z
    change b x.val (p.val + r.val) = 0
    rw [map_add,hpr x r,add_zero]
    exact hx p
  · intro x hx
    apply Subtype.ext
    apply hn.2 x.val
    intro z
    obtain ⟨⟨p,r⟩,rfl⟩ := e.surjective z
    change b (p.val + r.val) x.val = 0
    rw [map_add,LinearMap.add_apply,hrp r x,add_zero]
    exact hx p

theorem plus_nondegenerate (b : LinearMap.BilinForm F V) (hn : b.Nondegenerate)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (hb : ∀ x y, b (t x) (t y) = b x y) (h2 : (2 : F) ≠ 0) :
    (b.restrict (plus t)).Nondegenerate :=
  restriction_nondegenerate b hn _ _ (isCompl t ht h2)
    (orthogonal b t hb h2) (fun y x => orthogonal b.flip t (fun x y => hb y x) h2 x y)

theorem minus_nondegenerate (b : LinearMap.BilinForm F V) (hn : b.Nondegenerate)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (hb : ∀ x y, b (t x) (t y) = b x y) (h2 : (2 : F) ≠ 0) :
    (b.restrict (minus t)).Nondegenerate :=
  restriction_nondegenerate b hn _ _ (isCompl t ht h2).symm
    (fun y x => orthogonal b.flip t (fun x y => hb y x) h2 x y) (orthogonal b t hb h2)

theorem finrank_plus_add_minus [FiniteDimensional F V] (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    Module.finrank F (plus t) + Module.finrank F (minus t) = Module.finrank F V := by
  rw [← Module.finrank_prod]
  exact (decomposition t ht h2).finrank_eq
end Matrix.PSp4Three.NontrivialTwoCore.Geometry.LinearInvolution

end

namespace Matrix.PSp4Three.NontrivialTwoCore.Geometry.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]

private theorem eq_neg_id_of_plus_finrank_zero (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0)
    (h : Module.finrank F (plus t) = 0) : t = -LinearMap.id := by
  have hz : plus t = ⊥ := Submodule.finrank_eq_zero.mp h
  ext x
  obtain ⟨⟨p,m⟩,rfl⟩ := (decomposition t ht h2).surjective x
  have hp : p.val = 0 := by simpa [hz] using p.prop
  change t (p.val + m.val) = -(p.val + m.val)
  rw [hp, zero_add, (mem_minus t m.val).mp m.prop]

private theorem eq_id_of_minus_finrank_zero (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0)
    (h : Module.finrank F (minus t) = 0) : t = LinearMap.id := by
  have hz : minus t = ⊥ := Submodule.finrank_eq_zero.mp h
  ext x
  obtain ⟨⟨p,m⟩,rfl⟩ := (decomposition t ht h2).surjective x
  have hm : m.val = 0 := by simpa [hz] using m.prop
  change t (p.val + m.val) = p.val + m.val
  rw [hm, add_zero, (mem_plus t p.val).mp p.prop]

/-- An involutory isometry of an alternating plane is a scalar sign. -/
theorem eq_id_or_neg_id_of_finrank_le_two
    (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (hp : ∀ x y, B (t x) (t y) = B x y) (h2 : (2 : F) ≠ 0)
    (hd : Module.finrank F V ≤ 2) : t = LinearMap.id ∨ t = -LinearMap.id := by
  have hd' := finrank_plus_add_minus t ht h2
  obtain ⟨a, ha⟩ := AlternatingForm.even_finrank (B.restrict (plus t))
    (fun x => hA x.val) (plus_nondegenerate B hB t ht hp h2)
  obtain ⟨b, hb⟩ := AlternatingForm.even_finrank (B.restrict (minus t))
    (fun x => hA x.val) (minus_nondegenerate B hB t ht hp h2)
  by_cases hz : Module.finrank F (minus t) = 0
  · exact Or.inl (eq_id_of_minus_finrank_zero t ht h2 hz)
  · exact Or.inr (eq_neg_id_of_plus_finrank_zero t ht h2 (by omega))

/-- A nonscalar involution in dimension at most four has two alternating planes. -/
theorem finranks_eq_two
    (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (hp : ∀ x y, B (t x) (t y) = B x y) (h2 : (2 : F) ≠ 0)
    (hd : Module.finrank F V ≤ 4) (hnp : t ≠ LinearMap.id)
    (hnm : t ≠ -LinearMap.id) :
    Module.finrank F (plus t) = 2 ∧ Module.finrank F (minus t) = 2 := by
  have hd' := finrank_plus_add_minus t ht h2
  obtain ⟨a, ha⟩ := AlternatingForm.even_finrank (B.restrict (plus t))
    (fun x => hA x.val) (plus_nondegenerate B hB t ht hp h2)
  obtain ⟨b, hb⟩ := AlternatingForm.even_finrank (B.restrict (minus t))
    (fun x => hA x.val) (minus_nondegenerate B hB t ht hp h2)
  have hp0 := mt (eq_neg_id_of_plus_finrank_zero t ht h2) hnm
  have hm0 := mt (eq_id_of_minus_finrank_zero t ht h2) hnp
  omega

omit [FiniteDimensional F V] in
private theorem exists_sign (t : V →ₗ[F] V)
    (h : t = LinearMap.id ∨ t = -LinearMap.id) :
    ∃ b : Bool, t = if b then LinearMap.id else -LinearMap.id := by
  rcases h with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

/-- A faithful commuting family of involutory isometries in dimension at most
four has at most four members. -/
theorem card_le_four_of_commuting_involutions {ι : Type*}
    (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate)
    (f : ι → V →ₗ[F] V) (hf : Function.Injective f)
    (hi : ∀ i, Function.Involutive (f i))
    (hp : ∀ i x y, B (f i x) (f i y) = B x y)
    (hc : ∀ i j x, f i (f j x) = f j (f i x))
    (h2 : (2 : F) ≠ 0) (hd : Module.finrank F V ≤ 4) : Nat.card ι ≤ 4 := by
  classical
  by_cases hs : ∀ i, f i = LinearMap.id ∨ f i = -LinearMap.id
  · choose b hb using fun i => exists_sign (f i) (hs i)
    have hinj : Function.Injective b := by
      intro i j hij
      apply hf
      rw [hb i, hb j, hij]
    have hcard := Nat.card_le_card_of_injective b hinj
    have : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
    omega
  push Not at hs
  obtain ⟨a, ha1, ha2⟩ := hs
  have hdims := finranks_eq_two B hA hB (f a) (hi a) (hp a) h2 hd ha1 ha2
  have hplus (i : ι) : ∀ x ∈ plus (f a), f i x ∈ plus (f a) := by
    intro x hx
    rw [mem_plus] at hx ⊢
    rw [hc a i, hx]
  have hminus (i : ι) : ∀ x ∈ minus (f a), f i x ∈ minus (f a) := by
    intro x hx
    rw [mem_minus] at hx ⊢
    rw [hc a i, hx, map_neg]
  let fp (i : ι) : plus (f a) →ₗ[F] plus (f a) := (f i).restrict (hplus i)
  let fm (i : ι) : minus (f a) →ₗ[F] minus (f a) := (f i).restrict (hminus i)
  have hfp (i : ι) : fp i = LinearMap.id ∨ fp i = -LinearMap.id := by
    apply eq_id_or_neg_id_of_finrank_le_two (B.restrict (plus (f a)))
      (fun x => hA x.val) (plus_nondegenerate B hB (f a) (hi a) (hp a) h2)
      (fp i) (fun x => Subtype.ext (hi i x.val))
      (fun x y => hp i x.val y.val) h2 hdims.1.le
  have hfm (i : ι) : fm i = LinearMap.id ∨ fm i = -LinearMap.id := by
    apply eq_id_or_neg_id_of_finrank_le_two (B.restrict (minus (f a)))
      (fun x => hA x.val) (minus_nondegenerate B hB (f a) (hi a) (hp a) h2)
      (fm i) (fun x => Subtype.ext (hi i x.val))
      (fun x y => hp i x.val y.val) h2 hdims.2.le
  choose bp hbp using fun i => exists_sign (fp i) (hfp i)
  choose bm hbm using fun i => exists_sign (fm i) (hfm i)
  let signs (i : ι) := (bp i, bm i)
  have hinj : Function.Injective signs := by
    intro i j hij
    have hpij : fp i = fp j := by rw [hbp i, hbp j, show bp i = bp j from congrArg Prod.fst hij]
    have hmij : fm i = fm j := by rw [hbm i, hbm j, show bm i = bm j from congrArg Prod.snd hij]
    apply hf
    ext x
    obtain ⟨⟨p,m⟩,rfl⟩ := (decomposition (f a) (hi a) h2).surjective x
    have hpe := congrArg (fun t : plus (f a) →ₗ[F] plus (f a) => (t p).val) hpij
    have hme := congrArg (fun t : minus (f a) →ₗ[F] minus (f a) => (t m).val) hmij
    change f i (p.val + m.val) = f j (p.val + m.val)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hpe hme
  have hcard := Nat.card_le_card_of_injective signs hinj
  simpa [Nat.card_eq_fintype_card] using hcard

end Matrix.PSp4Three.NontrivialTwoCore.Geometry.LinearInvolution
