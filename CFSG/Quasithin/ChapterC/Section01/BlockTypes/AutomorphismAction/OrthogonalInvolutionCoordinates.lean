module
public import Theory.Representation.SL2OrthogonalCover.OuterSemilinear
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverCoordinates
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction

/-!
# Actual orthogonal coordinates for a full-cover block involution

The full central-cover hypothesis identifies the original two-core with the
three-dimensional orthogonal cover. Transporting the given block automorphism
through that same equivalence produces a binary actor intertwining the literal
quotient automorphism. Its outer involution has a nontrivial involutory field
coefficient, acting semilinearly on the entire core.

The packet retains both original quotient and conjugation maps. In particular,
central elements of the original core map into the orthogonal radical and hence
into the root-fixed plane. Consumers can therefore use the fixed commutator
rows and fixed singular vectors without substituting an unrelated model.

The private import is an intentional proof extension of AutomorphismAction;
its implementation remains absent from the public packet fields.
Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532, and the marked cover
calculation used in Lemma 2.4.21.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterC
variable (L : Type*) [Group L]

/-- Marked full-cover coordinates for the original block involution. -/
structure OrthogonalInvolutionCoordinates (n : ℕ) (a : MulAut L) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  [charTwo : CharP F 2]
  [binaryAlgebra : Algebra (ZMod 2) F]
  card : Nat.card F = 2 ^ n
  quotient : (L ⧸ pCore 2 L) ≃* SL2OrthogonalCover.SL F
  core : pCore 2 L ≃* Multiplicative (SL2OrthogonalCover.Space F)
  actor : SL2OrthogonalCover.Space F ≃ₗ[ZMod 2] SL2OrthogonalCover.Space F
  coefficient : F ≃+* F
  coefficient_ne : coefficient ≠ RingEquiv.refl F
  coefficient_involutive : Function.Involutive coefficient
  actor_involutive : Function.Involutive actor
  semilinear : ∀ c v, actor (c • v) = coefficient c • actor v
  core_equivariant : ∀ u : pCore 2 L,
    (core (MulAut.characteristic (pCore 2 L) a u)).toAdd = actor (core u).toAdd
  conjugation_equivariant : ∀ (l : L) (u : pCore 2 L),
    (core (MulAut.conjNormal l u)).toAdd = SL2OrthogonalCover.action
      (quotient (QuotientGroup.mk' (pCore 2 L) l)) (core u).toAdd
  normalizer_equivariant : ∀ (g : SL2OrthogonalCover.SL F) (v : SL2OrthogonalCover.Space F),
    actor (SL2OrthogonalCover.action g v) = SL2OrthogonalCover.action
      (MulAut.congr quotient (quotientAut (pCore 2 L) a) g) (actor v)

attribute [instance] OrthogonalInvolutionCoordinates.field OrthogonalInvolutionCoordinates.finite
  OrthogonalInvolutionCoordinates.charTwo OrthogonalInvolutionCoordinates.binaryAlgebra

variable {L}

/-- The packet is produced from the original full-cover block and involution,
with both quotient and core conjugation maps retained. -/
theorem IsL2EvenBlock.orthogonal_involution_coordinates {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : Nat.card (center L) = 2 ^ n)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) :
    Nonempty (OrthogonalInvolutionCoordinates L n a) := by
  let := hL.2.1.finite
  let := hL.2.1.elementary
  let := hL.2.1.module_elementary
  obtain ⟨F,_,_,hF,_,ρ,⟨m⟩,hm⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfixed : Nat.card (blockFixed L) = 2^n :=
    (Nat.card_congr (subgroupOfEquivOfLe (hL.center_le_module hcore)).toEquiv).trans hz
  obtain ⟨eU,heU⟩ := modelCover_orthogonal_equiv hL.2.1 m hm hL.1 hF hfixed
  let e : pCore 2 L ≃* Multiplicative (SL2OrthogonalCover.Space F) :=
    (MulEquiv.subgroupCongr hcore).trans eU
  let κ := MulAut.characteristic (pCore 2 L) a
  let A := MulAut.congr e κ
  let E₀ : SL2OrthogonalCover.Space F ≃+ SL2OrthogonalCover.Space F :=
    { toFun v := (A (Multiplicative.ofAdd v)).toAdd
      invFun v := (A.symm (Multiplicative.ofAdd v)).toAdd
      left_inv v := A.symm_apply_apply v
      right_inv v := A.apply_symm_apply v
      map_add' v w := A.map_mul v w }
  let E : SL2OrthogonalCover.Space F ≃ₗ[ZMod 2] SL2OrthogonalCover.Space F :=
    { E₀ with map_smul' := fun c v => ZMod.map_smul E₀ c v }
  have heκ (u : pCore 2 L) : (e (κ u)).toAdd = E (e u).toAdd := by
    change (e (κ u)).toAdd = (e (κ (e.symm (e u)))).toAdd
    rw [e.symm_apply_apply]
  have hel (l : L) (u : pCore 2 L) :
      (e (MulAut.conjNormal l u)).toAdd = SL2OrthogonalCover.action
        (m.actor l) (e u).toAdd := by
    exact heU l (MulEquiv.subgroupCongr hcore u)
  have hE (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : SL2OrthogonalCover.Space F) :
      E (SL2OrthogonalCover.action g v) = SL2OrthogonalCover.action (m.quotientAction a g) (E v) := by
    obtain ⟨l,rfl⟩ := m.actor_surjective g
    obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have hv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv,←hel,←heκ,←heκ,m.quotientAction_actor]
    have hconj : κ (MulAut.conjNormal l u) = MulAut.conjNormal (a l) (κ u) := by
      apply Subtype.ext
      change a (l*u.val*l⁻¹)=a l * a u.val * (a l)⁻¹
      simp only [map_mul,map_inv]
    rw [hconj,hel]
  have ho : ¬ ∃ g, m.quotientAction a = MulAut.conj g := by
    exact fun hh => houter ((MulAut.congr_inner_iff m.quotientIso _).mp hh)
  have hκ : Function.Involutive κ := by
    intro u
    have hh : κ^2=1 := by dsimp only [κ]; rw [←map_pow,ha,map_one]
    exact DFunLike.congr_fun hh u

  have hEinv : Function.Involutive E := by
    intro v
    obtain ⟨u, hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have hv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [← hv, ← heκ, ← heκ, hκ]
  have hFgt : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hL.1)
  obtain ⟨σ, hσne, hσ⟩ := SL2OrthogonalCover.outer_intertwiner_semilinear
    hFgt (m.quotientAction a) E hE ho
  exact ⟨{ F := F
           card := hF
           quotient := m.quotientIso
           core := e
           actor := E
           coefficient := σ
           coefficient_ne := hσne
           coefficient_involutive := SL2OrthogonalCover.semilinear_coefficient_involutive E hEinv σ hσ
           actor_involutive := hEinv
           semilinear := hσ
           core_equivariant := heκ
           conjugation_equivariant := hel
           normalizer_equivariant := hE }⟩

namespace OrthogonalInvolutionCoordinates
variable {n : ℕ} {a : MulAut L} (c : OrthogonalInvolutionCoordinates L n a)

/-- Central elements in the original core lie on the actual orthogonal radical. -/
theorem center_mem_radical (u : pCore 2 L) (hu : (u : L) ∈ center L) :
    (c.core u).toAdd ∈ (SL2OrthogonalCover.form (F := c.F)).polarBilin.ker := by
  rw [← SL2OrthogonalCover.fixed_radical]
  intro g
  obtain ⟨x, hx⟩ := c.quotient.surjective g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  have heq : MulAut.conjNormal l u = u := by
    apply Subtype.ext
    change l * (u : L) * l⁻¹ = (u : L)
    rw [(Subgroup.mem_center_iff.mp hu l), mul_assoc, mul_inv_cancel, mul_one]
  rw [← hx, ← c.conjugation_equivariant, heq]

/-- In particular the original center is contained in the root-fixed plane. -/
theorem center_mem_fixedPlane (u : pCore 2 L) (hu : (u : L) ∈ center L) :
    (c.core u).toAdd ∈ SL2OrthogonalCover.fixedPlane := by
  exact (SL2OrthogonalCover.mem_polar_ker _).mp (c.center_mem_radical u hu) |>.2
end OrthogonalInvolutionCoordinates
end CFSG.Quasithin.ChapterC
