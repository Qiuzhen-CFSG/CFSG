module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Reduction
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# A binary graph and field model in the Frobenius centralizer

Binary coefficient inclusion, followed by inner conjugation, commutes with
Frobenius on the actual PSL₃(4). It intertwines inverse transpose on binary
matrices with the projective graph involution. This constructs a homomorphism
from `(SL₃(2) ⋊ C₂) × C₂` into the full automorphism centralizer of Frobenius;
the semidirect factor acts by inverse transpose and the final factor by Frobenius.
The domain has order 672.

Surjectivity and faithfulness are separate obligations. The fixed-subgroup
isomorphism inside PSL₃(4) alone does not establish either assertion about its
full automorphism centralizer.

This is the concrete model calculation supporting the quaternion-placement
application on printed p.1192 of Aschbacher–Smith, `refs/quasithin.pdf`, with
the field-involution row 16.1.4(4), printed p.1171. The action conventions are
those of GLS3 §2.7.
-/

@[expose] public section

open Subgroup
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
noncomputable section

/-- The centralizer inside the full automorphism group of PSL₃(4). -/
abbrev C := automorphismCentralizer pslFrobenius
abbrev Binary := PSL3Two.SL
abbrev binaryCast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

/-- Binary matrices included in the actual projective group over four elements. -/
def binaryProject : Binary →* PSL :=
  (QuotientGroup.mk' (Subgroup.center SL)).comp (SpecialLinearGroup.map binaryCast)

theorem binaryCast_fixed (x : ZMod 2) : fieldFrobenius (binaryCast x) = binaryCast x := by
  have h : x = 0 ∨ x = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x
  rcases h with rfl | rfl <;> simp

theorem binaryProject_fixed (x : Binary) : pslFrobenius (binaryProject x) = binaryProject x := by
  change (slFrobenius (SpecialLinearGroup.map binaryCast x) : PSL) = _
  congr 1
  ext i j
  exact binaryCast_fixed (x i j)

theorem graph_commute_frobenius : Commute (graph F) pslFrobenius := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, pslFrobenius_mk, graph_mk]
    rw [map_inv]
    congr 2

-- The transpose-inverse involution at the binary matrix level.
theorem binaryGraph_sq : graphSL (ZMod 2) ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  exact (graphSL (ZMod 2)).left_inv x

/-- The inverse-transpose action on binary matrices. -/
def binaryGraphAction : C2 →* MulAut Binary :=
  involutionHom (graphSL (ZMod 2)) binaryGraph_sq

abbrev GraphModel := Binary ⋊[binaryGraphAction] C2
abbrev Model := GraphModel × C2

def binaryInner : Binary →* MulAut PSL := MulAut.conj.comp binaryProject

theorem graph_binaryProject (x : Binary) :
    graph F (binaryProject x) = binaryProject (graphSL (ZMod 2) x) := by
  change (QuotientGroup.mk' (center SL)) _ = (QuotientGroup.mk' (center SL)) _
  congr 1
  change (SpecialLinearGroup.transpose (SpecialLinearGroup.map binaryCast x))⁻¹ =
    SpecialLinearGroup.map binaryCast ((SpecialLinearGroup.transpose x)⁻¹)
  rw [map_inv]
  rfl

private theorem conjugate_conj (a : MulAut PSL) (x : PSL) :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  apply MulEquiv.ext
  intro y
  change a x * y * (a x)⁻¹ = a (x * a.symm y * x⁻¹)
  simp only [map_mul, map_inv, a.apply_symm_apply]

private theorem c2_cases (t : C2) : t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2) :=
  (by decide : ∀ t : C2, t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2)) t

private theorem graph_binaryInner (t : C2) :
    binaryInner.comp (binaryGraphAction t).toMonoidHom =
      (MulAut.conj (involutionHom (graph F) (graph_sq F) t)).toMonoidHom.comp
        binaryInner := by
  rcases c2_cases t with rfl | rfl
  · ext x
    rfl
  · apply MonoidHom.ext
    intro x
    change MulAut.conj (binaryProject (binaryGraphAction _ x)) = _
    rw [binaryGraphAction, involutionHom_generator, ← graph_binaryProject]
    exact conjugate_conj (graph F) (binaryProject x)

def graphModelHom : GraphModel →* MulAut PSL :=
  SemidirectProduct.lift binaryInner (involutionHom (graph F) (graph_sq F))
    (by exact graph_binaryInner)

theorem binaryInner_commute_frobenius (x : Binary) :
    Commute (binaryInner x) pslFrobenius := by
  apply MulEquiv.ext
  intro y
  change binaryProject x * pslFrobenius y * (binaryProject x)⁻¹ =
    pslFrobenius (binaryProject x * y * (binaryProject x)⁻¹)
  rw [map_mul, map_mul, map_inv, binaryProject_fixed]

theorem graphModelHom_commute_frobenius (x : GraphModel) :
    Commute (graphModelHom x) pslFrobenius :=
  (binaryInner_commute_frobenius x.left).mul_left
    (graph_commute_frobenius.pow_left x.right.toAdd.val)

def modelAutHom : Model →* MulAut PSL :=
  graphModelHom.noncommCoprod fieldAction (fun x t =>
    (graphModelHom_commute_frobenius x).pow_right t.toAdd.val)

/-- The binary graph and field action, with codomain the actual centralizer. -/
def modelHom : Model →* C := modelAutHom.codRestrict C (by
  intro x
  apply mem_centralizer_singleton_iff.mpr
  exact ((graphModelHom_commute_frobenius x.1).mul_left
    ((Commute.refl pslFrobenius).pow_left x.2.toAdd.val)).eq)

theorem modelHom_apply (x : Model) :
    (modelHom x : MulAut PSL) =
      MulAut.conj (binaryProject x.1.left) *
        involutionHom (graph F) (graph_sq F) x.1.right * fieldAction x.2 := rfl

instance finiteGraphModel : Finite GraphModel := Finite.of_equiv (Binary × C2) SemidirectProduct.equivProd.symm

theorem card_model : Nat.card Model = 672 := by
  rw [Nat.card_prod, Nat.card_congr (SemidirectProduct.equivProd (φ := binaryGraphAction)),
    Nat.card_prod, PSL3Two.card_SL, card_C2]

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
