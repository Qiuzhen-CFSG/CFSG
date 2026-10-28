module

public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.Frattini.Intersection
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The intersection in Lemma 12.8.11

For the literal W=C_U(V₂), X=W^g and E=W∩X, the earlier abelian
quotient gives [W,X]≤E. Frattini functoriality places Φ(E) in the
disjoint conjugate Frattini lines. Thus E is elementary abelian, and
its image in the actual quotient U/Z(U) is totally isotropic for the
commutator form. The earlier §12.8 inputs remain explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.11(1–2), printed p.854 / PDF p.871.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The point lies in the center of its conjugate span. -/
theorem point_le_ZU (F : InvariantFlag T V n) [IsMulCommutative V] (hn : 1 ≤ n) :
    F.Vi 1 ≤ F.ZU := by
  have hU : F.U ≤ centralizer (F.Vi 1 : Set G) :=
    F.U_le_H.trans (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 hn))
  intro z hz
  refine ⟨⟨z, (F.le_seed 1).trans (le_conjugateSpanBy V F.H) hz⟩,
    mem_center_iff.mpr ?_, rfl⟩
  intro u
  exact Subtype.ext (hU u.property z hz).symm

/-- Source 12.8.11(1), from the abelian quotient in 12.8.9(2). -/
theorem commutator_W_X_le_E (F : InvariantFlag T V n) (g : G)
    [((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal]
    [IsMulCommutative ((F.W ⊔ F.X g : Subgroup G) ⧸
      (F.E g).subgroupOf (F.W ⊔ F.X g))] :
    ⁅F.W, F.X g⁆ ≤ F.E g := by
  apply commutator_le.mpr
  intro w hw x hx
  let w' : (F.W ⊔ F.X g : Subgroup G) := ⟨w, (le_sup_left : F.W ≤ F.W ⊔ F.X g) hw⟩
  let x' : (F.W ⊔ F.X g : Subgroup G) := ⟨x, (le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx⟩
  exact ((Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := (F.E g).subgroupOf (F.W ⊔ F.X g))).mp inferInstance)
    (show ⁅w', x'⁆ ∈ _root_.commutator (F.W ⊔ F.X g : Subgroup G) from
      commutator_mem_commutator (mem_top w') (mem_top x'))

/-- Source 12.8.11(2): the two conjugate Frattini lines meet trivially.
The inputs are precisely the Frattini assertion of 12.8.4 and 12.8.9(7). -/
theorem frattini_E_eq_bot (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 1 ≤ n) (g : G)
    (hU : IsPGroup 2 F.U)
    (hPhi : (frattini F.U).map F.U.subtype = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU) :
    frattini (F.E g) = ⊥ := by
  have hE : F.E g ≤ F.U := inf_le_left.trans inf_le_left
  have hEg : F.E g ≤ conjugate F.U g :=
    inf_le_right.trans (map_mono (show F.W ≤ F.U from inf_le_left))
  apply frattini_eq_bot_of_disjoint_images hU
    (hU.map (MulAut.conj g⁻¹).toMonoidHom) hE hEg
  rw [frattini_image_map F.U _ (MulAut.conj g⁻¹).injective, hPhi]
  exact (hdis.mono_right (F.point_le_ZU hn)).symm

/-- The actual intersection is elementary abelian, not just its central image. -/
theorem E_elementary (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 1 ≤ n) (g : G)
    (hU : IsPGroup 2 F.U)
    (hPhi : (frattini F.U).map F.U.subtype = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU) :
    IsElementaryAbelian 2 (F.E g) := by
  let : Fact (IsPGroup 2 (F.E g)) := ⟨hU.of_injective
    (inclusion (show F.E g ≤ F.U from inf_le_left.trans inf_le_left))
    (inclusion_injective _)⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (F.frattini_E_eq_bot hn g hU hPhi hdis)


namespace Symplectic

/-- The literal image in `U/Z(U)`. -/
def hatImage (F : InvariantFlag T V n) (A : Subgroup G) : Subgroup F.Uhat :=
  (A.subgroupOf F.U).map (QuotientGroup.mk' (center F.U))

/-- The same image as a binary subspace. -/
def hatSpace (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (A : Subgroup G) : Submodule (ZMod 2) (Additive F.Uhat) :=
  AddSubgroup.toZModSubmodule (n := 2) (hatImage F A).toAddSubgroup

/-- Source 12.8.11(2), with the commutator form of 12.8.8(2) specified by
its zero criterion on the literal quotient map. -/
theorem Ehat_totally_isotropic (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 1 ≤ n) (g : G) (hU : IsPGroup 2 F.U)
    (hPhi : (frattini F.U).map F.U.subtype = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U,
      B (Additive.ofMul (QuotientGroup.mk' (center F.U) u))
        (Additive.ofMul (QuotientGroup.mk' (center F.U) v)) = 0 ↔ Commute u v) :
    ∀ e ∈ hatSpace F (F.E g), ∀ f ∈ hatSpace F (F.E g), B e f = 0 := by
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary hn g hU hPhi hdis
  intro e he f hf
  obtain ⟨u, hu, he⟩ := (show e.toMul ∈ hatImage F (F.E g) from he)
  obtain ⟨v, hv, hf⟩ := (show f.toMul ∈ hatImage F (F.E g) from hf)
  have hc : Commute u v := by
    change u * v = v * u
    apply Subtype.ext
    exact congrArg (fun a : F.E g => (a : G)) (mul_comm (⟨(u : G), hu⟩ : F.E g) ⟨(v : G), hv⟩)
  simpa only [he, hf, ofMul_toMul] using (hB u v).mpr hc

end Symplectic

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
