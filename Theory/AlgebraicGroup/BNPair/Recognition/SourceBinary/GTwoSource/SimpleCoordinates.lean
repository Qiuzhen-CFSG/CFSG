module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LinearLocalRoots

/-!
# Field coordinates through the actual local panel group

The specified unipotent Sylow U maps onto a Sylow subgroup of the source
panel group L_i. The earlier radical inclusion U_{s_i} ≤ K_i kills exactly
the remainder in U = U_i U_{s_i}, so the canonical simple root has that
entire Sylow image. Its already proved faithful panel action therefore
gives a multiplicative equivalence, and an actual L_i ≃ PSL₂(F) transfers
the additive field coordinates back to U_i in the same quotient.

This construction includes q=2 and uses no perfectness of an original local
factor. The model equation retains the literal panel map and the supplied
local isomorphism. Conjugation transports these coordinates along any
specified lift in the same N. Field compatibility between distinct roots,
SL₂ pinnings of R_i and mixed commutators are separate obligations.

Source: Fong--Seitz I, Section 5 (especially (5C)), printed pp.25--28,
and the actual local PSL₂ identifications in (6E)(a), printed p.43.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The image of the specified Sylow U in the actual local panel group. -/
def localSylow (i : Fin 2) : Sylow 2 (localGroup Q split i) :=
  (split.sylow.subtype (show split.U ≤ localClosure Q split i from le_sup_left)).mapSurjective
    (localAction Q split i).rangeRestrict_surjective

/-- The radical kernel premise makes the simple root image the full local Sylow. -/
theorem simpleRootLocalMap_range (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    (simpleRootLocalMap Q split i).range = (localSylow Q split i : Subgroup _) := by
  apply le_antisymm
  · rintro _ ⟨u,rfl⟩
    refine ⟨⟨u,(show simpleRoot Q split i ≤ localClosure Q split i from
      (simpleRoot_le Q split i).trans le_sup_left) u.property⟩,
      simpleRoot_le Q split i u.property,?_⟩
    apply Subtype.ext
    rw [simpleRootLocalMap_apply]
    change localAction Q split i _ = _
    rw [localAction_eq_panelAction]
    rfl
  · rintro _ ⟨u,hu,rfl⟩
    have hu' : (u : X ⧸ Q.D) ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
        (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]
      exact hu
    obtain ⟨a,ha,v,hv,hev⟩ := hu'
    let a' : localClosure Q split i := ⟨a, ((simpleRoot_le Q split i).trans (show split.U ≤ localClosure Q split i from le_sup_left)) ha⟩
    let v' : localClosure Q split i := ⟨v, (show split.U ≤ localClosure Q split i from
      le_sup_left) hv.1⟩
    have hvker : v' ∈ (localAction Q split i).ker := by
      rw [localAction_ker]
      exact hV hv
    have he : u = a' * v' := Subtype.ext hev.symm
    refine ⟨⟨a,ha⟩,?_⟩
    apply Subtype.ext
    rw [simpleRootLocalMap_apply]
    change panelAction Q i (simpleRoot Q split i) _ ⟨a,ha⟩ = localAction Q split i u
    rw [he,map_mul,MonoidHom.mem_ker.mp hvker,mul_one,localAction_eq_panelAction]
    rfl

/-- The full Sylow comparison uses the canonical panel action, even at q=2. -/
def simpleRootLocalSylowEquiv (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    simpleRoot Q split i ≃* localSylow Q split i :=
  (MonoidHom.ofInjective (simpleRootLocalMap_injective Q split i)).trans
      (MulEquiv.subgroupCongr (simpleRootLocalMap_range Q split i hV))

/-- The specified local PSL₂ comparison carries the same full Sylow. -/
def linearSylow (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F)) : Sylow 2 PSL(2,F) :=
  (localSylow Q split i).mapSurjective (f := μ.toMonoidHom) μ.surjective

def linearSylowEquiv (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F)) :
    localSylow Q split i ≃* linearSylow Q split i μ :=
  (localSylow Q split i : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective

def simpleRootFieldEquiv (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    Multiplicative F ≃* simpleRoot Q split i :=
  (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearSylow Q split i μ)).trans
    ((linearSylowEquiv Q split i μ).symm.trans
      (simpleRootLocalSylowEquiv Q split i hV).symm)

@[simp] theorem simpleRootLocalSylowEquiv_apply (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (u : simpleRoot Q split i) :
    (simpleRootLocalSylowEquiv Q split i hV u : localGroup Q split i) =
      simpleRootLocalMap Q split i u := rfl

@[simp] theorem simpleRootFieldEquiv_model (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (a : Multiplicative F) :
    μ (simpleRootLocalMap Q split i (simpleRootFieldEquiv Q split i hV μ a)) =
      (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearSylow Q split i μ) a : PSL(2,F)) := by
  rw [← simpleRootLocalSylowEquiv_apply Q split i hV]
  simp only [simpleRootFieldEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change (linearSylowEquiv Q split i μ
    ((linearSylowEquiv Q split i μ).symm
      (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearSylow Q split i μ) a)) : PSL(2,F)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The additive coordinates land in the original simple root in Y. -/
def simpleParameter (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) : Multiplicative F →* X ⧸ Q.D :=
  (simpleRoot Q split i).subtype.comp (simpleRootFieldEquiv Q split i hV μ).toMonoidHom

@[simp] theorem simpleParameter_range (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    (simpleParameter Q split i hV μ).range = simpleRoot Q split i := by
  rw [simpleParameter, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (simpleRootFieldEquiv Q split i hV μ).surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem simpleParameter_injective (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    Function.Injective (simpleParameter Q split i hV μ) :=
  Subtype.val_injective.comp (simpleRootFieldEquiv Q split i hV μ).injective

theorem simpleRoot_card (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    Nat.card (simpleRoot Q split i) = Nat.card F :=
  (Nat.card_congr (simpleRootFieldEquiv Q split i hV μ).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

/-- Transport the entire additive root along a specified lift in the same N. -/
def conjugateParameter (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : Q.tits.N) :
    Multiplicative F →* X ⧸ Q.D :=
  (MulAut.conj (n : X ⧸ Q.D)⁻¹).toMonoidHom.comp (simpleParameter Q split i hV μ)

theorem conjugateParameter_injective (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : Q.tits.N) :
    Function.Injective (conjugateParameter Q split i hV μ n) :=
  (MulAut.conj (n : X ⧸ Q.D)⁻¹).injective.comp
    (simpleParameter_injective Q split i hV μ)

theorem conjugateParameter_range (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (w : Weyl Q) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = w) :
    (conjugateParameter Q split i hV μ n).range = rootAt Q split i w := by
  rw [conjugateParameter, MonoidHom.range_comp, simpleParameter_range,
    rootAt_eq Q split i w n hn, rightConjugate, comap_equiv_eq_map_symm']
  rw [map_inv]
  rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
