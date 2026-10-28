module
public import Theory.SpecificGroups.PSL3Two.Parabolics.PointNormalizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.GroupTheory.RegularWreathSubgroup
public import Theory.SpecificGroups.SymmetricFourWreath.ResidualQuotient
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.WreathTwoCoreQuotient

/-!
# The two parabolics in the paired binary three-space actor

The coordinate copies of the point and line parabolics are distinct maximal
S₄ wreath subgroups. They contain the same full Sylow two-subgroup and generate
SL₃(2) wr C₂. The constructions retain the literal matrix flag and wreath
coordinates, for the two residuals in Aschbacher--Smith 10.2.4--5, p.747.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two.WreathPair
abbrev Bit := Multiplicative (ZMod 2)
abbrev Actor := RegularWreathProduct SL Bit
@[expose] def point : Subgroup Actor := RegularWreathProduct.coordinateSubgroup pointParabolicSL
@[expose] def line : Subgroup Actor := RegularWreathProduct.coordinateSubgroup lineParabolicSL
@[expose] def borel : Subgroup Actor := RegularWreathProduct.coordinateSubgroup borelSL

private theorem card_bit : Nat.card Bit = 2 := Nat.card_zmod 2

/-- The actual common flag subgroup is a full Sylow two-subgroup. -/
def sylow : Sylow 2 Actor := Sylow.ofCard borel (by
  change Nat.card (RegularWreathProduct.coordinateSubgroup (Q := Bit) borelSL) = _
  rw [Nat.card_congr (RegularWreathProduct.coordinateSubgroupEquiv borelSL).toEquiv,
    RegularWreathProduct.card,RegularWreathProduct.card,card_bit,card_borelSL,card_SL]
  decide +kernel)

theorem sylow_eq : (sylow : Subgroup Actor) = borel := by rfl

theorem borel_le_point : borel ≤ point := fun _ hw i => (hw i).1

theorem borel_le_line : borel ≤ line := fun _ hw i => (hw i).2

theorem point_maximal : IsCoatom point :=
  RegularWreathProduct.coordinateSubgroup_isCoatom pointParabolicSL
    isCoatom_pointParabolicSL pointParabolicSL_normalizer

private theorem line_normalizer : normalizer (lineParabolicSL : Set SL) = lineParabolicSL := by
  rw [← MarkedAutomorphisms.pointParabolic_map_diagram,
    ← map_equiv_normalizer_eq,pointParabolicSL_normalizer]

theorem line_maximal : IsCoatom line :=
  RegularWreathProduct.coordinateSubgroup_isCoatom lineParabolicSL
    isCoatom_lineParabolicSL line_normalizer

theorem point_ne_line : point ≠ line := by
  intro he
  apply pointParabolicSL_ne_line
  apply le_antisymm
  · intro x hx
    have h : (⟨fun _ => x,1⟩ : Actor) ∈ point := fun _ => hx
    exact (he ▸ h) 1
  · intro x hx
    have h : (⟨fun _ => x,1⟩ : Actor) ∈ line := fun _ => hx
    exact (he.symm ▸ h) 1

/-- The distinct maximal flag overgroups generate the whole paired actor. -/
theorem parabolics_generate : point ⊔ line = ⊤ := by
  apply point_maximal.2
  apply lt_of_le_of_ne le_sup_left
  intro he
  have hl : line ≤ point := he ▸ le_sup_right
  exact point_maximal.ne_top
    (line_maximal.2 _ (lt_of_le_of_ne hl (Ne.symm point_ne_line)))

private def coordinateEquiv (H : Subgroup SL) :
    RegularWreathProduct.coordinateSubgroup (Q := Bit) H ≃* RegularWreathProduct H Bit where
  toFun w := ⟨fun i => ⟨w.val.left i,w.property i⟩,w.val.right⟩
  invFun w := ⟨⟨fun i => (w.left i).val,w.right⟩,fun i => (w.left i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def pointEquiv : point ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) Bit :=
  (coordinateEquiv pointParabolicSL).trans
    (RegularWreathProduct.congr MarkedAutomorphisms.pointEquivSymmetric (MulEquiv.refl Bit))

def lineEquiv : line ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) Bit :=
  (coordinateEquiv lineParabolicSL).trans
    (RegularWreathProduct.congr MarkedAutomorphisms.lineEquivSymmetric (MulEquiv.refl Bit))

/-- Both coordinate identifications retain the original factor permutation. -/
theorem pointEquiv_right (x : point) : (pointEquiv x).right = x.val.right := by rfl

theorem lineEquiv_right (x : line) : (lineEquiv x).right = x.val.right := by rfl

/-- The quotient is by the parabolic's own two-core. -/
def pointQuotientEquiv : (point ⧸ pCore 2 point) ≃* Theory.GroupTheory.WreathTwoResidual.Actor :=
  (QuotientGroup.congr _ _ pointEquiv (pCore_map_iso 2 pointEquiv)).trans
    SymmetricFourWreath.quotientEquivActor

def lineQuotientEquiv : (line ⧸ pCore 2 line) ≃* Theory.GroupTheory.WreathTwoResidual.Actor :=
  (QuotientGroup.congr _ _ lineEquiv (pCore_map_iso 2 lineEquiv)).trans
    SymmetricFourWreath.quotientEquivActor

end Matrix.PSL3Two.WreathPair

namespace Matrix.PSL3Two.WreathPair
variable {H : Type*} [Group H] [Finite H]

private def preimageEquiv (f : H →* Actor) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (P : Subgroup Actor) :
    (P.comap f ⧸ pCore 2 (P.comap f)) ≃* (P ⧸ pCore 2 P) := by
  let r := f.subgroupComap P
  have hr : Function.Surjective r := f.subgroupComap_surjective_of_surjective P hf
  have hk : r.ker = f.ker.subgroupOf (P.comap f) := by
    ext x
    change (r x : P) = 1 ↔ f x = 1
    exact Subtype.ext_iff
  exact r.pCoreQuotientEquiv hr (by
    rw [hk]
    exact hp.comap_subtype)

/-- A two-group cover of the paired actor has two distinct actual maximal
parabolics above every full Sylow, with their intrinsic quotients preserved. -/
theorem exists_parabolics (f : H →* Actor) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (S : Sylow 2 H) :
    ∃ A B : Subgroup H, (S : Subgroup H) ≤ A ∧ (S : Subgroup H) ≤ B ∧
      IsCoatom A ∧ IsCoatom B ∧ A ≠ B ∧ A ⊔ B = ⊤ ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Theory.GroupTheory.WreathTwoResidual.Actor) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Theory.GroupTheory.WreathTwoResidual.Actor) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor (S.mapSurjective hf) sylow
  let q := (MulAut.conj g).toMonoidHom.comp f
  have hq : Function.Surjective q := (MulAut.conj g).surjective.comp hf
  have hk : q.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hqp : IsPGroup 2 q.ker := hk ▸ hp
  have hS : (S : Subgroup H).map q = borel := by
    have he := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup H).map f).map (MulAut.conj g).toMonoidHom = _ at he
    simpa only [Subgroup.map_map,sylow_eq] using he
  let A := point.comap q
  let B := line.comap q
  have hSA : (S : Subgroup H) ≤ A := map_le_iff_le_comap.mp (hS ▸ borel_le_point)
  have hSB : (S : Subgroup H) ≤ B := map_le_iff_le_comap.mp (hS ▸ borel_le_line)
  have hA : IsCoatom A := isCoatom_comap_of_surjective hq point_maximal
  have hB : IsCoatom B := isCoatom_comap_of_surjective hq line_maximal
  have hne : A ≠ B := by
    intro he
    have hh := congrArg (Subgroup.map q) he
    exact point_ne_line (by simpa only [A,B,map_comap_eq_self_of_surjective hq] using hh)
  have hgen : A ⊔ B = ⊤ := by
    apply hA.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hBA : B ≤ A := he ▸ le_sup_right
    exact hA.ne_top (hB.2 _ (lt_of_le_of_ne hBA (Ne.symm hne)))
  exact ⟨A,B,hSA,hSB,hA,hB,hne,hgen,
    ⟨(preimageEquiv q hq hqp point).trans pointQuotientEquiv⟩,
    ⟨(preimageEquiv q hq hqp line).trans lineQuotientEquiv⟩⟩

end Matrix.PSL3Two.WreathPair
