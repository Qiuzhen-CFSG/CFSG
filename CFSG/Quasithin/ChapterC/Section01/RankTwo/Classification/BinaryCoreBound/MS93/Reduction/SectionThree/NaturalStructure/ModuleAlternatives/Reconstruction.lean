module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Reconstruction.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Reconstruction.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments

/-!
# Source assembly of the four binary module alternatives

The checked abstract central-attachment classification transfers to the
literal C, U, X and Z. Subgroup/subspace equivalences preserve disjointness,
the fixed kernel's order, and the index of Z in X. The resulting conditional
assembly retains all four source branches and their actual marked maps.

The remaining input is the fixed-generation identity for Z. Edges proves the
faithfulness and two-subgroup fixed-generation premises needed for that
algebraic step; neither the input identity nor the final alternatives are
claimed unconditionally here.
Source: Meierfrankenfeld–Stellmacher (1993), (3.2)(i),(iii)–(v), p.863.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Reconstruction
open CentralAttachments
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
local instance : IsElementaryAbelian 2 (X R (alpha R)) := X_elementary R (alpha R)

omit [Finite M] in
noncomputable def spaceEquiv {H : Subgroup (FreeAmalgam R)} (hH : H ≤ X R (alpha R)) :
    H ≃* Multiplicative (space H) where
  toFun u := Multiplicative.ofAdd ⟨Additive.ofMul ⟨u.val, hH u.property⟩, u.property⟩
  invFun v := ⟨v.toAdd.val.toMul, v.toAdd.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite M] in
theorem space_card {H : Subgroup (FreeAmalgam R)} (hH : H ≤ X R (alpha R)) :
    Nat.card H = Nat.card (space H) := Nat.card_congr (spaceEquiv hH).toEquiv

omit [Finite M] in
theorem space_inf (H K : Subgroup (FreeAmalgam R)) : space (H ⊓ K) = space H ⊓ space K := by
  ext v
  rfl

omit [Finite M] in
theorem space_top : space (X R (alpha R)) = ⊤ := by
  change lattice ((X R (alpha R)).subgroupOf _) = ⊤
  rw [subgroupOf_self, lattice.map_top]

theorem disjoint_of_space_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    (hd : Disjoint (fixedSpace (Offenders.linearize (xAction source)) ⊤)
      (moving (Offenders.linearize (xAction source))).toSubmodule) :
    Disjoint (fixedPart R) (U R (alpha R)) := by
  rw [← space_fixed source, ← space_U_of_space_Z source geometry hb hZ] at hd
  apply disjoint_iff_inf_le.mpr
  intro u hu
  have hv : Additive.ofMul (⟨u, hu.1.1⟩ : X R (alpha R)) ∈
      space (fixedPart R) ⊓ space (U R (alpha R)) := hu
  have he := disjoint_iff_inf_le.mp hd hv
  exact congrArg (fun v : Additive (X R (alpha R)) => (v.toMul : FreeAmalgam R)) he

theorem X_eq_fixed_sup_U_of_centralSum_top (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    (htop : centralSum (Offenders.linearize (xAction source)) = ⊤) :
    X R (alpha R) = fixedPart R ⊔ U R (alpha R) := by
  have hZX : Z R (alpha R) = X R (alpha R) :=
    space_injective (geometry.omega_bound (alpha R) rfl hb) le_rfl
      (hZ.trans (htop.trans space_top.symm))
  exact hZX.symm.trans (Z_eq_fixed_sup_U_of_space_Z source geometry hb hZ)

theorem central_kernel_card_of_finrank (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    (hk : Module.finrank (ZMod 2)
      (fixedSpace (Offenders.linearize (xAction source)) ⊤ ⊓
        (moving (Offenders.linearize (xAction source))).toSubmodule :
          Submodule (ZMod 2) (Additive (X R (alpha R)))) = 1) :
    Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) = 2 := by
  let := finite_X R (alpha R)
  rw [space_card (inf_le_left.trans (show fixedPart R ≤ X R (alpha R) from inf_le_left)),
    space_inf, space_fixed source, space_U_of_space_Z source geometry hb hZ,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hk]
  decide

theorem Z_index_two_of_finrank (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    (hq : Module.finrank (ZMod 2) (Additive (X R (alpha R)) ⧸
      centralSum (Offenders.linearize (xAction source))) = 1) :
    (Z R (alpha R)).relIndex (X R (alpha R)) = 2 := by
  let := finite_X R (alpha R)
  let := finite_Z R (alpha R)
  have hd := (space (Z R (alpha R))).finrank_quotient_add_finrank
  have hq' : Module.finrank (ZMod 2) (Additive (X R (alpha R)) ⧸ space (Z R (alpha R))) = 1 := by
    rw [hZ]
    exact hq
  rw [hq'] at hd
  have hc : Nat.card (X R (alpha R)) = 2 * Nat.card (Z R (alpha R)) := by
    have hx := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X R (alpha R)))
    have hz := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := space (Z R (alpha R)))
    rw [Nat.card_zmod] at hx hz
    change Nat.card (X R (alpha R)) = _ at hx
    rw [hx, space_card (geometry.omega_bound (alpha R) rfl hb), hz, ← hd, pow_add, pow_one]

  have hi := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R (alpha R)) (X R (alpha R)) bot_le (geometry.omega_bound (alpha R) rfl hb)
  rw [relIndex_bot_left, relIndex_bot_left, hc, mul_comm 2] at hi
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hi

/-- Final source conversion of the abstract attachment classification. Its one
remaining premise is the edge fixed-generation identity for the actual Z. -/
theorem alternatives_of_space_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source))) :
    Alternatives source := by
  let := finite_X R (alpha R)
  let ρ := Offenders.linearize (xAction source)
  rcases CentralAttachments.classification ρ (xAction_injective source geometry hb)
      (xAction_isFFModule source geometry hb) with
    ⟨⟨e⟩, he⟩ | ⟨⟨e⟩, he⟩ | ⟨⟨q⟩, hsum, hk⟩ | ⟨⟨e⟩, hd, hq⟩
  · have hd := disjoint_of_space_Z source geometry hb hZ he.disjoint
    exact Or.inl ⟨⟨(quotientOnU source geometry hb hZ e.toQuotient).oneNatural source hd⟩,
      X_eq_fixed_sup_U_of_centralSum_top source geometry hb hZ he.sup_eq_top, hd⟩
  · exact Or.inr (Or.inl ⟨⟨copiesOnU source geometry hb hZ e⟩,
      X_eq_fixed_sup_U_of_centralSum_top source geometry hb hZ he.sup_eq_top,
      disjoint_of_space_Z source geometry hb hZ he.disjoint⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨quotientOnU source geometry hb hZ q⟩,
      X_eq_fixed_sup_U_of_centralSum_top source geometry hb hZ hsum,
      central_kernel_card_of_finrank source geometry hb hZ hk⟩))
  · have hdis := disjoint_of_space_Z source geometry hb hZ hd
    exact Or.inr (Or.inr (Or.inr
      ⟨⟨(quotientOnU source geometry hb hZ e.toQuotient).oneNatural source hdis⟩,
        Z_eq_fixed_sup_U_of_space_Z source geometry hb hZ, hdis,
        Z_index_two_of_finrank source geometry hb hZ hq⟩))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Reconstruction
