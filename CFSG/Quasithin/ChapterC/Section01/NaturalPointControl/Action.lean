module

public import Theory.Representation.PSL3Two.PointOffenders
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Basic
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.NormalElementaryQuotient

/-!
# The actual natural-point action and its full preimages

A compatible natural module marking identifies the action kernel with O₂(G).
The inverse images of the three displayed cyclic root groups are conjugate
under O²(G). Every point-radical subgroup has equal weight, so there are no
strong offenders and the action kernel has full two-rank in the point radical.
Consequently each cyclic root preimage has that same two-rank. All maps are
the given quotient projection and actual subgroup inclusions.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, especially the
natural-point application of B.2.19 on p.143.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalPointControl
open ChapterB ChapterB.BaumannArgument
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace Geometry
abbrev Vector := Matrix.PSL3Two.PointOffenders.Vector
end Geometry
variable {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

structure NaturalAction where
  q : G →* SL
  onto : Function.Surjective q
  kernel : q.ker = pCore 2 G
  coordinates : V ≃* Multiplicative Geometry.Vector
  action : ∀ g v, (coordinates (MulAut.conjNormal g v)).toAdd =
    q g • (coordinates v).toAdd

namespace NaturalAction
variable {V} (d : NaturalAction V)

def R : Subgroup G := pointV.comap d.q

def D (i : Fin 3) : Subgroup G := (zpowers (PointOffenders.root i)).comap d.q

omit [IsElementaryAbelian 2 V] in
theorem kernel_centralizer : d.q.ker = centralizer (V : Set G) := by
  ext g
  constructor
  · intro hg
    apply mem_centralizer_iff.mpr
    intro v hv
    have h : MulAut.conjNormal g (⟨v,hv⟩ : V) = ⟨v,hv⟩ := by
      apply d.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [d.action, show d.q g = 1 from hg, one_smul]
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)).symm
  · intro hg
    have hfix (v : Geometry.Vector) : d.q g • v = v := by
      let u := d.coordinates.symm (Multiplicative.ofAdd v)
      have hc : MulAut.conjNormal g u = u := by
        apply Subtype.ext
        change g * (u:G) * g⁻¹ = u
        rw [← mem_centralizer_iff.mp hg u u.property, mul_inv_cancel_right]
      have hh := d.action g u
      rw [hc, d.coordinates.apply_symm_apply] at hh
      exact hh.symm
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    exact (hfix v).trans (Matrix.one_mulVec v).symm

def addCoordinates : Additive V ≃+ Geometry.Vector where
  toFun v := (d.coordinates v.toMul).toAdd
  invFun v := Additive.ofMul (d.coordinates.symm (Multiplicative.ofAdd v))
  left_inv v := d.coordinates.symm_apply_apply v
  right_inv v := d.coordinates.apply_symm_apply (Multiplicative.ofAdd v)
  map_add' v w := d.coordinates.map_mul v.toMul w.toMul

noncomputable def linearCoordinates : Additive V ≃ₗ[ZMod 2] Geometry.Vector :=
  { d.addCoordinates with map_smul' := ZMod.map_smul d.addCoordinates }

noncomputable def ρ : Representation (ZMod 2) SL (Additive V) :=
  Representation.NormalElementaryQuotient.representation V d.q d.onto d.kernel_centralizer

theorem equivariant (g : SL) (v : Additive V) :
    d.linearCoordinates (d.ρ g v) = BinaryLinearThree.W g (d.linearCoordinates v) := by
  obtain ⟨a,rfl⟩ := d.onto g
  have he := Representation.NormalElementaryQuotient.representation_apply
    V d.q d.onto d.kernel_centralizer a v
  have hc : (d.ρ (d.q a) v).toMul = MulAut.conjNormal a v.toMul := Subtype.ext he
  change (d.coordinates _).toAdd = _
  rw [hc]
  exact d.action a v.toMul

theorem fixed_finrank (E : Subgroup SL) :
    Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace d.ρ E) =
      Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace BinaryLinearThree.W E) := by
  have he := Representation.BinaryOffender.fixedSpace_map_equivariant d.ρ BinaryLinearThree.W
    (MonoidHom.id SL) d.linearCoordinates d.equivariant E
  rw [map_id] at he
  exact ((Submodule.equivMapOfInjective d.linearCoordinates.toLinearMap
    d.linearCoordinates.injective _).trans (LinearEquiv.ofEq _ _ he)).finrank_eq

theorem equalWeightLE {A B : Subgroup SL} (hA : A ≤ pointV) (hBA : B ≤ A) :
    Representation.BinaryOffender.EqualWeightLE d.ρ B A := by
  refine ⟨hBA, ?_⟩
  simp only [Representation.BinaryOffender.weight, d.fixed_finrank]
  exact (PointOffenders.equalWeightLE_of_le hA hBA).2

include d in
omit [IsElementaryAbelian 2 V] in
theorem module_card : Nat.card V = 8 := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  change Nat.card Geometry.Vector = 8
  simp [Geometry.Vector, PointOffenders.Vector]

variable [Finite G]

theorem fixed_card (A : Subgroup G) :
    Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card (PointOffenders.fixed (A.map d.q)) := by
  have h1 := Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv
    V d.q d.onto d.kernel_centralizer A)
  rw [← h1]
  change Nat.card (Representation.BinaryOffender.fixedSpace d.ρ (A.map d.q)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), d.fixed_finrank]
  rw [← Module.natCard_eq_pow_finrank (K := ZMod 2)]
  exact PointOffenders.fixedSpace_card _

theorem fixedCodim_eq_rank (A : Subgroup G) (hA : A ≤ d.R) :
    fixedCodim V A = Representation.BinaryOffender.rank (A.map d.q) := by
  have he : A.map d.q ≤ pointV := map_le_iff_le_comap.mpr hA
  have hs := PointOffenders.fixed_rank_sum (A.map d.q) he
  rw [fixedCodim, d.module_card, d.fixed_card]
  have hf := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Representation.BinaryOffender.fixedSpace BinaryLinearThree.W (A.map d.q))
  rw [Nat.card_zmod, PointOffenders.fixedSpace_card] at hf
  rw [hf, Nat.log_pow Nat.one_lt_two]
  change 3 - _ = _
  omega

omit [Finite G] in
noncomputable def actionEquiv : (G ⧸ centralizer (V : Set G)) ≃* SL :=
  (QuotientGroup.quotientMulEquivOfEq d.kernel_centralizer.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.q d.onto)

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem actionEquiv_apply (g : G) : d.actionEquiv (actionMap V g) = d.q g := rfl

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem image_eq (A : Subgroup G) :
    (A.map (actionMap V)).map d.actionEquiv.toMonoidHom = A.map d.q := by
  rw [map_map]
  rfl

theorem noStrongOffenders : NoStrongOffenders V d.R := by
  intro A hA _ _
  have hc : Nat.card (A.map (actionMap V)) = Nat.card (A.map d.q) := by
    rw [← d.image_eq A, card_map_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective]
  rw [hc, d.fixedCodim_eq_rank A hA]
  rfl


omit [Finite G] [IsElementaryAbelian 2 V] in
theorem kernel_le_R : d.q.ker ≤ d.R := by
  intro g hg
  change d.q g ∈ pointV
  rw [show d.q g = 1 from hg]
  exact one_mem _

omit [Finite G] in
theorem module_le_R : V ≤ d.R := by
  exact V.le_centralizer.trans (d.kernel_centralizer ▸ d.kernel_le_R)

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem R_two : IsPGroup 2 d.R :=
  (IsPGroup.of_card (n := 2) card_pointV).comap_of_ker_isPGroup d.q
    (d.kernel.symm ▸ pCore_isPGroup)

omit [IsElementaryAbelian 2 V] in
theorem residual_image : (pResidual 2 G).map d.q = ⊤ := by
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 3) :=
    BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect SL := Group.IsPerfect.ofSurjective
    (f := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom)
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective
  rw [map_pResidual_of_surjective 2 d.q d.onto]
  apply (pResidual_eq_top_iff 2 SL).mpr
  intro N hN hp
  let := hN
  have hs : Subsingleton (SL ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (SL ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

omit [IsElementaryAbelian 2 V] in
theorem residual_surjective : Function.Surjective (d.q.comp (pResidual 2 G).subtype) := by
  intro g
  obtain ⟨l,hl,he⟩ := show g ∈ (pResidual 2 G).map d.q from d.residual_image.symm ▸ mem_top g
  exact ⟨⟨l,hl⟩,he⟩

theorem centralizer_rank : twoRank d.q.ker = twoRank d.R := by
  have hr := (centralizer_rank_and_alpha V d.R d.module_le_R d.noStrongOffenders).1
  rwa [← d.kernel_centralizer, inf_eq_right.mpr d.kernel_le_R] at hr

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem D_image (i : Fin 3) : (d.D i).map d.q = zpowers (PointOffenders.root i) :=
  by rw [D, map_comap_eq, MonoidHom.range_eq_top.mpr d.onto, top_inf_eq]

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem D_kernel (i : Fin 3) : d.q.ker ≤ d.D i := by
  intro x hx
  change d.q x ∈ zpowers _
  rw [show d.q x = 1 from hx]
  exact one_mem _

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem D_zero_le_R : d.D 0 ≤ d.R := by
  apply comap_mono
  apply zpowers_le.mpr
  rw [← PointOffenders.row_range]
  exact ⟨Multiplicative.ofAdd (1,0),rfl⟩

private theorem rank_mono {A B : Subgroup G} (h : A ≤ B) : twoRank A ≤ twoRank B :=
  Nat.log_mono_right (elementaryAbelianMaxOrder_le_and_j_le_of_eq A B h).1

theorem D_zero_rank : twoRank (d.D 0) = twoRank d.R := by
  apply le_antisymm (rank_mono d.D_zero_le_R)
  rw [← d.centralizer_rank]
  exact rank_mono (d.D_kernel 0)


omit [Finite G] [IsElementaryAbelian 2 V] in
theorem preimage_conjugate (E : Subgroup SL) (g : G) :
    (E.comap d.q).map (MulAut.conj g).toMonoidHom =
      (E.map (MulAut.conj (d.q g)).toMonoidHom).comap d.q := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨d.q y,hy,by simp⟩
  · rintro ⟨y,hy,he⟩
    refine ⟨g⁻¹*x*g, ?_, by dsimp; group⟩
    change d.q (g⁻¹*x*g) ∈ E
    have hx : d.q x = d.q g * y * (d.q g)⁻¹ := he.symm
    rw [map_mul, map_mul, map_inv, hx]
    have hh : (d.q g)⁻¹ * (d.q g * y * (d.q g)⁻¹) * d.q g = y := by group
    rw [hh]
    exact hy

omit [IsElementaryAbelian 2 V] in
theorem D_conjugate (i : Fin 3) :
    ∃ l ∈ pResidual 2 G, (d.D 0).map (MulAut.conj l).toMonoidHom = d.D i := by
  obtain ⟨l,hl⟩ := d.residual_surjective (PointOffenders.cycle ^ i.val)
  refine ⟨l,l.property,?_⟩
  change ((zpowers (PointOffenders.root 0)).comap d.q).map _ = _
  rw [d.preimage_conjugate, MonoidHom.map_zpowers, show d.q l = PointOffenders.cycle ^ i.val from hl]
  change (zpowers (MulAut.conj (PointOffenders.cycle ^ i.val) (PointOffenders.root 0))).comap d.q = _
  rw [PointOffenders.root_conjugate]
  rfl

theorem D_rank (i : Fin 3) : twoRank (d.D i) = twoRank d.R := by
  obtain ⟨l,_,hl⟩ := d.D_conjugate i
  rw [← hl, twoRank_map_equiv]
  exact d.D_zero_rank



end NaturalAction
end CFSG.Quasithin.ChapterC.NaturalPointControl
