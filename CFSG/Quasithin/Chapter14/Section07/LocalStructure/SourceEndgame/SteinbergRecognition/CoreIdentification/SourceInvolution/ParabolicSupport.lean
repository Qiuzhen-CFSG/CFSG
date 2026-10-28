module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.SourceMarking
public import Theory.Representation.ResidualMovedGeneration
public import Theory.Representation.PSL3Two.SteinbergStructure.Duality


/-!
# Steinberg commutator generation inside the actual parabolic residual

The compatible marking identifies the image of the original L₁, under the
inverse twist of the unchanged qL, with the embedded two-residual of the line
parabolic. Full commutator generation survives restriction to this residual:
the dual fixed space for a normal subgroup with two-group quotient cannot be
nonzero when the whole group's fixed space vanishes. The checked Steinberg
automorphism equivalence handles the point/line twist.

Transporting these displacements through the original Steinberg coordinates
makes the image of [S,L₁] all of S/V. Frattini nongeneration then gives
[S,L₁]=S. Since S≤Q≤T and T normalizes L₁, this proves S≤L₁; normalization
of S by L₁ and the two-group property strengthen this to S≤O₂(L₁).

The explicit coordinates, Φ(S)=V, S≤Q and T-normalization inputs are earlier
72 conclusions, discharged by its enclosing source assembly. Neither S=O₂(L)
nor parabolic containment is assumed. The terminal Application leaf supplies
this containment to the existing source-involution consumer, retaining its
independent TorusGeometry input. This leaf imports SourceInvolution.Basic so
that the source-involution owner can import it without a cycle.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, first branch of
14.7.72 and opening proof of 14.7.73, printed p.1076 (PDF p.1093); H.6.3(5),
printed pp.387–388 (PDF pp.398–399).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.ParabolicSupport
open Chapter12.Section08 CriticalFusion.Source ModuleRecognition.ParabolicSeed

private theorem twisted_residual_commutator_eq_top (a : MulAut BinaryLinearThree.Group) :
    subspaceCommutator (BinaryLinearThree.S.comp a.toMonoidHom) ⊤
      ((pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
        Matrix.PSL3Two.lineParabolicSL.subtype) = ⊤ := by
  let e := BinaryLinearThree.SteinbergStructure.autEquiv a
  let K := (pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
    Matrix.PSL3Two.lineParabolicSL.subtype
  let C := subspaceCommutator (BinaryLinearThree.S.comp a.toMonoidHom) ⊤ K
  have hK : subspaceCommutator BinaryLinearThree.S ⊤ K = ⊤ :=
    commutator_pResidual_eq_top BinaryLinearThree.S _
      BinaryLinearThree.SteinbergStructure.LocalActions.line_commutator_eq_top
  have hmap : ∀ w ∈ subspaceCommutator BinaryLinearThree.S ⊤ K, e.toIntertwiningMap w ∈ C := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, hg, v, _, rfl⟩ := hw
      rw [map_sub, e.toIntertwiningMap.isIntertwining]
      exact Submodule.subset_span ⟨g, hg, e v, Submodule.mem_top, rfl⟩
    | zero => simpa only [map_zero] using C.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using C.add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using C.smul_mem c hx
  apply top_unique
  intro v _
  obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective v
  exact hmap w (hK.symm ▸ Submodule.mem_top)

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

private theorem coordinates_commutator_onto (c : SteinbergCoordinates d)
    (b : Marking d) :
    ((⁅S F L,F.Li L 1⁆).subgroupOf (S F L)).map
      (N := Multiplicative BinaryLinearThree.Steinberg) c.coordinates = ⊤ := by
  let C := (⁅S F L,F.Li L 1⁆).subgroupOf (S F L)
  let X : Submodule (ZMod 2) BinaryLinearThree.Steinberg :=
    AddSubgroup.toZModSubmodule 2 (C.map c.coordinates).toAddSubgroup'
  have hdisp (g : BinaryLinearThree.Group)
      (hg : g ∈ (pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
        Matrix.PSL3Two.lineParabolicSL.subtype)
      (v : BinaryLinearThree.Steinberg) :
      BinaryLinearThree.S (b.twist g) v - v ∈ X := by
    rw [← b.residual d] at hg
    obtain ⟨l, hl, he⟩ := hg
    have hq : d.qL l = b.twist g := by
      apply b.twist.symm.injective
      exact he.trans (b.twist.symm_apply_apply g).symm
    obtain ⟨a, ha⟩ := c.onto (Multiplicative.ofAdd v)
    let a' : S F L := ⟨l * a * (l : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_S l.property) a).mp a.property⟩
    change Multiplicative.ofAdd (BinaryLinearThree.S (b.twist g) v - v) ∈ C.map c.coordinates
    refine ⟨a' * a⁻¹, ?_, ?_⟩
    · change (l : G) * a * (l : G)⁻¹ * (a : G)⁻¹ ∈ ⁅S F L,F.Li L 1⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hl a.property
    · apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv]
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, ← sub_eq_add_neg]
      rw [c.equivariant l a, ha, hq]
      rfl
  have hX : X = ⊤ := by
    apply top_unique
    rw [← twisted_residual_commutator_eq_top b.twist]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    exact hdisp g hg v
  apply top_unique
  intro v _
  have hv : v.toAdd ∈ X := by rw [hX]; trivial
  exact hv

/-- H.6.3(5), restricted to the actual two-residual and lifted through Φ(S),
gives generation by the original first flag actor. -/
theorem S_commutator_parabolic_eq (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ⁅S F L,F.Li L 1⁆ = S F L := by
  obtain ⟨b⟩ := nonempty_marking d hTL
  have hCS : ⁅S F L,F.Li L 1⁆ ≤ S F L :=
    le_normalizer_iff_commutator_le_left.mp
      (((F.Li_le L 1).trans inf_le_left).trans L_normalizes_S)
  let C := (⁅S F L,F.Li L 1⁆).subgroupOf (S F L)
  have hPhi' : frattini (S F L) = V.subgroupOf (S F L) := by
    have he := congrArg (fun A : Subgroup G => A.subgroupOf (S F L)) hPhi
    simpa only [subgroupOf, comap_map_eq_self_of_injective (S F L).subtype_injective] using he
  have htop : C ⊔ frattini (S F L) = ⊤ := by
    rw [hPhi', ← c.kernel_eq]
    apply top_unique
    intro a _
    have ha : c.coordinates a ∈ C.map c.coordinates := by
      rw [coordinates_commutator_onto d c b]
      trivial
    obtain ⟨b, hb, he⟩ := ha
    have hba : b⁻¹ * a ∈ c.coordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he]
      exact inv_mul_cancel (c.coordinates a)
    have hh := (C ⊔ c.coordinates.ker).mul_mem (mem_sup_left hb) (mem_sup_right hba)
    simpa only [mul_inv_cancel_left] using hh
  have hC := frattini_nongenerating htop
  apply le_antisymm hCS
  intro a ha
  have hh : (⟨a,ha⟩ : S F L) ∈ C := by rw [hC]; trivial
  exact hh

/-- Generation and S≤Q≤T put the original S inside L₁. No identification
with O₂(L) is used. -/
theorem S_le_parabolic (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    S F L ≤ F.Li L 1 := by
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hSN : S F L ≤ normalizer (F.Li L 1 : Set G) := by
    change S F L ≤ normalizer
      (((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype) : Set G)
    apply (hSQ.trans hQT).trans
    apply LE.le.trans _ (normalizer_le_normalizer_characteristic_image
      (L ⊓ F.H) (pResidual 2 (L ⊓ F.H : Subgroup G)))
    exact (le_inf hTL ((F.invariant 1).trans F.H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [← S_commutator_parabolic_eq d c hPhi hTL]
  exact le_normalizer_iff_commutator_le_right.mp hSN

/-- The same S is a normal two-subgroup of the original L₁. -/
theorem S_le_parabolic_core (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    S F L ≤ (F.Li L 1).pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le hSQ)
    (S_le_parabolic d c hPhi hSQ hTL)
    (((F.Li_le L 1).trans inf_le_left).trans L_normalizes_S)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.ParabolicSupport
