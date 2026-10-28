module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Obstruction.Actor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Obstruction.Pairing.Construction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius

/-!
# From the radical of radius forms to the derived bound

Conjugation identifies the image of the moving radius in V/Z with elements
of the residual commutator subspace. If that subspace lies in the radical
of every invariant binary form, the separating forms of the actual pairing
modulo U give [Vcirc,V] ≤ U. The source generation V = Vcirc ∨ V_b and the
abelianness of the incident radius V_b then give V' ≤ U.

This is the conditional binary pairing reduction for Meierfrankenfeld–
Stellmacher (1993), (4.6.2), printed pp.901–902. The form-radical premise
remains with the obstruction assembly; no center bound or trivial action
of the vertex kernel is assumed here.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The moving radius maps into the residual commutator subspace for the
published conjugation representation on the literal V/Z. -/
private theorem moving_mem_subspaceCommutator [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) (x : V R a)
    (hx : (x : FreeAmalgam R) ∈ Vcirc R a) :
    letI := radiusZ_normal common a ha
    letI := radiusQuotient_elementary common hb a ha
    Additive.ofMul (QuotientGroup.mk' ((Z R a).subgroupOf (V R a)) x) ∈
      subspaceCommutator (radiusRepresentation common hb a ha) ⊤
        (pResidual 2 (stabilizer R a)) := by
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  let q := QuotientGroup.mk' ((Z R a).subgroupOf (V R a))
  let D := subspaceCommutator (radiusRepresentation common hb a ha) ⊤
    (pResidual 2 (stabilizer R a))
  let K := (Subgroup.toAddSubgroup.symm D.toAddSubgroup).comap q
  have hVK : Vcirc R a ≤ K.map (V R a).subtype := by
    rw [Vcirc, commutator_comm]
    apply commutator_le.mpr
    intro g hg v hv
    obtain ⟨g, hg, rfl⟩ := hg
    let v' : V R a := ⟨v, hv⟩
    let c : V R a := ⟨(g : FreeAmalgam R) * v * (g : FreeAmalgam R)⁻¹,
      (mem_normalizer_iff.mp (V_normalized a g.property) v).mp hv⟩
    have hc : (c * v'⁻¹ : V R a).val = ⁅(g : FreeAmalgam R),v⁆ := rfl
    refine ⟨c * v'⁻¹, ?_, hc⟩
    change Additive.ofMul (q (c * v'⁻¹)) ∈ D
    have hm : radiusRepresentation common hb a ha g (Additive.ofMul (q v')) -
        Additive.ofMul (q v') ∈ D :=
      Submodule.subset_span ⟨g, hg, Additive.ofMul (q v'), Submodule.mem_top, rfl⟩
    have he : radiusRepresentation common hb a ha g (Additive.ofMul (q v')) -
        Additive.ofMul (q v') = Additive.ofMul (q (c * v'⁻¹)) := by
      rw [radiusRepresentation_apply]
      change Additive.ofMul (radiusQuotientAction common a ha g
        (QuotientGroup.mk' ((Z R a).subgroupOf (V R a)) v')) -
          Additive.ofMul (q v') = _
      rw [radiusQuotientAction_apply]
      change Additive.ofMul (q c) - Additive.ofMul (q v') = _
      simp only [map_mul, map_inv, sub_eq_add_neg]
      rfl
    rwa [he] at hm
  obtain ⟨y, hy, he⟩ := hVK hx
  have hyx : y = x := Subtype.ext he
  subst y
  exact hy

/-- If every residual-invariant binary form has the residual moved space
in its radical, the actual moving radius centralizes V modulo U. -/
theorem radius_moving_commutator_le_U_of_form_radical [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hrad : letI := radiusZ_normal common a ha
      letI := radiusQuotient_elementary common hb a ha
      ∀ B : LinearMap.BilinForm (ZMod 2)
          (Additive ((V R a) ⧸ (Z R a).subgroupOf (V R a))),
        (∀ g : stabilizer R a, g ∈ pResidual 2 (stabilizer R a) →
          ∀ v w, B (radiusRepresentation common hb a ha g v)
            (radiusRepresentation common hb a ha g w) = B v w) →
        ∀ v ∈ subspaceCommutator (radiusRepresentation common hb a ha) ⊤
          (pResidual 2 (stabilizer R a)), ∀ w, B v w = 0) :
    ⁅Vcirc R a, V R a⁆ ≤ U R a := by
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  obtain ⟨forms, hinv, hsep⟩ := radius_commutator_forms common hb a ha
  have hmov : Vcirc R a ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  apply commutator_le.mpr
  intro x hx y hy
  apply (hsep ⟨x, hmov hx⟩ ⟨y, hy⟩).mp
  intro B hB
  exact hrad B (hinv B hB) _
    (moving_mem_subspaceCommutator common hb a ha ⟨x, hmov hx⟩ hx) _

/-- The binary form-radical reduction of the derived-radius containment.
The moving radius centralizes V modulo U, and the incident radius is abelian;
together they generate V. No center-containment premise or trivial Q-action
is required. The invariant-form hypothesis is discharged by the separate
representation-theoretic argument in the obstruction assembly. -/
theorem radius_derived_le_U_of_form_radical [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hrad : letI := radiusZ_normal common a ha
      letI := radiusQuotient_elementary common hb a ha
      ∀ B : LinearMap.BilinForm (ZMod 2)
          (Additive ((V R a) ⧸ (Z R a).subgroupOf (V R a))),
        (∀ g : stabilizer R a, g ∈ pResidual 2 (stabilizer R a) →
          ∀ v w, B (radiusRepresentation common hb a ha g v)
            (radiusRepresentation common hb a ha g w) = B v w) →
        ∀ v ∈ subspaceCommutator (radiusRepresentation common hb a ha) ⊤
          (pResidual 2 (stabilizer R a)), ∀ w, B v w = 0) :
    ⁅V R a, V R a⁆ ≤ U R a := by
  have hm := radius_moving_commutator_le_U_of_form_radical common hb a ha hrad
  have hmov : Vcirc R a ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have he := NaturalStructure.Exclusion.edge_radius_le_radius ha hab
  have hgen := NaturalStructure.Exclusion.radius_eq_moving_sup_edge source ha hab
  have hn : V R a ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    ((radius_le_Q common a ha).trans (fun _ hx => hx.1)).trans (U_normalized a)
  have hee : ⁅V R b, V R b⁆ ≤ U R a := by
    have hc := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr
        (NaturalStructure.Exclusion.edge_radius_commutative geometry common.large_distance a b ha hab))
    exact hc.le.trans bot_le
  have hVe : ⁅V R a, V R b⁆ ≤ U R a := by
    have hle : V R a ≤ commutatorPreimage (V R a) (V R b) (U R a) :=
      hgen.le.trans (sup_le
        (le_commutatorPreimage hmov ((commutator_mono le_rfl he).trans hm))
        (le_commutatorPreimage he hee))
    exact (commutator_mono hle le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hn)
  have hle : V R a ≤ commutatorPreimage (V R a) (V R a) (U R a) := by
    apply hgen.le.trans
    apply sup_le (le_commutatorPreimage hmov hm)
    apply le_commutatorPreimage he
    rwa [commutator_comm]
  exact (commutator_mono hle le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hn)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
