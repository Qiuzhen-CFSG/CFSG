module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Basic
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer.Quotient.Core

/-!
# Faithfulness of the actual source cubic normalizer

The original centralizer in A is transported to the native cubic fixed
subgroup. An element acting trivially on A lies in A by the source
self-centralizer theorem; fixedness and centrality then force it to be one.
The inner-action formula retains the literal lifts needed for F.1.12.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
open Centralizers.Choices ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}
    {B5:Sylow 5 d.toTypeRuSetup.H} (m:SecondCubicMarking (p:=p) B5)

def fixedEquiv : (p.A B5⊓centralizer (p.cubicSubgroup m.X:Set G):Subgroup G)≃CubicAction.fixedCore where
  toFun a:=⟨m.coordinates ⟨a,a.property.1⟩,(m.fixed_iff_mem_centralizer ⟨a,a.property.1⟩).mpr a.property.2⟩
  invFun a:=⟨m.coordinates.symm a,(m.coordinates.symm a).property,
    (m.fixed_iff_mem_centralizer (m.coordinates.symm a)).mp
      (by rw [m.coordinates.apply_symm_apply];exact a.property)⟩
  left_inv a:=Subtype.ext (congrArg (fun z:p.A B5=>(z:G)) (m.coordinates.symm_apply_apply _))
  right_inv a:=Subtype.ext (m.coordinates.apply_symm_apply _)

theorem fixed_card : Nat.card (p.A B5⊓centralizer (p.cubicSubgroup m.X:Set G):Subgroup G)=8 :=
  (Nat.card_congr m.fixedEquiv).trans CubicAction.fixedCore_card

theorem normalizer_inf_core : secondCubicNormalizer B5 m.X⊓p.A B5=
    p.A B5⊓centralizer (p.cubicSubgroup m.X:Set G) := by
  have hn:p.cubicSubgroup m.X≤normalizer (p.A B5:Set G):=
    (map_subtype_le _).trans (p.A_normalized B5)
  have hd:Disjoint (p.A B5) (p.cubicSubgroup m.X):=
    IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ (p.A_isPGroup B5)
      (m.X.isPGroup'.map p.parabolic.subtype)
  have he:=SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf (p.A B5) (p.cubicSubgroup m.X) hn hd
  ext a
  constructor
  · rintro ⟨ha,hA⟩
    exact he.le ⟨hA,ha.2⟩
  · rintro ⟨hA,hC⟩
    exact ⟨⟨p.A_le_F₂ B5 m.X hA,(Subgroup.centralizer_le_normalizer _) hC⟩,hA⟩

theorem native_fixed_lift_mem (a:CubicAction.fixedCore) :
    (m.coordinates.symm a:G)∈secondCubicNormalizer B5 m.X := by
  refine ⟨p.A_le_F₂ B5 m.X (m.coordinates.symm a).property,?_⟩
  apply Subgroup.centralizer_le_normalizer
  apply (m.fixed_iff_mem_centralizer (m.coordinates.symm a)).mp
  rw [m.coordinates.apply_symm_apply]
  exact a.property

theorem action_core (a:p.A B5) (ha:(a:G)∈secondCubicNormalizer B5 m.X) :
    secondCubicNormalizerAction B5 m.X m.coordinates ⟨a,ha⟩=MulAut.conj (m.coordinates a) := by
  apply MulEquiv.ext
  intro b
  apply m.coordinates.symm.injective
  change m.coordinates.symm (secondCubicNormalizerAction B5 m.X m.coordinates ⟨a,ha⟩ b)=
    m.coordinates.symm (m.coordinates a*b*(m.coordinates a)⁻¹)
  simp only [map_mul,map_inv,m.coordinates.symm_apply_apply]
  apply Subtype.ext
  have hh:=secondCoreAction_apply B5 m.coordinates
    (⟨a,(p.F₂_le_parabolic B5 m.X) ha.1⟩:p.parabolic) (m.coordinates.symm b)
  rw [m.coordinates.apply_symm_apply] at hh
  exact hh

theorem action_injective : Function.Injective (secondCubicNormalizerAction B5 m.X m.coordinates) := by
  apply (MonoidHom.ker_eq_bot_iff (secondCubicNormalizerAction B5 m.X m.coordinates)).mp
  apply eq_bot_iff.mpr
  intro z hz
  change secondCubicNormalizerAction B5 m.X m.coordinates z=1 at hz
  let zP:p.parabolic:=⟨z,(p.F₂_le_parabolic B5 m.X) z.property.1⟩
  have hC:(z:G)∈centralizer (p.A B5:Set G):=by
    intro a ha
    let aA:p.A B5:=⟨a,ha⟩
    have hh:=secondCoreAction_apply B5 m.coordinates zP aA
    have hf:=DFunLike.congr_fun hz (m.coordinates aA)
    change secondCoreAction B5 m.coordinates zP (m.coordinates aA)=m.coordinates aA at hf
    rw [hf,m.coordinates.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hA:(z:G)∈p.A B5:=p.centralizer_le_of_plane_le (p.F₂_le_parabolic B5 m.X)
    (p.le_seed.trans (p.V_le_S₂.trans (p.S₂_le_A B5)))
    (p.F₂_inf_R₂ B5 m.X m.quotient) ⟨z.property.1,hC⟩
  let a:p.A B5:=⟨z,hA⟩
  have hfix:CubicAction.cubic (m.coordinates a)=m.coordinates a:=
    (m.fixed_iff_mem_centralizer a).mpr ((m.normalizer_inf_core).le ⟨z.property,hA⟩).2
  have hcomm:Commute (m.coordinates a) (CubicAction.orbit 0):=by
    have hc:Commute a (m.coordinates.symm (CubicAction.orbit 0)):=by
      apply Subtype.ext
      exact (hC _ (m.coordinates.symm (CubicAction.orbit 0)).property).symm
    have hh:=hc.map m.coordinates.toMonoidHom
    change Commute (m.coordinates a) (m.coordinates (m.coordinates.symm (CubicAction.orbit 0))) at hh
    simpa only [m.coordinates.apply_symm_apply] using hh
  have he:m.coordinates a=1:=CollectedBitVectors.cubic_fixed_eq_one_of_commute _ hfix hcomm
  have ha:a=1:=m.coordinates.injective (he.trans m.coordinates.map_one.symm)
  exact Subtype.ext (congrArg (fun b:p.A B5=>(b:G)) ha)

theorem generator_mem : ((m.generator:p.parabolic):G)∈secondCubicNormalizer B5 m.X := by
  have hx:((m.generator:p.parabolic):G)∈p.cubicSubgroup m.X :=
    ⟨m.generator,m.generator.property,rfl⟩
  have hF:p.cubicSubgroup m.X≤p.F₂ B5 m.X:=le_sup_right.trans le_sup_left
  exact ⟨hF hx,(p.cubicSubgroup m.X).le_normalizer hx⟩

theorem action_generator_normalizer :
    secondCubicNormalizerAction B5 m.X m.coordinates ⟨((m.generator:p.parabolic):G),m.generator_mem⟩=
      CubicAction.cubic := m.action_generator

end CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
