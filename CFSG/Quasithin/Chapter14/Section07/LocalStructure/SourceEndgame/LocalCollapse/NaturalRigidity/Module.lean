module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Elementary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Escape
public import Theory.Representation.BinaryConjugationSection.CentralKernel
public import Theory.Representation.FirstCohomologyBounds
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The actual natural extension and its connecting map

The first Gaschütz bound makes QC centralize S. Hence conjugation on the
original QC descends through the original map d.qL, whose kernel is S.
When C_Q(L)=1, Elementary supplies its binary vector-space structure.
The original natural coordinates identify V inside this representation.
The connecting map embeds the literal QC/V into natural first cohomology,
whose dimension is one. A proper extension therefore has dimension four.

The parabolic actor below is exactly O₂(L₁), included into L before applying
d.qL. Its linear displacement is transported to the literal group
commutator and applied to Escape.false_of_QC_parabolic_displacement. The
proof that this displacement equals V is still a separate obligation;
the H¹ dimension calculation alone does not supply it.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.7.74, printed p.1077; I.1.6 and B.4.8(3).
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)

variable [IsElementaryAbelian 2 (QC T L V)]
  (hKC : ⁅QC T L V, K F⁆ ≤ F.U)

include a hKC in
/-- Conjugation descends through the original qL because its kernel S centralizes QC. -/
theorem exists_action : ∃ ρ : Representation (ZMod 2) BinaryLinearThree.Group
    (Additive (QC T L V)), ∀ (l : L) (x : Additive (QC T L V)),
      ((ρ (d.qL l) x).toMul : G) = l * x.toMul * (l : G)⁻¹ := by
  apply BinaryConjugationSection.exists_action_of_central_kernel L (QC T L V)
    (le_sup_left.trans (LT_normalizes_QC d a)) d.qL d.qL_surjective
  intro l hl
  have hs : (l : G) ∈ S L F := by
    rw [d.qL_ker] at hl
    exact a.core.symm ▸ hl
  exact le_centralizer_iff.mp (QC_centralizes_S d a hKC) hs

/-- The actual conjugation action on QC, descended along the fixed source marking qL. -/
noncomputable def action : Representation (ZMod 2) BinaryLinearThree.Group
    (Additive (QC T L V)) := Classical.choose (exists_action d a hKC)

/-- The descended action agrees with literal ambient conjugation. -/
theorem action_apply (l : L) (x : Additive (QC T L V)) :
    (((action d a hKC) (d.qL l) x).toMul : G) = l * x.toMul * (l : G)⁻¹ :=
  Classical.choose_spec (exists_action d a hKC) l x

/-- The original V as a subrepresentation of the actual QC module. -/
noncomputable def naturalPart : Subrepresentation (action d a hKC) where
  toSubmodule := AddSubgroup.toZModSubmodule 2 (V.subgroupOf (QC T L V)).toAddSubgroup
  apply_mem_toSubmodule := by
    intro g x hx
    obtain ⟨l,rfl⟩ := d.qL_surjective g
    change (((action d a hKC) (d.qL l) x).toMul : G) ∈ V
    rw [action_apply]
    exact (mem_normalizer_iff.mp (d.natural.chosen.normalizes l.property) x.toMul).mp hx

/-- The original natural coordinates restricted to this literal subrepresentation. -/
noncomputable def naturalCoordinates : (naturalPart d a hKC).toSubmodule →ₗ[ZMod 2]
    BinaryLinearThree.Vector :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := fun x => (d.naturalCoordinates ⟨x.val.toMul,x.property⟩).toAdd
    map_zero' := congrArg Multiplicative.toAdd d.naturalCoordinates.map_one
    map_add' x y := congrArg Multiplicative.toAdd
      (d.naturalCoordinates.map_mul ⟨x.val.toMul,x.property⟩ ⟨y.val.toMul,y.property⟩) }

/-- The source coordinates identify the entire original natural subgroup. -/
theorem naturalCoordinates_bijective : Function.Bijective (naturalCoordinates d a hKC) := by
  constructor
  · intro x y hxy
    have hh : (⟨x.val.toMul,x.property⟩ : V) = ⟨y.val.toMul,y.property⟩ :=
      d.naturalCoordinates_bijective.1 hxy
    exact Subtype.ext (congrArg
      (fun v : V => Additive.ofMul (⟨v,V_le_QC d a v.property⟩ : QC T L V)) hh)
  · intro v
    obtain ⟨x,hx⟩ := d.naturalCoordinates_bijective.2 (Multiplicative.ofAdd v)
    exact ⟨⟨Additive.ofMul ⟨x,V_le_QC d a x.property⟩,x.property⟩, hx⟩

/-- The subrepresentation is the natural SL₃(2) module with the original orientation. -/
noncomputable def naturalEquiv : (naturalPart d a hKC).toRepresentation.Equiv
    BinaryLinearThree.W where
  toLinearEquiv := LinearEquiv.ofBijective _ (naturalCoordinates_bijective d a hKC)
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨l,rfl⟩ := d.qL_surjective g
    have hh := d.naturalCoordinates_equivariant l (⟨x.val.toMul,x.property⟩ : V)
    change (d.naturalCoordinates ⟨((action d a hKC) (d.qL l) x.val).toMul,_⟩).toAdd = _
    convert hh using 1
    · congr 2
      exact Subtype.ext (action_apply d a hKC l x.val)
    · rfl

/-- The defining commutator bound for QC makes the actual quotient QC/V trivial. -/
theorem trivialQuotient : OneCohomology.HasTrivialQuotient (naturalPart d a hKC) := by
  intro g x
  obtain ⟨l,rfl⟩ := d.qL_surjective g
  change ((((action d a hKC) (d.qL l) x).toMul / x.toMul : QC T L V) : G) ∈ V
  rw [Subgroup.coe_div, div_eq_mul_inv, action_apply]
  have h := QC_commutator_le (F := F) (L := L)
  rw [commutator_comm] at h
  exact commutator_le.mp h l l.property x.toMul x.toMul.property

/-- Vanishing of the literal C_Q(L) eliminates fixed vectors in the descended module. -/
theorem fixed_eq_bot (hQL : QL T L = ⊥) : OneCohomology.fixed (action d a hKC) = ⊥ := by
  apply bot_unique
  intro x hx
  have hxc : (x.toMul : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have hh := congrArg (fun y : Additive (QC T L V) => (y.toMul : G)) (hx (d.qL ⟨l,hl⟩))
    rw [action_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hxQL : (x.toMul : G) ∈ QL T L :=
    ⟨(commutatorPreimage_le _ _ _) x.toMul.property,hxc⟩
  have he : (x.toMul : G) = 1 := by rwa [hQL, mem_bot] at hxQL
  exact congrArg Additive.ofMul (Subtype.ext he)

/-- Transport first cohomology using the original natural coordinates. -/
noncomputable def cohomologyEquiv :
    OneCohomology.H1 (naturalPart d a hKC).toRepresentation ≃ₗ[ZMod 2]
      OneCohomology.H1 BinaryLinearThree.W :=
  OneCohomology.H1Congr _ _ (MulEquiv.refl _) (naturalEquiv d a hKC).toLinearEquiv
    (fun g x => LinearMap.congr_fun ((naturalEquiv d a hKC).isIntertwining' g) x)

/-- The connecting map from the actual QC/V into natural first cohomology. -/
noncomputable def connectingMap :
    ((Additive (QC T L V)) ⧸ (naturalPart d a hKC).toSubmodule) →ₗ[ZMod 2]
      OneCohomology.H1 BinaryLinearThree.W :=
  (cohomologyEquiv d a hKC).toLinearMap.comp
    (OneCohomology.quotientToH1 _ (trivialQuotient d a hKC))

/-- No fixed vectors means no extra kernel in the connecting map. -/
theorem connectingMap_injective (hQL : QL T L = ⊥) :
    Function.Injective (connectingMap d a hKC) :=
  (cohomologyEquiv d a hKC).injective.comp
    (OneCohomology.quotientToH1_injective _ (trivialQuotient d a hKC)
      (fixed_eq_bot d a hKC hQL))

/-- The natural H¹ calculation bounds the dimension of the actual quotient QC/V. -/
theorem quotient_finrank_le_one (hQL : QL T L = ⊥) :
    Module.finrank (ZMod 2)
      ((Additive (QC T L V)) ⧸ (naturalPart d a hKC).toSubmodule) ≤ 1 := by
  have h := OneCohomology.finrank_le_H1_of_linearEquiv (action d a hKC)
    (naturalPart d a hKC) (trivialQuotient d a hKC) (fixed_eq_bot d a hKC hQL)
    (LinearEquiv.refl (ZMod 2) _)
  rw [(cohomologyEquiv d a hKC).finrank_eq,
    OneCohomology.SLHigherNatural.finrank_H1_sl3_two] at h
  exact h

/-- The original natural layer has dimension three. -/
theorem naturalPart_finrank : Module.finrank (ZMod 2) (naturalPart d a hKC).toSubmodule = 3 :=
  (naturalEquiv d a hKC).toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))

include a hKC in
/-- The connecting-map bound gives dimension at most four upstairs. -/
theorem QC_finrank_le_four (hQL : QL T L = ⊥) :
    Module.finrank (ZMod 2) (Additive (QC T L V)) ≤ 4 := by
  have h := (naturalPart d a hKC).toSubmodule.finrank_quotient_add_finrank
  rw [naturalPart_finrank d a hKC] at h
  have hb := quotient_finrank_le_one d a hKC hQL
  omega

include a hKC in
/-- A proper extension of the original V has dimension exactly four. -/
theorem QC_finrank_eq_four (hQL : QL T L = ⊥) (hlt : V < QC T L V) :
    Module.finrank (ZMod 2) (Additive (QC T L V)) = 4 := by
  have hn : (naturalPart d a hKC).toSubmodule ≠ ⊤ := by
    intro he
    apply not_le_of_gt hlt
    intro x hx
    have hh : Additive.ofMul (⟨x,hx⟩ : QC T L V) ∈ (naturalPart d a hKC).toSubmodule := by
      rw [he]
      trivial
    exact hh
  have h := Submodule.finrank_lt hn
  rw [naturalPart_finrank d a hKC] at h
  have hb := QC_finrank_le_four d a hKC hQL
  omega

/-- The marked image of the literal two-core, without replacing it by a residual. -/
noncomputable def parabolicMap : (F.Li L 1).pCoreIn 2 →* BinaryLinearThree.Group :=
  d.qL.comp (Subgroup.inclusion ((pCoreIn_le 2 (F.Li L 1)).trans
    ((F.Li_le L 1).trans inf_le_left)))

theorem commutator_eq_of_linear_displacement
    (hdisp : BinaryOffender.subspaceCommutator (action d a hKC) ⊤ (parabolicMap d).range =
      (naturalPart d a hKC).toSubmodule) : ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V := by
  have hPL : (F.Li L 1).pCoreIn 2 ≤ L :=
    (pCoreIn_le 2 (F.Li L 1)).trans ((F.Li_le L 1).trans inf_le_left)
  apply le_antisymm
  · exact (commutator_mono le_rfl hPL).trans (QC_commutator_le (F := F))
  · let C : Submodule (ZMod 2) (Additive (QC T L V)) :=
      AddSubgroup.toZModSubmodule 2
        ((⁅QC T L V, (F.Li L 1).pCoreIn 2⁆).subgroupOf (QC T L V)).toAddSubgroup
    have hm : BinaryOffender.subspaceCommutator (action d a hKC) ⊤
        (parabolicMap d).range ≤ C := by
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨p,rfl⟩, x, _, rfl⟩
      change ((((action d a hKC) (parabolicMap d p) x).toMul / x.toMul : QC T L V) : G) ∈
        ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆
      rw [Subgroup.coe_div, div_eq_mul_inv]
      change (((action d a hKC) (d.qL (Subgroup.inclusion hPL p)) x).toMul : G) * _ ∈ _
      rw [action_apply]
      rw [commutator_comm]
      exact commutator_mem_commutator p.property x.toMul.property
    rw [hdisp] at hm
    intro v hv
    exact hm (show Additive.ofMul (⟨v,V_le_QC d a hv⟩ : QC T L V) ∈
      (naturalPart d a hKC).toSubmodule from hv)

theorem false_of_linear_displacement
    (hdisp : BinaryOffender.subspaceCommutator (action d a hKC) ⊤ (parabolicMap d).range =
      (naturalPart d a hKC).toSubmodule) : False :=
  false_of_QC_parabolic_displacement d a hKC (QC_centralizes_S d a hKC)
    (commutator_eq_of_linear_displacement d a hKC hdisp)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
