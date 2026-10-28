module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.InitialSplitting
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Marked coordinates on the original nonbinary MS initial subgroup

For E = Ω₁(Z(O₂(KR))), construct a section model of [E,K] over the
original field: it is natural or doubled natural with one full SL₃
quotient marking. The proved initial moved-space classification supplies
the coordinates. Finite-field uniqueness returns them to the given field;
the literal inclusion and quotient projection retain the conjugation action.
In particular, the scalar center at field four is retained.

The same moved-space complement proves E = [E,K] × C_E(K) in the original
group. Its moving factor lies in Z(msQ K R). These statements supply the
initial-module input of original 4.3.9; the whole-core sections, Sylow
radical inequalities and full C.1.34 assembly remain separate obligations.
No original-ambient centrality of C_msQ(K) is asserted.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, and original
4.3.9, p.616; Meierfrankenfeld--Stellmacher (1993), Sections 2--3.
The full SL₃ field transport uses the existing attributed ATLAS port;
see LICENSES/ATLAS.txt.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
noncomputable section
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "ρ" => centralOmegaRepresentation K R
local notation "B" => centralOmegaComponent K R
local notation "O" => offenderSubgroup ρ

/-- The original central omega subgroup of O₂(KR), embedded in G. -/
def initialOmega (K R : Subgroup G) : Subgroup G :=
  (centralOmegaLayer K R).map (K ⊔ R).subtype
/-- Its literal commutator with the original component. -/
def initialMoved (K R : Subgroup G) : Subgroup G := ⁅initialOmega K R,K⁆

omit [Finite G] in
private theorem initialMoved_eq_map : initialMoved K R =
    (⁅centralOmegaLayer K R,L⁆).map (J).subtype := by
  rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ R from le_sup_left)]
  rfl

include h hn

omit [CharP F 2] in
private theorem initialMoved_normalized : K ≤ normalizer (initialMoved K R) := by
  have hnorm : (⁅centralOmegaLayer K R,L⁆).Normal := by
    let := component_normal h hn
    infer_instance
  rw [initialMoved_eq_map]
  exact (le_sup_left : K ≤ K ⊔ R).trans
    ((normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
      (by simpa only [subgroupOf, comap_map_eq_self_of_injective (J).subtype_injective] using hnorm))

omit [CharP F 2] in
private theorem initial_space_eq
    (s : MovedSection ((ρ).comp (O).subtype) ((B).subgroupOf O)) :
    s.space.toSubmodule = subspaceCommutator ρ ⊤ B := by
  rw [s.space_eq, moved, subspaceCommutator_comp_map,
    map_subgroupOf_eq_of_le (centralOmega_source_conclusion h hn).1]

private def initialCoordinates
    (s : MovedSection ((ρ).comp (O).subtype) ((B).subgroupOf O)) :
    initialMoved K R ≃* Multiplicative s.space.toSubmodule := by
  let U := centralOmegaLayer K R
  let M := ⁅U,L⁆
  let : IsElementaryAbelian 2 M := IsElementaryAbelian.of_le (commutator_le_left U L)
  let a : M ≃* initialMoved K R :=
    (M.equivMapOfInjective (J).subtype (J).subtype_injective).trans
      (MulEquiv.subgroupCongr initialMoved_eq_map.symm)
  let b : Additive M ≃ₗ[ZMod 2] s.space.toSubmodule :=
    (NormalElementaryQuotient.movedEquiv U (centralOmegaProjection K R)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) L).trans
      (LinearEquiv.ofEq _ _ (initial_space_eq h hn s).symm)
  exact a.symm.trans ((MulEquiv.multiplicativeAdditive M).symm.trans
    b.toAddEquiv.toMultiplicative)

omit [CharP F 2] in
private theorem initialCoordinates_val
    (s : MovedSection ((ρ).comp (O).subtype) ((B).subgroupOf O)) (x : initialMoved K R) :
    (((initialCoordinates h hn s x).toAdd.val.toMul : J) : G) = x := by
  let M := ⁅centralOmegaLayer K R,L⁆
  let a : M ≃* initialMoved K R :=
    (M.equivMapOfInjective (J).subtype (J).subtype_injective).trans
      (MulEquiv.subgroupCongr initialMoved_eq_map.symm)
  change (a (a.symm x) : G) = x
  exact congrArg Subtype.val (a.apply_symm_apply x)

private def initialActor (k : K) : (B).subgroupOf O :=
  ⟨⟨centralOmegaProjection K R ⟨k,mem_sup_left k.property⟩,
    (centralOmega_source_conclusion h hn).1 (mem_map_of_mem _ k.property)⟩,
    mem_map_of_mem _ k.property⟩

omit [CharP F 2] in
private theorem initialCoordinates_conjugate
    (s : MovedSection ((ρ).comp (O).subtype) ((B).subgroupOf O))
    (k : K) (x y : initialMoved K R)
    (hy : (y : G) = k * (x : G) * (k : G)⁻¹) :
    (initialCoordinates h hn s y).toAdd =
      (s.space.toRepresentation.comp ((B).subgroupOf O).subtype)
        (initialActor h hn k) (initialCoordinates h hn s x).toAdd := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  have he := NormalElementaryQuotient.representation_apply
    (centralOmegaLayer K R) (centralOmegaProjection K R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (⟨k,mem_sup_left k.property⟩ : J) (initialCoordinates h hn s x).toAdd.val
  exact (initialCoordinates_val h hn s y).trans
    (hy.trans ((congrArg (fun z : G => (k : G) * z * (k : G)⁻¹)
      (initialCoordinates_val h hn s x).symm).trans
      (congrArg (J).subtype he).symm))

private def initialMark
    (mark : (B).subgroupOf O ≃* SL(3,F)) : (K ⧸ pCore 2 K) ≃* SL(3,F) :=
  let e := Classical.choice h.model
  e.trans ((centralOmegaFullEquiv h hn e).symm.trans
    ((subgroupOfEquivOfLe (centralOmega_source_conclusion h hn).1).symm.trans mark))

private theorem initialMark_mk (mark : (B).subgroupOf O ≃* SL(3,F)) (k : K) :
    linearThreeActor (initialMark h hn mark) k = mark (initialActor h hn k) := by
  let e := Classical.choice h.model
  have he := centralOmegaFullEquiv_mk h hn e
    (⟨⟨k,mem_sup_left k.property⟩,k.property⟩ : L)
  change mark ((subgroupOfEquivOfLe (centralOmega_source_conclusion h hn).1).symm
    ((centralOmegaFullEquiv h hn e).symm (e (QuotientGroup.mk' _ k)))) = _
  rw [← he, MulEquiv.symm_apply_apply]
  rfl

omit h hn [Finite G] [Finite F] [CharP F 2] in
private theorem section_of_coordinates
    {H X k : Type*} [Group H] [AddCommGroup X] [Field k] [Module k X]
    {A D : Subgroup G} (actor : A →* H) (v : Representation k H X)
    (hnorm : A ≤ normalizer D) (E : D ≃* Multiplicative X)
    (he : ∀ (a : A) (x y : D), (y : G) = a * (x : G) * (a : G)⁻¹ →
      (E y).toAdd = v (actor a) (E x).toAdd) :
    HasSectionModel A D ⊥ actor v := by
  rw [HasSectionModel,bot_subgroupOf]
  exact ⟨bot_le,hnorm,le_normalizer_of_normal,inferInstance,QuotientGroup.quotientBot.trans E,he⟩

private theorem initial_section_of_action
    [Algebra (ZMod 2) F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) F V]
    (v : Representation F SL(3,F) V)
    (s : MovedSection ((ρ).comp (O).subtype) ((B).subgroupOf O))
    (a : ActionEquiv (s.space.toRepresentation.comp ((B).subgroupOf O).subtype)
      (v.restrictScalars (k := ZMod 2))) :
    HasSectionModel K (initialMoved K R) ⊥
      (linearThreeActor (initialMark h hn a.groupEquiv)) v := by
  let E := (initialCoordinates h hn s).trans a.linearEquiv.toAddEquiv.toMultiplicative
  apply section_of_coordinates _ v (initialMoved_normalized h hn) E
  intro k x y hy
  change a.linearEquiv (initialCoordinates h hn s y).toAdd =
    v (linearThreeActor (initialMark h hn a.groupEquiv) k)
      (a.linearEquiv (initialCoordinates h hn s x).toAdd)
  exact (congrArg a.linearEquiv (initialCoordinates_conjugate h hn s k x y hy)).trans
    ((a.intertwines (initialActor h hn k) (initialCoordinates h hn s x).toAdd).trans
      (congrArg (fun g : SL(3,F) => v g (a.linearEquiv (initialCoordinates h hn s x).toAdd))
        (initialMark_mk h hn a.groupEquiv k).symm))

private def fieldCoordinates (E : BinaryField) [Algebra (ZMod 2) F]
    (f : E.Carrier ≃+* F) :
    (Fin 3 → E.Carrier) ≃ₗ[ZMod 2] (Fin 3 → F) where
  toFun v i := f (v i)
  invFun v i := f.symm (v i)
  left_inv v := funext (fun i => f.symm_apply_apply (v i))
  right_inv v := funext (fun i => f.apply_symm_apply (v i))
  map_add' v w := funext (fun i => f.map_add (v i) (w i))
  map_smul' c v := funext (fun i => ZMod.map_smul f.toAddMonoidHom c (v i))

omit h hn [Finite G] [Finite F] [CharP F 2] in
private theorem fieldCoordinates_intertwines (E : BinaryField) [Algebra (ZMod 2) F]
    (f : E.Carrier ≃+* F) (g : SL(3,E.Carrier)) (v : Fin 3 → E.Carrier) :
    fieldCoordinates E f (linearNatural E 3 g v) =
      Representation.specialLinearNatural 3 (Atlas.fieldEquivSL 3 f g)
        (fieldCoordinates E f v) := by
  ext i
  change f (∑ j, g.val i j * v j) = ∑ j, f (g.val i j) * f (v j)
  simp only [map_sum,map_mul]

private def naturalFieldAction [Algebra (ZMod 2) F]
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) X W} (E : BinaryField) (f : E.Carrier ≃+* F)
    (a : ActionEquiv σ (linearNatural E 3)) :
    ActionEquiv σ ((Representation.specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)) where
  groupEquiv := a.groupEquiv.trans (Atlas.fieldEquivSL 3 f)
  linearEquiv := a.linearEquiv.trans (fieldCoordinates E f)
  intertwines g v := by
    change fieldCoordinates E f (a.linearEquiv (σ g v)) = _
    rw [a.intertwines]
    exact fieldCoordinates_intertwines E f _ _

private def doubleFieldAction [Algebra (ZMod 2) F]
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) X W} (E : BinaryField) (f : E.Carrier ≃+* F)
    (a : ActionEquiv σ (repeated (linearNatural E 3) 2)) :
    ActionEquiv σ (((Representation.specialLinearNatural (k := F) 3).prod
      (Representation.specialLinearNatural (k := F) 3)).restrictScalars (k := ZMod 2)) where
  groupEquiv := a.groupEquiv.trans (Atlas.fieldEquivSL 3 f)
  linearEquiv := a.linearEquiv.trans
    ((LinearEquiv.piCongrRight fun _ : Fin 2 => fieldCoordinates E f).trans
      (LinearEquiv.finTwoArrow (ZMod 2) (Fin 3 → F)))
  intertwines g v := by
    change (fieldCoordinates E f (a.linearEquiv (σ g v) 0),
      fieldCoordinates E f (a.linearEquiv (σ g v) 1)) = _
    rw [a.intertwines]
    apply Prod.ext
    · exact fieldCoordinates_intertwines E f _ _
    · exact fieldCoordinates_intertwines E f _ _

/-- The actual initial commutator has natural or doubled-natural coordinates
over the original field, with one full quotient marking in either case. -/
theorem initialMoved_section_models :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K (initialMoved K R) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := F) 3) ∨
      HasSectionModel K (initialMoved K R) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)) := by
  obtain ⟨c,_,E,hE,ha⟩ := centralOmega_split_source h hn
  let := Fintype.ofFinite F
  let := Fintype.ofFinite E.Carrier
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let f : E.Carrier ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      E.card_eq,h.field_card,hE])
  rcases ha with ha | ha
  · obtain ⟨a⟩ := ha
    let b := naturalFieldAction E f a
    exact ⟨initialMark h hn b.groupEquiv,
      Or.inl (initial_section_of_action h hn _ c.sectionData b)⟩
  · obtain ⟨a⟩ := ha
    let b := doubleFieldAction E f a
    exact ⟨initialMark h hn b.groupEquiv,
      Or.inr (initial_section_of_action h hn _ c.sectionData b)⟩

omit h hn [Finite G] [Finite F] [CharP F 2] in
/-- The central-omega group uses the original ambient two-core. -/
theorem initialOmega_eq : initialOmega K R =
    Subgroup.omegaCenterIn ((K ⊔ R).pCoreIn 2) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨hp,hc,hs⟩ := (mem_omegaCenterIn_iff _ _).mp hy
    refine (mem_omegaCenterIn_iff _ _).mpr ⟨mem_map_of_mem _ hp,?_,?_⟩
    · rintro z ⟨w,hw,rfl⟩
      exact congrArg (K ⊔ R).subtype (hc w hw)
    · exact congrArg (K ⊔ R).subtype hs
  · intro hx
    obtain ⟨⟨y,hy,rfl⟩,hc,hs⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    refine ⟨y,(mem_omegaCenterIn_iff _ _).mpr ⟨hy,?_,?_⟩,rfl⟩
    · intro z hz
      exact Subtype.ext (hc z (mem_map_of_mem _ hz))
    · exact Subtype.ext hs

omit h hn [Finite G] [Finite F] [CharP F 2] in
/-- The initial commutator stays inside the literal central omega group. -/
theorem initialMoved_le_omega : initialMoved K R ≤ initialOmega K R := by
  rw [initialMoved_eq_map]
  exact map_mono (commutator_le_left (centralOmegaLayer K R) L)

omit h hn [Finite G] [Finite F] [CharP F 2] in
/-- The actual initial moved group is a subgroup of the original MS core. -/
theorem initialMoved_le_msQ : initialMoved K R ≤ msQ K R := by
  apply commutator_mono _ le_rfl
  exact map_mono (map_subtype_le _)

omit h hn [Finite G] [Finite F] [CharP F 2] in
/-- The initial moved group embeds in the center of the original MS core. -/
theorem initialMoved_le_core_center : initialMoved K R ≤
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ K R) := by
  have hQ : msQ K R ≤ (K ⊔ R).pCoreIn 2 := by
    rw [← commutator_map_eq_msQ]
    exact map_mono (commutator_le_left (pCore 2 J) L)
  intro x hx
  refine ⟨⟨x,initialMoved_le_msQ hx⟩,mem_center_iff.mpr ?_,rfl⟩
  intro y
  apply Subtype.ext
  have he : x ∈ Subgroup.omegaCenterIn ((K ⊔ R).pCoreIn 2) :=
    initialOmega_eq (K := K) (R := R) ▸ initialMoved_le_omega hx
  exact ((mem_omegaCenterIn_iff _ _).mp he).2.1 y (hQ y.property)

/-- The original central omega is the direct product of its actual moved
subgroup and its component-fixed subgroup. -/
theorem initialMoved_split :
    initialMoved K R ⊔ (initialOmega K R ⊓ centralizer (K : Set G)) = initialOmega K R ∧
    initialMoved K R ⊓ (initialOmega K R ⊓ centralizer (K : Set G)) = ⊥ := by
  obtain ⟨c,hs,_⟩ := centralOmega_split_source h hn
  let s := c.sectionData
  have hfixed (v : Additive (centralOmegaLayer K R)) :
      v ∈ fixedSpace ((ρ).comp (O).subtype) ((B).subgroupOf O) ↔
      ((v.toMul : J) : G) ∈ centralizer (K : Set G) := by
    have he : fixedSpace ((ρ).comp (O).subtype) ((B).subgroupOf O) = fixedSpace ρ B := by
      ext w
      constructor
      · intro hw b
        exact hw ((subgroupOfEquivOfLe (centralOmega_source_conclusion h hn).1).symm b)
      · intro hw b
        exact hw ((subgroupOfEquivOfLe (centralOmega_source_conclusion h hn).1) b)
    rw [he]
    change v ∈ fixedSpace (NormalElementaryQuotient.representation _ _ _ _) ((L).map _) ↔ _
    rw [NormalElementaryQuotient.mem_fixedSpace_image]
    constructor
    · intro hc k hk
      exact congrArg (K ⊔ R).subtype (hc ⟨k,mem_sup_left hk⟩ hk)
    · intro hc k hk
      exact Subtype.ext (hc k hk)
  constructor
  · apply le_antisymm (sup_le initialMoved_le_omega inf_le_left)
    rintro x ⟨xJ,hxJ,rfl⟩
    let v : Additive (centralOmegaLayer K R) := Additive.ofMul ⟨xJ,hxJ⟩
    have hv : v ∈ s.space.toSubmodule ⊔
        fixedSpace ((ρ).comp (O).subtype) ((B).subgroupOf O) :=
      hs.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hv
    have ha' : ((a.toMul : J) : G) ∈ initialMoved K R := by
      rw [initialMoved_eq_map]
      refine mem_map_of_mem _ ?_
      change a ∈ NormalElementaryQuotient.commutatorSpace (centralOmegaLayer K R) L
      rw [NormalElementaryQuotient.commutatorSpace_eq (centralOmegaLayer K R)
        (centralOmegaProjection K R) (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _) L]
      exact (initial_space_eq h hn s) ▸ ha
    have hb' : ((b.toMul : J) : G) ∈ initialOmega K R ⊓ centralizer (K : Set G) :=
      ⟨mem_map_of_mem _ b.toMul.property,(hfixed b).mp hb⟩
    have he' := congrArg (fun w : Additive (centralOmegaLayer K R) => ((w.toMul : J) : G)) he
    change ((a.toMul : J) : G) * ((b.toMul : J) : G) = (xJ : G) at he'
    change (xJ : G) ∈ initialMoved K R ⊔ (initialOmega K R ⊓ centralizer (K : Set G))
    exact he' ▸ mul_mem_sup ha' hb'
  · apply bot_unique
    intro x hx
    let v := (initialCoordinates h hn s ⟨x,hx.1⟩).toAdd
    have hf : v.val ∈ fixedSpace ((ρ).comp (O).subtype) ((B).subgroupOf O) :=
      (hfixed v.val).mpr ((initialCoordinates_val h hn s ⟨x,hx.1⟩).symm ▸ hx.2.2)
    have hz : v.val = 0 := (disjoint_iff.mp hs.disjoint).le ⟨v.property,hf⟩
    exact (initialCoordinates_val h hn s ⟨x,hx.1⟩).symm.trans
      (congrArg (fun w : Additive (centralOmegaLayer K R) => ((w.toMul : J) : G)) hz)

end
end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
