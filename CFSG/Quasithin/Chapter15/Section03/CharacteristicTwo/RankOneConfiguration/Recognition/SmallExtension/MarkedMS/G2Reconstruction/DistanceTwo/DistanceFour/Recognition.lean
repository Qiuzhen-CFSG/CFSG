module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.Displacement
public import Theory.GroupTheory.NormalSectionResidualMonolith
public import Theory.Representation.PSL3Two.ResidualFFForms.Descent
public import Theory.Representation.BinaryOffender.SectionLinear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.NaturalCommutator

/-!
# Whole natural recognition in the fixed-derived G₂ radius branch

A projected offender acts on an irreducible submodule after descent through
the actual two-group kernel. The order-6048 FF classification recognizes
its whole natural six-space, whose offender costs exactly three dimensions.
The quotient therefore has zero displacement. The centric simple residual
image forces the quotient to be residual-fixed, and residual commutator
generation makes the submodule exhaust the original module.

Applied to the actual moving central quotient, this constructs the whole
natural action and the trivial two-core action instead of assuming either.
The scalar commutator-form calculation then bounds the whole moving
commutator by two. The nonfixed derived-radius branch remains the obligation
of qt-e-ms-small-g2-reconstruction; this is not unconditional reconstruction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(1.4)--(1.5) and (3.8), printed pp.842 and 878--879; AS B.5.1 and C.1.32.
The natural octonion action retains the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour

private def whole_of_full_fixed
    {D V W E : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    (τ : Representation (ZMod 2) E W) (s : MovedSection ρ C)
    (hm : moved ρ C = ⊤) (hz : fixedSpace ρ C = ⊥)
    (e : ActionEquiv (s.action.comp C.subtype) τ) :
    ActionEquiv (ρ.comp C.subtype) τ := by
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  have hc : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    have hv' : (v : V) ∈ fixedSpace ρ C := fun g => congrArg Subtype.val (hv g)
    rw [hz] at hv'
    exact Subtype.ext hv'
  let f : V ≃ₗ[ZMod 2] s.space.toSubmodule :=
    (LinearEquiv.ofBijective s.space.toSubmodule.subtype
      ⟨Subtype.val_injective, fun v => ⟨⟨v,hs.symm ▸ Submodule.mem_top⟩,rfl⟩⟩).symm
  let q := (s.central.toSubmodule.quotEquivOfEqBot hc).symm
  refine ⟨e.groupEquiv, (f.trans q).trans e.linearEquiv, ?_⟩
  intro g v
  change e.linearEquiv (q (f (ρ g v))) = τ (e.groupEquiv g) (e.linearEquiv (q (f v)))
  have hfv (x : V) : (f x : V) = x :=
    (LinearEquiv.ofBijective s.space.toSubmodule.subtype
      ⟨Subtype.val_injective, fun v => ⟨⟨v,hs.symm ▸ Submodule.mem_top⟩,rfl⟩⟩).apply_symm_apply x
  have hact : f (ρ (g : D) v) = s.space.toRepresentation g (f v) := by
    apply Subtype.ext
    change (f (ρ g v) : V) = ρ g (f v)
    rw [hfv,hfv]
  simp only [q,Submodule.quotEquivOfEqBot_symm_apply]
  rw [hact]
  exact e.intertwines g (s.central.toSubmodule.mkQ (f v))

private theorem irreducible_full_fixed
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [IsIrreducible ρ]
    (C : Subgroup D) [C.Normal]
    (hn : ¬ ∀ g ∈ C, ∀ v, ρ g v = v) :
    moved ρ C = ⊤ ∧ fixedSpace ρ C = ⊥ := by
  let s := MovedSection.ofNormal ρ C
  have hm : s.space.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top s.space with h | h
    · exfalso
      apply hn
      have hz : subspaceCommutator ρ ⊤ C = ⊥ := by
        change moved ρ C = ⊥
        rw [←s.space_eq,h]; rfl
      have hf := (subspaceCommutator_eq_bot_iff ρ ⊤ C).mp hz
      exact fun g hg v => hf Submodule.mem_top ⟨g,hg⟩
    · exact congrArg Subrepresentation.toSubmodule h
  have hz : fixedSpace ρ C = ⊥ := by
    rcases eq_bot_or_eq_top (fixedSubrepresentation ρ C) with h | h
    · exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hn
      have hh : fixedSpace ρ C = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact fun g hg v => (show v ∈ fixedSpace ρ C from hh.symm ▸ Submodule.mem_top) ⟨g,hg⟩
  exact ⟨s.space_eq.symm.trans hm,hz⟩

private theorem simple_centric_faithful
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    [C.Normal] [IsSimpleGroup C]
    (hC : centralizer (C : Set D) = ⊥)
    (hn : ¬ ∀ g ∈ C, ∀ v, ρ g v = v) : Function.Injective ρ := by
  apply MovedSection.faithful_of_faithful_centric_restriction (L := C) ρ ?_ hC
  apply ((ρ.comp C.subtype).ker_eq_bot_iff).mp
  rcases (inferInstance : (ρ.comp C.subtype).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  · exfalso
    apply hn
    intro g hg v
    have he : (ρ.comp C.subtype) ⟨g,hg⟩ = 1 :=
      show ⟨g,hg⟩ ∈ (ρ.comp C.subtype).ker from hk.symm ▸ mem_top _
    exact DFunLike.congr_fun he v

/-- An irreducible module nontrivial on a centric G₂ component spends all
three units of the displacement bound and is the whole natural six-space. -/
theorem irreducible_g2_offender_natural
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [IsIrreducible ρ]
    (C : Subgroup D) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hc : Nat.card C = 6048) (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hn : ¬ ∀ g ∈ C, ∀ v, ρ g v = v)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 8) (hcost : fixedCodim ρ A ≤ 3) :
    fixedCodim ρ A = 3 ∧
      Nonempty (ActionEquiv (ρ.comp C.subtype) (g2DerivedNatural (ZMod 2))) := by
  have hf := simple_centric_faithful ρ C hC hn
  have hr : rank A = 3 := by rw [rank,hcard]; decide
  have hne : A ≠ ⊥ := by intro h; rw [h,card_bot] at hcard; omega
  have hoff : IsOffender ρ A := ⟨⟨hne,hA⟩,hr.symm ▸ hcost⟩
  obtain ⟨_,⟨e⟩⟩ := ChapterC.RankTwo.G2.ff_card_g2_two_moved_natural ρ C hc hC hsq hf ⟨A,hoff⟩
  obtain ⟨hm,hz⟩ := irreducible_full_fixed ρ C hn
  let E := whole_of_full_fixed ρ C _ (MovedSection.ofNormal ρ C) hm hz e
  obtain ⟨f,hf',_,he⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding ρ C
    E.groupEquiv E.linearEquiv E.intertwines hf
  have ho := hoff.map_equivariant ρ (Atlas.G2.Natural.action (ZMod 2))
    f hf' E.linearEquiv he
  have hd := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim (F := ZMod 2) (n := 1)
    (by norm_num : Nat.card (ZMod 2) = 2 ^ 1) (by decide) (A.map f) ho
  have heq := fixedCodim_map_equivariant ρ (Atlas.G2.Natural.action (ZMod 2))
    f E.linearEquiv he A
  have heq' := fixedCodim_map_equivariant (Atlas.G2.Natural.action (ZMod 2))
    (Atlas.G2.NaturalOffenders.binaryNatural (F := ZMod 2))
    (MonoidHom.id _) (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) (A.map f)
  rw [map_id] at heq'
  exact ⟨heq.trans (heq'.trans (by simpa using hd)),⟨E⟩⟩

/-- The projected offender recognizes the entire residual-full, residual-fixed-free
module, including descent of the original two-group kernel on that whole module. -/
theorem projected_g2_whole_natural
    {S D V : Type*} [Group S] [Finite S] [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (q : S →* D) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (C : Subgroup D) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hres : (pResidual 2 S).map q = C)
    (hc : Nat.card C = 6048) (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (ρ : Representation (ZMod 2) S V)
    (hfull : subspaceCommutator ρ ⊤ (pResidual 2 S) = ⊤)
    (hfixed : fixedSpace ρ (pResidual 2 S) = ⊥)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card (A.map q) = 8) (hcost : fixedCodim ρ A ≤ 3) :
    ∃ σ : Representation (ZMod 2) D V, σ.comp q = ρ ∧
      Nonempty (ActionEquiv (σ.comp C.subtype) (g2DerivedNatural (ZMod 2))) := by
  obtain ⟨U,hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let : IsIrreducible U.toRepresentation := hU
  let : Nontrivial U.toSubmodule := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  let σ := BinaryLinearThree.ResidualFFForms.irreducibleDescent q hq hp U.toRepresentation
  have he : σ.comp q = U.toRepresentation :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_comp q hq hp U.toRepresentation
  let : IsIrreducible σ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_irreducible q hq hp U.toRepresentation
  have hn : ¬ ∀ g ∈ C, ∀ v, σ g v = v := by
    intro hn
    obtain ⟨u,hu⟩ := exists_ne (0 : U.toSubmodule)
    apply hu
    apply Subtype.ext
    have hu' : (u : V) ∈ fixedSpace ρ (pResidual 2 S) := by
      intro g
      have hg : q g ∈ C := hres ▸ mem_map_of_mem q g.property
      have hx := hn (q g) hg u
      have he' := congrArg (fun τ => τ g u) he
      exact congrArg Subtype.val (he'.symm.trans hx)
    exact show (u : V) ∈ (⊥ : Submodule (ZMod 2) V) from hfixed ▸ hu'
  have hcostU : fixedCodim σ (A.map q) = fixedCodim U.toRepresentation A := by
    rw [←he]
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have huBound := fixedCodim_subrepresentation_le ρ U A
  obtain ⟨hthree,⟨E⟩⟩ := irreducible_g2_offender_natural σ C hc hC hsq hn (A.map q)
    (by let := hA; exact IsElementaryAbelian.map q) hcard (by omega)
  have hadd := fixedCodim_quotient_add_subrepresentation_le ρ U A
  have hzero : fixedCodim U.quotientRepresentation A = 0 := by omega
  have hAK : A ≤ U.quotientRepresentation.asGroupHom.ker := by
    have hz := (fixedCodim_eq_zero_iff U.quotientRepresentation A).mp hzero
    intro a ha
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact (show v ∈ fixedSpace U.quotientRepresentation A from hz.symm ▸ Submodule.mem_top) ⟨a,ha⟩
  have hAn : ¬ A ≤ q.ker := by
    intro h
    have hz := (map_eq_bot_iff A).mpr h
    rw [hz,card_bot] at hcard
    omega
  let : IsSimpleGroup ((pResidual 2 S).map q) := hres.symm ▸ inferInstance
  have hK := pResidual_le_normal_of_not_le_monolithic_kernel 2 q hq hp
    (hres.symm ▸ hC) U.quotientRepresentation.asGroupHom.ker (fun h => hAn (hAK.trans h))
  have hUtop : U.toSubmodule = ⊤ := by
    apply top_unique
    rw [←hfull]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp
    have hg' := congrArg Units.val (hK hg)
    have hv := congrArg (fun f : Module.End (ZMod 2) (V ⧸ U.toSubmodule) => f (U.toSubmodule.mkQ v)) hg'
    change U.toSubmodule.mkQ (ρ g v) = U.toSubmodule.mkQ v at hv
    change U.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub,hv,sub_self]
  let f : U.toSubmodule ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective U.toSubmodule.subtype
      ⟨Subtype.val_injective, fun v => ⟨⟨v,hUtop.symm ▸ Submodule.mem_top⟩,rfl⟩⟩
  let τ : Representation (ZMod 2) D V := f.conjRingEquiv.toMonoidHom.comp σ
  refine ⟨τ,?_,⟨⟨E.groupEquiv,f.symm.trans E.linearEquiv,?_⟩⟩⟩
  · ext g v
    obtain ⟨u,rfl⟩ := f.surjective v
    change f (σ (q g) (f.symm (f u))) = ρ g (f u)
    rw [f.symm_apply_apply]
    have hh := congrArg (fun π => π g u) he
    exact congrArg Subtype.val hh
  · intro g v
    change E.linearEquiv (f.symm (f (σ g (f.symm v)))) = _
    rw [f.symm_apply_apply]
    exact E.intertwines g (f.symm v)

open Stellmacher.PushingUp.AmalgamGraph
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NaturalStructure.Exclusion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "H" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)

private theorem moving_derived_bound_of_descended_natural
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (hb : 2 < (geometry h).b T) (a : Vertex T) (ha : color T a = false)
    (hfixed : ⁅V T a,V T a⁆ ≤ fixedCore T a)
    {D : Type*} [Group D] (q : stabilizer T a →* D) (C : Subgroup D)
    (hres : (pResidual 2 (stabilizer T a)).map q = C)
    [IsElementaryAbelian 2 ((Vcirc T a) ⧸ center (Vcirc T a))]
    (σ : Representation (ZMod 2) D (Additive ((Vcirc T a) ⧸ center (Vcirc T a))))
    (hσ : σ.comp q = Offenders.linearize (movingQuotientAction a))
    (E : ActionEquiv (σ.comp C.subtype) (g2DerivedNatural (ZMod 2))) :
    Nat.card (commutator (Vcirc T a)) ≤ 2 := by
  let P := Vcirc T a
  let S := stabilizer T a
  let := finite_moving (geometry h) hb a ha
  let ρ := Offenders.linearize (movingQuotientAction a)
  let coord := (Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).toLinearEquiv
  apply central_quotient_derived_bound (E.linearEquiv.trans coord)
  intro g
  let c := E.groupEquiv.symm g
  have hEg : E.groupEquiv c = g := E.groupEquiv.apply_symm_apply g
  obtain ⟨s,hs,hsc⟩ := (show c.val ∈ (pResidual 2 S).map q from hres.symm ▸ c.property)
  refine ⟨movingAction a s,?_,?_⟩
  · intro x
    apply Subtype.ext
    rw [movingAction_apply]
    have hx : (x.val.val : FreeAmalgam T) ∈ ⁅Vcirc T a,Vcirc T a⁆ := by
      rw [←map_subtype_commutator]
      exact mem_map_of_mem P.subtype x.property
    have hm : P ≤ V T a := le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (V_normalized a))
    have hxf := hfixed (commutator_mono hm hm hx)
    have hsl : s.val ∈ Ltilde T a := mem_map_of_mem S.subtype hs
    rw [hxf.2 s.val hsl,mul_inv_cancel_right]
  · intro v
    have heσ := congrArg (fun τ => τ s v) hσ
    have hEc := E.intertwines c v
    change E.linearEquiv (σ c.val v) =
      g2DerivedNatural (ZMod 2) (E.groupEquiv c) (E.linearEquiv v) at hEc
    change σ (q s) v = ρ s v at heσ
    rw [←hsc] at hEc
    rw [heσ] at hEc
    change coord (E.linearEquiv (ρ s v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) g.val
        (coord (E.linearEquiv v))
    rw [hEc]
    rw [hEg]
    exact DFunLike.congr_fun ((Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining' g.val) _

/-- The fixed-derived branch bounds the whole moving commutator; the natural
central quotient and the trivial action of the two-core are derived here. -/
theorem moving_commutator_card_le_two_of_fixed
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hb : 2 < (geometry h).b T) (a : Vertex T) (ha : color T a = false)
    (hfixed : ⁅V T a,V T a⁆ ≤ fixedCore T a) :
    Nat.card (⁅Vcirc T a,V T a⁆ : Subgroup (FreeAmalgam T)) ≤ 2 := by
  classical
  let P := Vcirc T a
  let := finite_moving (geometry h) hb a ha
  let := moving_central_quotient_elementary (geometry h) (by omega) a ha hfixed
  let W := Additive (P ⧸ center P)
  let ρ := Offenders.linearize (movingQuotientAction a)
  have hbnd : Nat.card (commutator P) ≤ 2 := by
    by_cases ht : Subsingleton W
    · have hc : IsMulCommutative P := by
        refine ⟨⟨fun x y => ?_⟩⟩
        have hx : QuotientGroup.mk' (center P) x = 1 :=
          congrArg Additive.toMul (ht.elim (Additive.ofMul (QuotientGroup.mk' (center P) x)) 0)
        exact ((mem_center_iff.mp ((QuotientGroup.eq_one_iff x).mp hx)) y).symm
      have hz : commutator P = ⊥ := by
        rw [commutator_eq_bot_iff_center_eq_top,center_eq_top_iff]
        exact hc
      rw [hz,card_bot]
      decide
    · let : Nontrivial W := not_subsingleton_iff_nontrivial.mp ht
      let S := stabilizer T a
      let := finite_stabilizer T a
      obtain ⟨d,A,hA,hcard,hcost⟩ := moving_projected_offender_of_fixed h e hb a ha hfixed
      obtain ⟨i,hi,hir,_,_,hiQ⟩ :=
        RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel T
          (edge_two_group h) (core_le_edge h) ha
      let j : H ≃* S := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
      have hj (s : S) : i (j.symm s) = s.val := congrArg Subtype.val (j.apply_symm_apply s)
      let q₀ := QuotientGroup.mk' (pCore 2 H)
      let q := q₀.comp j.symm.toMonoidHom
      have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp j.symm.surjective
      have hqk : q.ker = (pCore 2 H).comap j.symm.toMonoidHom := by
        rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      have hp : IsPGroup 2 q.ker := by
        rw [hqk]
        exact pCore_isPGroup.comap_of_injective j.symm.toMonoidHom j.symm.injective
      have hqQ : q.ker.map S.subtype = Q T a := by
        rw [hqk,←hiQ]
        apply le_antisymm
        · rintro _ ⟨s,hs,rfl⟩
          exact ⟨j.symm s,hs,hj s⟩
        · rintro _ ⟨s,hs,rfl⟩
          refine ⟨j s,?_,rfl⟩
          change j.symm (j s) ∈ pCore 2 H
          rwa [j.symm_apply_apply]
      have hk : q.ker = d.actor.ker :=
        (map_injective S.subtype_injective) (hqQ.trans d.actor_kernel.symm)
      have hcA : Nat.card (A.map q) = 8 := by
        rw [←relIndex_ker, hk,relIndex_ker]
        exact hcard
      have hcost' : fixedCodim ρ A ≤ 3 := by
        have hr : rank (A.map d.actor) = 3 := by rw [rank,hcard]; decide
        simpa only [hr] using hcost
      let C := quotientComponent (L := L) (R := R)
      let := (quotientComponent_structure h e).1
      let := (quotientComponent_structure h e).2.1
      let := (quotientComponent_structure h e).2.2.1
      have hres : (pResidual 2 S).map q = C := by
        change (pResidual 2 S).map (q₀.comp j.symm.toMonoidHom) = C
        rw [←map_map, map_pResidual_of_surjective 2 j.symm.toMonoidHom j.symm.surjective,
          relative_residual h]
        rfl
      obtain ⟨σ,hσ,⟨E⟩⟩ := projected_g2_whole_natural q hq hp C hres
        (quotientComponent_card h e) (quotientComponent_structure h e).2.2.2
        (quotientComponent_sqtk h) ρ
        (moving_quotient_full_of_fixed h hb a ha hfixed)
        (moving_quotient_fixedSpace_eq_bot h hb a ha hfixed) A hA hcA hcost'
      exact moving_derived_bound_of_descended_natural h hb a ha hfixed q C hres σ hσ E
  rw [moving_commutator_eq_derived_of_fixed h hb a ha hfixed,
    ←map_subtype_commutator,card_map_of_injective (Vcirc T a).subtype_injective]
  exact hbnd

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
