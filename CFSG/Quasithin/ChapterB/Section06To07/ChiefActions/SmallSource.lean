module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NaturalSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleFiveMarker
public import Theory.Representation.NormalComponentConstituents

/-!
# Full symmetric-five actions on the original irreducible chief module

The marked B.6.9 section initially describes a moved-space quotient. For a
faithful irreducible action, the normal alternating-five layer moves the
whole module and has zero fixed space. The marked map therefore becomes a
linear equivalence. Its normalizer supplies the whole symmetric-five actor;
the marked section already contains enough offenders to force the ambient
offender subgroup to be the whole actor.

The image adapter retains the literal representation image of the original
minimal parabolic. This is the single symmetric-five branch of 3.1.9(5)
and 15.1.12(3), printed pp.577–578 and1090 of Aschbacher–Smith.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

set_option backward.isDefEq.respectTransparency false in
/-- A marked five-point B.6.9 section is the whole faithful irreducible action. -/
theorem source_quasisimple_five_whole_action
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (hff : IsFFModule ρ)
    (hcore : pCore 2 G = ⊥)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)))
    (e : MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (generalizedFitting (offenderSubgroup ρ))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    Nonempty (ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 5))) ∧
      offenderSubgroup ρ = ⊤ := by
  let Y := offenderSubgroup ρ
  let A := generalizedFitting Y
  let L := A.map Y.subtype
  let s := c.sectionData
  let := offenderSubgroup_normal ρ
  have hL : L = pResidual 2 G :=
    (source_quasisimple_fitting_eq_residual T hP Y
      (offender_generation T hP ρ hff hcore).2 hqs).1
  let : L.Normal := hL ▸ inferInstance
  have hself : centralizer (L : Set G) ≤ L := by
    rw [hL]
    exact centralizer_pResidual_le_of_pCore_eq_bot hcore
  let eg := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e.subgroupEquiv
  have hne : L ≠ ⊥ := by
    intro hb
    have hc : Nat.card L = Nat.card (alternatingGroup (Fin 5)) := Nat.card_congr eg.toEquiv
    rw [hb,nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num at hc
  have hm : s.space.toSubmodule = subspaceCommutator ρ ⊤ L := by
    rw [s.space_eq]
    have hh := subspaceCommutator_map_embedding (ρ.comp Y.subtype) ρ Y.subtype
      (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl) A ⊤
    simpa only [Submodule.map_id] using hh
  have ht : s.space.toSubmodule = ⊤ := hm.trans
    (subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf inferInstance L hne)
  have hz := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf inferInstance L hne
  let j : V ≃ₗ[ZMod 2] s.space.toSubmodule := ((LinearEquiv.ofEq _ _ ht).trans Submodule.topEquiv).symm
  have hj (v : V) : (j v : V) = v := rfl
  let f : V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    e.action.linearEquiv.toLinearMap.comp (s.central.toSubmodule.mkQ.comp j.toLinearMap)
  have hsurj : Function.Surjective f := e.action.linearEquiv.surjective.comp
    (s.central.toSubmodule.mkQ_surjective.comp j.surjective)
  have hk : f.ker = fixedSpace ρ L := by
    ext v
    change e.action.linearEquiv (s.central.toSubmodule.mkQ (j v)) = 0 ↔ _
    rw [←e.action.linearEquiv.map_zero,e.action.linearEquiv.injective.eq_iff,
      Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,s.central_eq]
    constructor
    · intro hv a
      obtain ⟨b,hb,hba⟩ := a.property
      change ρ (a:G) v = v
      rw [←hba]
      exact congrArg Subtype.val (hv ⟨b,hb⟩)
    · intro hv a
      exact Subtype.ext (hv ⟨(a:Y),mem_map_of_mem Y.subtype a.property⟩)
  have hequiv (g : L) v : f (ρ (g:G) v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (eg g) (f v) := by
    let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm g
    have ha : ((a:A):G) = (g:G) := congrArg Subtype.val
      ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply g)
    have hjact : j (ρ (g:G) v) = s.space.toRepresentation (a:Y) (j v) := by
      apply Subtype.ext
      change ρ (g:G) v = ρ ((a:Y):G) v
      rw [ha]
    change e.action.linearEquiv (s.central.toSubmodule.mkQ (j (ρ (g:G) v))) = _
    rw [hjact]
    have hh := e.action.intertwines ⟨(a:Y),e.contained a.property⟩
      (s.central.toSubmodule.mkQ (j v))
    rw [e.compatible] at hh
    exact hh
  have hproper : L ≠ ⊤ := by
    intro htop
    let b := e.action.groupEquiv.symm (Equiv.swap 0 1)
    have hb : ((b:offenderSubgroup s.action):Y) ∈ A := by
      have hg : (((b:offenderSubgroup s.action):Y):G) ∈ L := htop ▸ mem_top _
      obtain ⟨a,ha,he⟩ := hg
      exact (Y.subtype_injective he) ▸ ha
    let a : A := ⟨(b:Y),hb⟩
    have hab : (⟨(a:Y),e.contained a.property⟩ : offenderSubgroup s.action) = b := Subtype.ext rfl
    have hc := e.compatible a
    rw [hab,e.action.groupEquiv.apply_symm_apply] at hc
    have hm : Equiv.swap (0:Fin 5) 1 ∈ alternatingGroup (Fin 5) := hc.symm ▸ (e.subgroupEquiv a).property
    norm_num [Equiv.Perm.mem_alternatingGroup] at hm
  obtain ⟨p,hp,hpf,_⟩ := exists_five_quotient_of_natural_layer ρ L hself hproper eg f hsurj hk hequiv
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp (hk.trans hz)
  let eG := MulEquiv.ofBijective p hp
  have hcard : Nat.card G ≤ Nat.card Y := by
    rw [Nat.card_congr eG.toEquiv]
    have hh := Nat.card_congr e.action.groupEquiv.toEquiv
    exact hh.symm.le.trans (Nat.card_le_card_of_injective (offenderSubgroup s.action).subtype
      (offenderSubgroup s.action).subtype_injective)
  refine ⟨⟨⟨eG,LinearEquiv.ofBijective f ⟨hinj,hsurj⟩,hpf⟩⟩,?_⟩
  exact Subgroup.eq_of_le_of_card_ge le_top (by simpa only [Subgroup.card_top] using hcard)

/-- The single five-point branch for the literal image of an original
irreducible FF chief action; its reduced and faithful hypotheses are derived. -/
theorem minimalParabolic_chief_five_action
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (Representation.BinaryOffender.imageRepresentation ρ))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ))))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      ((Representation.BinaryOffender.imageRepresentation ρ).comp
        (offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ)).subtype)
      (generalizedFitting (offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ))))
    (e : MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (generalizedFitting (offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    Nonempty (ActionEquiv (Representation.BinaryOffender.imageRepresentation ρ)
      (BinaryPermutation.naturalRepresentation (Fin 5))) ∧
      offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ) = ⊤ := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let := imageRepresentation_irreducible ρ (inferInstance : IsIrreducible ρ)
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨A,hA⟩ := hff
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [←hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  exact source_quasisimple_five_whole_action _ (imageRepresentation_injective ρ)
    (S.mapSurjective hq) (minimalParabolic_reduced_image S hS q hq hc hn).2
    hff hc hqs c e

end CFSG.Quasithin.ChapterB
