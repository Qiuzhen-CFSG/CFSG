module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointSelection
public import Theory.SpecificGroups.SymplecticFour.PointLargeGeneration
/-!
# The full point-mover selector at every critical image size

Retain the original natural cover while constructing one quotient marking
that gives both exact U-indices and quadraticity of the actual critical
endpoint. A containing Sylow and the maximum-small-mover dichotomy identify
the large-movement join with the full point radical in this same marking.
The large quadratic actor calculation now produces one residual conjugator
which generates with every neighboring mover through the whole Q-kernel.
Combining it with the established root selector covers every image size,
including the exact fixed subgroup on the full original edge Z.

PointLargePaths applies this selector to the actual critical path and
excludes its trapped alternative for images larger than the field.
Source: MS93 (5.5), printed pp.915--917. Proper smaller movers, the root-image
trapped case and terminal distance exclusions remain separate obligations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.SymplecticFourOrthogonalCover
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A single marking of the whole vertex quotient computes every exact
centralizer index on the original U, including its entire fixed kernel. -/
theorem Input.replacement_critical_natural_indices
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        IsQuadratic (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2))
          (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.start_color
  have hCtop : C = ⊤ := by
    have hpre : C.comap q = ⊤ := by
      rw [show C = (K.subgroupOf d.overgroup).map q from rfl,
        comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    rw [←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hlarge : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let ed : L (K := E.Carrier) ≃* Sp E.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hlarge)).trans Subgroup.topEquiv
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let fD := e.groupEquiv.toMonoidHom.comp κC
  let f := ed.toMonoidHom.comp fD
  have hκC : Function.Surjective κC := by
    intro x
    obtain ⟨g,hg⟩ := hκ x
    exact ⟨g,Subtype.ext hg⟩
  have hf : Function.Surjective f := ed.surjective.comp (e.groupEquiv.surjective.comp hκC)
  have hfker : f.ker = κ.ker := by
    ext x
    change ed (e.groupEquiv (κC x)) = 1 ↔ κ x = 1
    rw [ed.map_eq_one_iff,e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff

  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  let U₀ := (U d.radical a).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjS : Function.Injective jS := fun v w he => hj (congrArg Subtype.val he)
  have hjSr : jS.range = U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U d.radical a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  refine ⟨E,hE,f,hf,by rw [hfker]; exact hκQ,?_,?_⟩
  · intro A
    let σ := MovedSection.coverAction s e
    have hi := embedded_centralizer_index σ U₀ A jS hjS hjSr (fD.comp A.subtype) (by
      intro x w
      apply Subtype.ext
      change j (Multiplicative.ofAdd (s.space.toRepresentation
        (e.groupEquiv.symm (e.groupEquiv (κC x.val))) w)) = _
      rw [e.groupEquiv.symm_apply_apply]
      exact hconj x.val w)
    rw [fixedCodim_of_binaryCover (MovedSection.coverProjection s e) he] at hi
    rw [MonoidHom.range_comp,range_subtype] at hi
    rw [hi]
    congr 1
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have hσ : binaryNatural (K := E.Carrier) = τ.comp ed.toMonoidHom := rfl
    rw [hσ,fixedCodim,fixedSpace_comp_map,Subgroup.map_map]
    rfl

  · let rev : CriticalPath d.radical geometry z a :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse d.radical geometry
          (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
            (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
          a path.start_color (by rw [geometry.distance_constant a path.start_color]; exact (show 0 < geometry.b d.radical by omega))
          z path.end_color path.critical }
    have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
    let δ := κ.comp (inclusion hzS)
    have hq := critical_ambient_quadratic rev (by omega) s e he j hj hjr δ
      (fun x w => hconj (inclusion hzS x) w)
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    have hxδ : κ x ∈ δ.range := ⟨⟨x.val,hx⟩,rfl⟩
    have hyδ : κ y ∈ δ.range := ⟨⟨y.val,hy⟩,rfl⟩
    have hh := hq (κ x) hxδ (κ y) hyδ v
    have hax (w : Vector E.Carrier) : MovedSection.ambientAction s e (κ x) w = f x • w :=
      MovedSection.ambientAction_component s e (κC x) w
    have hay (w : Vector E.Carrier) : MovedSection.ambientAction s e (κ y) w = f y • w :=
      MovedSection.ambientAction_component s e (κC y) w
    change f x • (f y • v-v) = f y • v-v
    simpa only [hax,hay] using hh

omit h d in
private theorem quadratic_conjugate {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {A : Subgroup G} (hA : IsQuadratic ρ A) (g : G) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change ρ (g*a*g⁻¹) (ρ (g*b*g⁻¹) v-v) = ρ (g*b*g⁻¹) v-v
  have hh := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul,Module.End.mul_apply,map_sub,ρ.inv_self_apply,ρ.self_inv_apply] using hh
/-- Preserve exact U-indices and endpoint quadraticity in one Sylow marking. -/
private theorem critical_small_coordinates
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    {t : Vertex d.radical}
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
              2 ^ fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        (∀ A : Subgroup (stabilizer d.radical a), A ≤ (Q d.radical t).subgroupOf (stabilizer d.radical a) →
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            movingIndex ((A.map f).subgroupOf unipotent)) ∧
        IsQuadratic (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2))
          (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f) := by
  obtain ⟨E,hE,f,hf,hfQ,hidx,hquad⟩ := h.replacement_critical_natural_indices d path hb
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hpT : IsPGroup 2 (Q d.radical t) := hjR ▸ (h.replacement_two_group d).map j
  let T := (Q d.radical t).subgroupOf (stabilizer d.radical a)
  obtain ⟨S,hS⟩ := (hpT.comap_subtype.map f).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E.Carrier) S
    (unipotentSylow (by rw [E.card_eq]) (by rw [hE]; exact h.nonbinary.le))
  have hSm : (S : Subgroup (Sp E.Carrier)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun S : Sylow 2 (Sp E.Carrier) => (S : Subgroup (Sp E.Carrier))) hg
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact (map_mono hS).trans_eq hSm
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  refine ⟨E,hE,f',(MulAut.conj g).surjective.comp hf,by rw [hker]; exact hfQ,hTf,?_,?_,?_⟩
  · intro A
    rw [←Subgroup.map_map,fixedCodim_map_conj]
    exact hidx A
  · intro A hAT
    have hAf : A.map f' ≤ unipotent := (map_mono hAT).trans hTf
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have hi : (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) = 2 ^ fixedCodim τ (A.map f') := by
      rw [←Subgroup.map_map, fixedCodim_map_conj]
      exact hidx A
    rw [hi,←binary_movingIndex]
    congr 1
    have hcomp : restrictScalars (k := ZMod 2) (natural (F := E.Carrier)) =
        τ.comp (unipotent (F := E.Carrier)).subtype := rfl
    rw [hcomp]
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,map_subgroupOf_eq_of_le hAf]
  · rw [←Subgroup.map_map]
    exact quadratic_conjugate _ hquad g
/-- The large-movement edge is the full point radical in a marking which
also retains the actual critical endpoint action and every full U-index. -/
theorem Input.replacement_large_movement_point_critical_coordinates
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    {t : Vertex d.radical}
    (hat : Adjacent d.radical a t)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2) = Q d.radical t ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f =
          (CentralRootGeometry.wing false).map unipotent.subtype ∧
        IsQuadratic (restrictScalars (k := ZMod 2) (symplecticNatural (k := B.Carrier) 2))
          (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hglobal,hidx,hquad⟩ :=
    critical_small_coordinates h d path hb hat
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card B.Carrier^2)
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color))
      (U_le_Z a hu) k.val hkQ)
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hjoin : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hUT,hfQ,hTT,hcard]
  have hTi : T.map f ≤ unipotent.subtype.range := by simpa only [range_subtype] using hTf
  rcases Degree.Quotient.maximal_singleton_or_point_radical U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK hTi hidx with ⟨E,hE,hJE⟩ | ⟨hpoint,_,hJT,_⟩
  · have he : E ∈ Subgroup.SmallMover.Maximal U₀ f.ker T (Nat.card B.Carrier^2) :=
      hE ▸ Set.mem_singleton E
    have hi := he.1.2.2
    rw [←hJE] at hi
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective U₀ J
    rw [hUT,hjoin] at hh
    rw [←hh,hcard] at hi
    exact (hJm.not_ge hi).elim
  · refine ⟨B,hB,f,hf,hfQ,hglobal,?_,?_,hquad⟩
    · change J = T at hJT
      rw [←hjoin,hJT,hTT]
    · rw [←Degree.Quotient.coordinates_map f unipotent.subtype T hTi,hpoint]

/-- The large-movement join and the original larger critical endpoint
generate the whole vertex stabilizer after one residual conjugation.
The same conjugator works for every neighboring mover: equal orders force
all of them to equal the full edge. -/
theorem Input.replacement_large_movement_large_generator
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hlarge : Nat.card F < (Q d.radical a).relIndex (Z d.radical z))
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ g ∈ Ltilde d.radical a, ∀ c : Vertex d.radical, Adjacent d.radical c t →
      (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom ⊔
          Z d.radical z = stabilizer d.radical a := by
  obtain ⟨B,hB,f,hf,hfQ,hindex,hJT,hpoint,hquad⟩ :=
    h.replacement_large_movement_point_critical_coordinates d path hb hat hJm
  let S := stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf S
  let A := (Z d.radical z).subgroupOf S
  let L₀ := (Ltilde d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hc : Nat.card B.Carrier < Nat.card (A.map f) := by
    have hh := Sp4Four.SourceComparison.quotient_image_card (Z d.radical z) S
      (Q d.radical a) hzS f hfQ
    rw [MonoidHom.range_comp,inclusion_range] at hh
    rw [hh,B.card_eq,hB,←h.field_card]
    exact hlarge
  obtain ⟨g₀,hgen₀⟩ := PointLargeGeneration.exists_point_large_quadratic_generator (T.map f) (A.map f)
    ⟨1,by
      rw [show (MulAut.conj (1 : Sp B.Carrier)).toMonoidHom = MonoidHom.id _ by
        apply MonoidHom.ext
        intro y
        change 1*y*1⁻¹=y
        group,Subgroup.map_id]
      exact hpoint⟩ hquad hc
  have hL : L₀.map f = ⊤ := by
    have he : L₀ = pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two (by
      rw [B.card_eq,hB]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary))
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,hfg⟩ := (show g₀ ∈ L₀.map f by rw [hL]; trivial)
  have hkT : f.ker ≤ T := by
    intro y hy
    have hyQ : y.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hy
    have ht : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical hat
      rw [path.start_color] at hh
      cases ht : color d.radical t <;> simp_all
    exact Q_le_adjacent_h d.radical ht hat hyQ
  have hkg : f.ker ≤ T.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hkT
    simpa only [MulEquiv.toMonoidHom_eq_coe,Subgroup.Normal.map_conj_eq] using hh
  have hgen : T.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    have hm : (T.map (MulAut.conj g).toMonoidHom ⊔ A).map f = ⊤ := by
      rwa [Subgroup.map_sup,Subgroup.image_conjugate,hfg]
    have hh := congrArg (Subgroup.comap f) hm
    rwa [comap_map_eq_self (hkg.trans le_sup_left),comap_top] at hh
  have hwhole := congrArg (Subgroup.map S.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.image_conjugate,map_subgroupOf_eq_of_le hTS,
    map_subgroupOf_eq_of_le hzS,←MonoidHom.range_eq_map,range_subtype] at hwhole
  refine ⟨g.val,hg,?_⟩
  intro c hct
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  have hc := small_mover_neighbor_card_eq d.radical hat hct (Nat.card F^2)
  rw [hJT] at hc
  have hJc : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) = Q d.radical t :=
    eq_of_le_of_card_ge (Subgroup.SmallMover.join_le _ _ _ _) hc.le
  rw [hJc]
  exact hwhole

/-- Above the small fixed-index cutoff, a single residual conjugator
works for every neighboring mover at every critical image size. -/
theorem Input.replacement_large_movement_generator
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ g ∈ Ltilde d.radical a, ∀ c : Vertex d.radical, Adjacent d.radical c t →
      (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom ⊔
          Z d.radical z = stabilizer d.radical a := by
  by_cases hs : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2
  · exact h.replacement_large_movement_root_generator d path hb hat hs hJm
  have hq : 1 < Nat.card F := Finite.one_lt_card
  exact h.replacement_large_movement_large_generator d path hb hat
    (lt_of_lt_of_le (by nlinarith : Nat.card F < Nat.card F^2) (le_of_not_gt hs)) hJm

/-- On the actual first edge, the same selector satisfies the
full original edge-layer fixed-subgroup clause for every neighboring mover.
Thus the two source selections may coincide in this point-radical branch. -/
theorem Input.replacement_large_movement_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ g ∈ Ltilde d.radical a, ∀ c : Vertex d.radical, Adjacent d.radical c t →
      let Jc := (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom
      Jc ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (Jc : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg,hall⟩ := h.replacement_large_movement_generator d path hb hat hJm
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    exact Ne.symm hh
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length - 1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hfix : Z d.radical t ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    rw [Z,if_neg ht] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2 y (hzT hy)
  refine ⟨g,hg,?_⟩
  intro c hct
  dsimp only
  have hgen := hall c hct
  refine ⟨hgen,?_⟩
  apply le_antisymm
  · refine le_inf inf_le_left (le_centralizer_iff.mpr ?_)
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hfix))
  · have hle : (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom ≤
          stabilizer d.radical a := le_sup_left.trans_eq hgen
    exact inf_le_inf_left _ (centralizer_le hle)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
