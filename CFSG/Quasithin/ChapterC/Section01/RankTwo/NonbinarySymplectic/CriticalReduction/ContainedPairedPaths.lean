module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedGenerationPaths

/-!
# Both backward paths at the contained individual/paired selector

Each actual selected edge generates the vertex group with the whole critical
endpoint. Thus that endpoint cannot normalize the corresponding neighboring
seed join: the edge already normalizes it, whereas MS3's original neighbor
join is not vertex-normal. If either seed were trapped in the penultimate
kernel, the critical-pair comparison would force endpoint image order q,
contradicting its retained q² lower bound.

Both backward paths therefore exist on the very same v and shear x, even
in the exceptional paired-mover branch. Every overlap, full-Z fixed clause,
B-relative U-index, quotient marking, full-Q intersection bound and whole-X
nonsplitting alternative is retained. This is the contained branch of
MS93 (5.5) and (5.7), pp.915--919; it does not assert the terminal distance
exclusion or the final minimum-replacement witness.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem backward_of_edge
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (g : stabilizer d.radical a)
    (hwholeEdge : Q d.radical (act d.radical g.val⁻¹ t) ⊔ Z d.radical z =
      stabilizer d.radical a) :
    let c₁ := act d.radical g.val⁻¹ c
    let t₁ := act d.radical g.val⁻¹ t
    Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
    ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = t₁ ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) := by
  let S := stabilizer d.radical a
  let c₁ := act d.radical g.val⁻¹ c
  let t₁ := act d.radical g.val⁻¹ t
  have hga : act d.radical g.val⁻¹ a=a := S.inv_mem g.property
  have hat₁ : Adjacent d.radical a t₁ := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g.val⁻¹ _ _).mpr hat
  have hct₁ : Adjacent d.radical c₁ t₁ := (adjacent_act_iff d.radical g.val⁻¹ _ _).mpr hct
  have hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hbad
    have hTN := edge_normalizes_neighbor_seed_join hat₁ hct₁
    have hwhole : S ≤ normalizer
        ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      change stabilizer d.radical a ≤ _
      rw [←hwholeEdge]
      exact sup_le hTN hbad
    have hZa : (Z d.radical a).map (MulAut.conj g.val⁻¹).toMonoidHom = Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (S.inv_mem g.property))
    have hZc : (Z d.radical c₁).map (MulAut.conj g.val⁻¹).toMonoidHom = Z d.radical c := by
      rw [show Z d.radical c₁ = (Z d.radical c).map (MulAut.conj g.val).toMonoidHom by
        simp only [c₁,Z_act,inv_inv],Subgroup.map_map]
      have hh : (MulAut.conj g.val⁻¹).toMonoidHom.comp (MulAut.conj g.val).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro x
        change g.val⁻¹*(g.val*x*g.val⁻¹)*(g.val⁻¹)⁻¹=x
        group
      rw [hh,Subgroup.map_id]
    have hm := map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) hwhole
    have hSm : S.map (MulAut.conj g.val⁻¹).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem g.property))
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g.val⁻¹).bijective,
      Subgroup.map_sup,hZc,hZa,hSm] at hm
    exact hnormal hm
  refine ⟨hwholeEdge,hn,?_⟩
  have hnot : ¬ Z d.radical c₁ ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    intro hk
    have hYV : Z d.radical c₁ ≤ V d.radical a :=
      le_sup_left.trans (neighbor_seed_join_le_radius hat₁ hct₁)
    have hYS : Z d.radical c₁ ≤ stabilizer d.radical z :=
      (le_inf hYV hk).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
    have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
    obtain ⟨_,hi⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
      (by omega) (Z d.radical c₁) hYS hYQ hn
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  exact exists_backward_path_of_not_le geometry (by omega) path hat₁ hct₁ hnot

/-- The same contained selector supplies both overlapping backward critical
paths together with its individual/paired residual generation alternative. -/
theorem Input.replacement_contained_neighbor_paired_paths_original_fixed_normalized
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        unipotent ≤ normalizer
          (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp B.Carrier)) ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
            (CentralRootGeometry.wing true).map unipotent.subtype →
          (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
              ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f →
          ∃ u v : stabilizer d.radical a,
            u.val∈Ltilde d.radical a ∧ v.val∈Ltilde d.radical a ∧
            f u∈planeLocal ∧ f u∉pointParabolic ∧
            let f' := (MulAut.conj (f u)).toMonoidHom.comp f
            let A := (Z d.radical z).subgroupOf (stabilizer d.radical a)
            let t₁ := act d.radical v.val⁻¹ t
            let c₁ := act d.radical v.val⁻¹ c
            let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
              (Q d.radical t₁) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
            Function.Surjective f' ∧ f'.ker=f.ker ∧
            Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
              f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              let t₂ := act d.radical x.val⁻¹ t₁
              let c₂ := act d.radical x.val⁻¹ c₁
              Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
              Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
              Q d.radical t₂ ⊔ Z d.radical z = stabilizer d.radical a ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₁) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical c) ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₂) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical c) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₂ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₁ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (∃ back : CriticalPath d.radical geometry c₂ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₂ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₂) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E ∧
                pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E.map (MulAut.conj x).toMonoidHom) ∨
              (Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                  (Q d.radical t) (Nat.card F^2) ∧
                Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2) ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                  (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                X d.radical a ≠ U d.radical a ⊔ (X d.radical a ⊓
                  centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
                (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_generation_edge_fixed_original_fixed_normalized d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained hJplane
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hedge₁,hedge₂,hfix₁,hfix₂,hOriginal₁,hOriginal₂,hD⟩ :=
    hall hcontained hJplane
  let S := stabilizer d.radical a
  let t₁ := act d.radical v.val⁻¹ t
  let c₁ := act d.radical v.val⁻¹ c
  let t₂ := act d.radical x.val⁻¹ t₁
  let c₂ := act d.radical x.val⁻¹ c₁
  have hxa : act d.radical x.val⁻¹ a=a := S.inv_mem x.property
  have hat₂ : Adjacent d.radical a t₂ := by
    rw [←hxa]
    exact (adjacent_act_iff d.radical x.val⁻¹ _ _).mpr hat₁
  have hct₂ : Adjacent d.radical c₂ t₂ := (adjacent_act_iff d.radical x.val⁻¹ _ _).mpr hct₁
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0<geometry.b d.radical)
  have hTS₁ : Q d.radical t₁ ≤ S := fun _ hy => hy.2 a (adjacent_symm d.radical hat₁)
  have hwhole₁ : Q d.radical t₁ ⊔ Z d.radical z = S := by
    have hh := congrArg (Subgroup.map S.subtype) hedge₁
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hzS,map_subgroupOf_eq_of_le hTS₁,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact sup_comm _ _ |>.trans hh
  have hwhole₂ : Q d.radical t₂ ⊔ Z d.radical z = S := by
    have hh := congrArg (Subgroup.map S.subtype) hedge₂
    rw [Subgroup.map_sup,Subgroup.image_conjugate,map_subgroupOf_eq_of_le hzS,
      map_subgroupOf_eq_of_le hTS₁,←MonoidHom.range_eq_map,range_subtype] at hh
    have he : Q d.radical t₂ = (Q d.radical t₁).map (MulAut.conj x.val).toMonoidHom := by
      simp only [t₂,Q_act,inv_inv]
    change Z d.radical z ⊔ (Q d.radical t₁).map (MulAut.conj x.val).toMonoidHom = S at hh
    rw [←he] at hh
    exact sup_comm _ _ |>.trans hh
  obtain ⟨_,hn₁,hback₁⟩ := backward_of_edge h d path hb hat hct hnormal hlarge v hwhole₁
  have htcomp : act d.radical (x*v).val⁻¹ t=t₂ := by
    simp only [Subgroup.coe_mul,mul_inv_rev,act_mul,t₂,t₁]
  have hccomp : act d.radical (x*v).val⁻¹ c=c₂ := by
    simp only [Subgroup.coe_mul,mul_inv_rev,act_mul,c₂,c₁]
  obtain ⟨_,hn₂,hback₂⟩ := backward_of_edge h d path hb hat hct hnormal hlarge (x*v)
    (by rw [htcomp]; exact hwhole₂)
  rw [hccomp] at hn₂
  rw [hccomp,htcomp] at hback₂
  have hi₁ := movingIndex_act geometry (d := c) (by omega) path.start_color v.val⁻¹
    (S.inv_mem v.property)
  have hi₂ := movingIndex_act geometry (d := c₁) (by omega) path.start_color x.val⁻¹
    (S.inv_mem x.property)
  have hJ₂ : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t₂) (Nat.card F^2) =
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t₁) (Nat.card F^2)).map
        (MulAut.conj x.val).toMonoidHom := by
    have hU : (U d.radical a).map (MulAut.conj x.val).toMonoidHom = U d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized a x.property)
    have hQ : (Q d.radical a).map (MulAut.conj x.val).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a x.property)
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj x.val).injective,hU,hQ]
    simp only [t₂,Q_act,inv_inv]
  have hOriginal₂' : Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t₂) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical t ⊓ centralizer (S : Set (FreeAmalgam d.radical)) := by
    rw [hJ₂]
    exact hOriginal₂
  exact ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hat₂,hct₂,
    hwhole₁,hwhole₂,hi₁,hi₂.trans hi₁,hn₁,hn₂,hback₁,hback₂,hfix₁,hfix₂,hOriginal₁,hOriginal₂',hD⟩

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_paired_paths_original_fixed
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
            (CentralRootGeometry.wing true).map unipotent.subtype →
          (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
              ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f →
          ∃ u v : stabilizer d.radical a,
            u.val∈Ltilde d.radical a ∧ v.val∈Ltilde d.radical a ∧
            f u∈planeLocal ∧ f u∉pointParabolic ∧
            let f' := (MulAut.conj (f u)).toMonoidHom.comp f
            let A := (Z d.radical z).subgroupOf (stabilizer d.radical a)
            let t₁ := act d.radical v.val⁻¹ t
            let c₁ := act d.radical v.val⁻¹ c
            let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
              (Q d.radical t₁) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
            Function.Surjective f' ∧ f'.ker=f.ker ∧
            Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
              f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              let t₂ := act d.radical x.val⁻¹ t₁
              let c₂ := act d.radical x.val⁻¹ c₁
              Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
              Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
              Q d.radical t₂ ⊔ Z d.radical z = stabilizer d.radical a ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₁) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical c) ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₂) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical c) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₂ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₁ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (∃ back : CriticalPath d.radical geometry c₂ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₂ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₂) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E ∧
                pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E.map (MulAut.conj x).toMonoidHom) ∨
              (Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                  (Q d.radical t) (Nat.card F^2) ∧
                Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2) ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                  (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                X d.radical a ≠ U d.radical a ⊔ (X d.radical a ⊓
                  centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
                (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_paired_paths_original_fixed_normalized d path hb hat hct hne hnormal hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

/-- The original paired-path interface, preserving every original clause. -/
theorem Input.replacement_contained_neighbor_paired_paths
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
            (CentralRootGeometry.wing true).map unipotent.subtype →
          (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
              ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f →
          ∃ u v : stabilizer d.radical a,
            u.val∈Ltilde d.radical a ∧ v.val∈Ltilde d.radical a ∧
            f u∈planeLocal ∧ f u∉pointParabolic ∧
            let f' := (MulAut.conj (f u)).toMonoidHom.comp f
            let A := (Z d.radical z).subgroupOf (stabilizer d.radical a)
            let t₁ := act d.radical v.val⁻¹ t
            let c₁ := act d.radical v.val⁻¹ c
            let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
              (Q d.radical t₁) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
            Function.Surjective f' ∧ f'.ker=f.ker ∧
            Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
              f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              let t₂ := act d.radical x.val⁻¹ t₁
              let c₂ := act d.radical x.val⁻¹ c₁
              Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
              Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
              Q d.radical t₂ ⊔ Z d.radical z = stabilizer d.radical a ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₁) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical c) ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₂) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical c) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₂ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₁ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (∃ back : CriticalPath d.radical geometry c₂ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₂ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E ∧
                pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E.map (MulAut.conj x).toMonoidHom) ∨
              (Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                  (Q d.radical t) (Nat.card F^2) ∧
                Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2) ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                  (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                X d.radical a ≠ U d.radical a ⊔ (X d.radical a ⊓
                  centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
                (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩ :=
    h.replacement_contained_neighbor_paired_paths_original_fixed d path hb hat hct hne hnormal hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,?_⟩
  intro hcontained hJplane
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hat₂,hct₂,hwhole₁,hwhole₂,hi₁,hi₂,hn₁,hn₂,hback₁,hback₂,hfix₁,hfix₂,_,_,hD⟩ := hall hcontained hJplane
  exact ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hat₂,hct₂,hwhole₁,hwhole₂,hi₁,hi₂,hn₁,hn₂,hback₁,hback₂,hfix₁,hfix₂,hD⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
