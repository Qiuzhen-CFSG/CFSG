module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedOriginalFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedEdgeGeneration
public import Theory.SpecificGroups.SymplecticFour.PointIndividualGeneration
public import Theory.GroupTheory.Amalgam.NormalSubamalgam
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Individual or paired generation for the actual contained endpoint

The whole-point-local branch now gives full symplectic image: the selected
unequal mover fixes a different point in the same marking. Its original
Q-kernel normalizes the mover, so the normal-closure argument lifts generation
to containment of the entire vertex residual without assuming Q lies in it.
The other branch uses the already constructed shear and full-Q paired generation.

The endpoint, original neighbor, two residual conjugators and quotient kernel
are retained throughout. In the smaller-J plane branch, the same selector
also generates with the whole edge. ContainedGenerationPaths retains both
edge-generation identities and fixed clauses; ContainedPairedPaths constructs
both backward paths on those witnesses.
Source: MS93 (5.5)(a,c), printed pp.915--917. Terminal distance exclusion and
the minimum-replacement witness remain further obligations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
private theorem residual_le_individual_join {G D : Type*} [Group G] [Group D]
    (f : G →* D) (E A : Subgroup G) (hk : IsPGroup 2 f.ker)
    (hA : IsPGroup 2 A) (hn : f.ker ≤ normalizer (E : Set G))
    (hgen : (E ⊔ A).map f = ⊤) : pResidual 2 G ≤ E ⊔ A := by
  have htop : (E ⊔ A) ⊔ f.ker = ⊤ := by
    rw [←comap_map_eq,hgen,comap_top]
  let N := normalClosure (E : Set G)
  have hN : N ≤ E ⊔ A := normalClosure_le_of_normal_supplement f.ker (E ⊔ A) E
    (by rwa [sup_comm]) hn le_sup_left
  have hNtop : N ⊔ (A ⊔ f.ker) = ⊤ := by
    apply top_unique
    rw [←htop]
    exact sup_le (sup_le (le_normalClosure.trans le_sup_left)
      (le_sup_left.trans le_sup_right)) (le_sup_right.trans le_sup_right)
  have hquot := isPGroup_quotient_of_sup_eq_top N (A ⊔ f.ker)
    (hA.to_sup_of_normal_right hk) hNtop
  exact (show pResidual 2 G ≤ N from sInf_le ⟨inferInstance,hquot⟩).trans hN

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same selected unequal mover either individually generates the residual
with the endpoint, or has the actual paired-generation and full-Q exception. -/
theorem Input.replacement_contained_neighbor_generation_alternative_with_edge_original_fixed_normalized
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
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
            (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₁)
                (Q d.radical c₁) (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
              Z d.radical t ⊓ centralizer (Q d.radical t₁ : Set (FreeAmalgam d.radical))) ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
              (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
                ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f →
              A ⊔ ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map
                (MulAut.conj v).toMonoidHom = ⊤ ∧
              Z d.radical t ⊓ centralizer ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                (Q d.radical t) (Nat.card F^2)).map (MulAut.conj v.val).toMonoidHom : Set (FreeAmalgam d.radical)) =
                  Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E) ∨
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
                ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
                  f' x = (pointRadicalElement (1:B.Carrier) 0 0).val ∧
                  f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_paired_generation_normalized d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,hD⟩ :=
    hall hcontained
  have hedge : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f →
      (Z d.radical z).subgroupOf (stabilizer d.radical a) ⊔
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map
          (MulAut.conj v).toMonoidHom = ⊤ ∧
        Z d.radical t ⊓ centralizer ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                (Q d.radical t) (Nat.card F^2)).map (MulAut.conj v.val).toMonoidHom : Set (FreeAmalgam d.radical)) =
                  Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    intro hJplane
    obtain ⟨s,w,hs,hsp,hw,hws,hcore,hcross'⟩ := hcross
    have hcore' : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal := by
      intro y hy
      obtain ⟨k,rfl⟩ := hf' y
      exact hcore hy
    have hva : act d.radical v.val⁻¹ a=a := (stabilizer d.radical a).inv_mem v.property
    have hES : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) ≤ stabilizer d.radical a :=
      (Subgroup.SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 a (adjacent_symm d.radical hat))
    have hES₁ : Subgroup.SmallMover.join (U d.radical (act d.radical v.val⁻¹ c))
        (Q d.radical (act d.radical v.val⁻¹ c)) (Q d.radical (act d.radical v.val⁻¹ t))
          (Nat.card F^2) ≤ stabilizer d.radical a :=
      (Subgroup.SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 a (adjacent_symm d.radical hat₁))
    have he : (Subgroup.SmallMover.join (U d.radical (act d.radical v.val⁻¹ c))
        (Q d.radical (act d.radical v.val⁻¹ c)) (Q d.radical (act d.radical v.val⁻¹ t))
          (Nat.card F^2)).subgroupOf (stabilizer d.radical a) =
        ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map
            (MulAut.conj v).toMonoidHom := by
      apply map_injective (stabilizer d.radical a).subtype_injective
      rw [Subgroup.image_conjugate,map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hES₁,
        U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj v.val).injective]
      simp only [inv_inv,Subgroup.coe_subtype]
    constructor
    · apply h.replacement_contained_marked_edge_generation d path hb hat hct hne hlarge
        B hB f hf hfQ hTf hindex hJplane u v s w hs hsp hw hws hcore' hAP hproj
      rwa [he] at hgen
    · apply h.replacement_contained_marked_original_fixed d geometry hb path.start_color hat hct hne
        B hB f hf hfQ hTf hindex hJplane
        (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map
          ((MulAut.conj (f u)).toMonoidHom.comp f)) u v hup hun hAP
      · rwa [hw]
      · rw [Subgroup.map_sup,he] at hgen
        have himage : (((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map
              (MulAut.conj v).toMonoidHom).map ((MulAut.conj (f u)).toMonoidHom.comp f) =
          (((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f).map
              (MulAut.conj (f u*f v)).toMonoidHom := by
          rw [Subgroup.map_map,Subgroup.map_map]
          congr 1
          apply MonoidHom.ext
          intro y
          change f u*f (v*y*v⁻¹)*(f u)⁻¹=(f u*f v)*f y*(f u*f v)⁻¹
          rw [map_mul,map_mul,map_inv]
          group
        rwa [himage] at hgen
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hedge,?_⟩
  rcases hD with hD | ⟨hQorig,hQsel,hcaporig,hcapsel,hnonsplit,hDR,hsize,hAR,hupper,hT₀,hroots⟩
  swap
  · right
    obtain ⟨s,w,hs,hsp,hw,hws,hcore,hcross'⟩ := hcross
    obtain ⟨r,b,hb',hpair,hidx,hTeq,hcoords,x,hx,hfx,hxc,hxc₀,hlocal,hwhole⟩ :=
      hroots s w hs hsp hw hws hcore
    exact ⟨hQorig,hQsel,hcaporig,hcapsel,hnonsplit,x,hx,hfx,hxc,hxc₀,hwhole⟩
  left
  let := finite_stabilizer d.radical a
  let S := stabilizer d.radical a
  let A := (Z d.radical z).subgroupOf S
  let f' := (MulAut.conj (f u)).toMonoidHom.comp f
  let Eorig := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let E₀ := Eorig.subgroupOf S
  let t₁ := act d.radical v.val⁻¹ t
  let c₁ := act d.radical v.val⁻¹ c
  let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
    (Q d.radical t₁) (Nat.card F^2)).subgroupOf S
  have hES : Eorig ≤ S :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 a (adjacent_symm d.radical hat))
  have hES₁ : Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
      (Q d.radical t₁) (Nat.card F^2) ≤ S :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 a (adjacent_symm d.radical hat₁))
  have hEconj : E = E₀.map (MulAut.conj v).toMonoidHom := by
    apply map_injective S.subtype_injective
    rw [Subgroup.image_conjugate,map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hES₁]
    dsimp only [c₁,t₁]
    rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj v.val).injective]
    simp only [inv_inv,Subgroup.coe_subtype]
  obtain ⟨s,w,hs,hsp,hw,hws,hcore,hcross'⟩ := hcross
  have hEimage : E.map f' = (E₀.map f).map (MulAut.conj w).toMonoidHom := by
    rw [hEconj,Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change f u*f (v*x*v⁻¹)*(f u)⁻¹=w*f x*w⁻¹
    rw [map_mul,map_mul,map_inv,←hw]
    group
  have hwP : w ∉ pointParabolic := by
    intro hwP
    exact hsp (by simpa only [inv_mul_cancel_left] using
      pointParabolic.mul_mem (pointParabolic.inv_mem hwP) (pointLocal_le hws))
  let E₁ := (E₀.map f).subgroupOf unipotent
  have hEf : E₀.map f ≤ unipotent :=
    (map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf
  have hE₁ : E₁.map unipotent.subtype = E₀.map f := map_subgroupOf_eq_of_le hEf
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hmove : movingIndex E₁ =
      (centralizer (Eorig : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) E₁ = _
    rw [fixedCodim,fixedSpace_comp_map,hE₁]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES,hindex] at hh
    exact hh.symm
  have hbig : Nat.card B.Carrier^2 < movingIndex E₁ := by
    rw [hmove,show Nat.card B.Carrier=Nat.card F by rw [B.card_eq,hB,h.field_card]]
    exact (h.replacement_unequal_individual_indices d geometry hb path.start_color hat hct hne).2
  have hfull : (A ⊔ E).map f' = ⊤ := by
    rw [Subgroup.map_sup,hEimage,←hE₁]
    apply PointIndividualGeneration.generate_of_pointLocal_le B.card_eq
      (by rw [hB]; exact h.nonbinary) (A.map f') E₁
      (fixed_eq_point_and_movingIndex_of_square_lt E₁ hbig).1 w hwP
    rw [hE₁,←hEimage,←Subgroup.map_sup]
    intro y hy
    exact (show (⟨y,hy⟩ : pointLocal) ∈ ((A ⊔ E).map f').subgroupOf pointLocal from
      hD.symm ▸ mem_top _)
  have hQeq : f'.ker = (Q d.radical a).subgroupOf S := by
    rw [hker,←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective _).symm
  have hQp : IsPGroup 2 f'.ker := by
    rw [hQeq]
    exact (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a path.start_color).comap_subtype
  let : IsElementaryAbelian 2 (Z d.radical z) := geometry.Z_elementary (by omega) z path.end_color
  have hAp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z d.radical z)).comap_subtype
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hTc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 c (adjacent_symm d.radical hct)
  have hTE : Q d.radical t ≤ normalizer (Eorig : Set (FreeAmalgam d.radical)) :=
    (le_inf (le_inf (hTc.trans (U_normalized c))
      (hTc.trans (Q_normalized d.radical c))) (Q d.radical t).le_normalizer).trans
      (Subgroup.SmallMover.normalizer_join _ _ _ _)
  have hQn : f'.ker ≤ normalizer (E₀ : Set S) := by
    rw [hQeq]
    exact (comap_mono (hQT.trans hTE)).trans (Eorig.le_normalizer_comap S.subtype)
  have hQn' : f'.ker ≤ normalizer (E : Set S) := by
    rw [hEconj]
    have hh := (map_mono (f := (MulAut.conj v).toMonoidHom) hQn).trans
      (le_normalizer_map (MulAut.conj v).toMonoidHom)
    simpa only [MulEquiv.toMonoidHom_eq_coe,Subgroup.Normal.map_conj_eq] using hh
  rw [sup_comm]
  exact residual_le_individual_join f' E A hQp hAp hQn' (by rwa [sup_comm])

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_generation_alternative_with_edge_original_fixed
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
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
            (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₁)
                (Q d.radical c₁) (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
              Z d.radical t ⊓ centralizer (Q d.radical t₁ : Set (FreeAmalgam d.radical))) ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
              (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
                ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f →
              A ⊔ ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map
                (MulAut.conj v).toMonoidHom = ⊤ ∧
              Z d.radical t ⊓ centralizer ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                (Q d.radical t) (Nat.card F^2)).map (MulAut.conj v.val).toMonoidHom : Set (FreeAmalgam d.radical)) =
                  Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E) ∨
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
                ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
                  f' x = (pointRadicalElement (1:B.Carrier) 0 0).val ∧
                  f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_generation_alternative_with_edge_original_fixed_normalized d path hb hat hct hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

/-- The original edge-generation interface, retaining its public statement. -/
theorem Input.replacement_contained_neighbor_generation_alternative_with_edge
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
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
            (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₁)
                (Q d.radical c₁) (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
              Z d.radical t ⊓ centralizer (Q d.radical t₁ : Set (FreeAmalgam d.radical))) ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
              (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
                ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f →
              A ⊔ ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map
                (MulAut.conj v).toMonoidHom = ⊤) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E) ∨
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
                ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
                  f' x = (pointRadicalElement (1:B.Carrier) 0 0).val ∧
                  f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩ :=
    h.replacement_contained_neighbor_generation_alternative_with_edge_original_fixed d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,?_⟩
  intro hcontained
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hedge,hD⟩ := hall hcontained
  exact ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,(fun hJplane => (hedge hJplane).1),hD⟩

/-- The individual/paired alternative, retaining the original public interface.
The stronger same-witness theorem also supplies generation by the selected edge. -/
theorem Input.replacement_contained_neighbor_generation_alternative
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
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
            (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₁)
                (Q d.radical c₁) (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
              Z d.radical t ⊓ centralizer (Q d.radical t₁ : Set (FreeAmalgam d.radical))) ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E) ∨
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
                ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
                  f' x = (pointRadicalElement (1:B.Carrier) 0 0).val ∧
                  f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                  (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩ :=
    h.replacement_contained_neighbor_generation_alternative_with_edge d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,?_⟩
  intro hcontained
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hedge,hD⟩ := hall hcontained
  exact ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hD⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
