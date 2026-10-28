module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NeighborParabolicCrossing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedPointProjection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NeighborEdgeFixed
public import Theory.SpecificGroups.SymplecticFour.NeighborRankOneProjection

/-!
# A contained endpoint and neighboring mover at the same rank-one point

Use the endpoint's Sylow projection to mark a point in the chosen plane.
The unequal neighboring mover crosses a second point core. A rank-one Levi
conjugator places that crossing opposite the endpoint's upper root image.
Lifting this conjugator to the original vertex residual transports the actual
neighbor and edge together. Their generated group has full SL₂ image and
supplements the point two-core in the whole point-local preimage.

The same witnesses retain the endpoint Sylow condition, the literal crossing
between full parabolic preimages, and the neighboring mover's fixed-subgroup
comparison on the whole original edge Z. All original quotient kernels,
central attachments and nonbinary degrees remain present. In particular the
proof does not assume that the neighboring mover contains the original Q.

Source: MS93 (5.5), printed p.916, through the rank-one residual projection
following the definition of F. The analysis of its Sylow subgroup T₀, the
individual/paired generation alternative, the complete source fixed clauses
and backward paths, terminal exclusions and the minimum-replacement witness
are further obligations. The independent original-radical characteristic
control problem is not addressed by this projection.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem core_preimage {S T : Type*} [Group S] [Group T] [Finite S] [Finite T]
    (f : S →* T) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (P : Subgroup T) : (P.comap f).pCoreIn 2 = (P.pCoreIn 2).comap f := by
  have hh := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f (P.comap f) hk
  rw [map_comap_eq_self_of_surjective hf] at hh
  exact hh.symm.trans (inf_eq_right.mpr (comap_mono (pCoreIn_le 2 P)))

private theorem image_intersection_preimage {S T : Type*} [Group S] [Group T]
    (f : S →* T) (D : Subgroup S) (P : Subgroup T) :
    (D ⊓ P.comap f).map f = D.map f ⊓ P := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hxp⟩,rfl⟩
    exact ⟨mem_map_of_mem f hx,hxp⟩
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x,⟨hx,hp⟩,rfl⟩

private theorem lift_supplement {S T : Type*} [Group S] [Group T]
    (f : S →* T) (hf : Function.Surjective f) (D : Subgroup S) (L C : Subgroup T)
    (hgen : D.map f ⊓ L ⊔ C = L) :
    (D ⊓ L.comap f) ⊔ C.comap f = L.comap f := by
  have hm : ((D ⊓ L.comap f) ⊔ C.comap f).map f = L := by
    rw [Subgroup.map_sup,image_intersection_preimage,map_comap_eq_self_of_surjective hf,hgen]
  have hk : f.ker ≤ (D ⊓ L.comap f) ⊔ C.comap f := (ker_le_comap _ _).trans le_sup_right
  exact (comap_map_eq_self hk).symm.trans (congrArg (Subgroup.comap f) hm)

private theorem mover_act {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (g : FreeAmalgam R) (a t : Vertex R) (q : ℕ) :
    Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) q =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) q).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- For a contained large endpoint, select an actual neighboring mover
whose crossing uses the same point as the endpoint's Sylow projection.
The subgroup they generate supplements the full point-parabolic two-core
inside the literal point-local preimage. No containment of Q in the mover
is assumed, and the original neighboring vertices are transported together. -/
theorem Input.replacement_contained_neighbor_rankOne_projection_normalized
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
            let P := pointParabolic.comap f'
            let L := pointLocal.comap f'
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
            ((A.map f').subgroupOf pointLocal).map pointQuotient =
              Matrix.SpecialLinearGroup.upperUnipotent B.Carrier ∧
            (∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype = A ⊔ P.pCoreIn 2) ∧
            (∃ s w : Sp B.Carrier, s∈planeLocal ∧ s∉pointParabolic ∧
              f u*f v=w ∧ w*s∈pointLocal ∧
              ((planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).comap f' ≤ L ∧
              ¬ E ⊓ ((planeParabolic.map (MulAut.conj w).toMonoidHom).comap f').pCoreIn 2 ≤
                P.pCoreIn 2) ∧
            (((A ⊔ E).map f').subgroupOf pointLocal).map pointQuotient = ⊤ ∧
            (A ⊔ E) ⊓ L ⊔ P.pCoreIn 2 = L) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_unequal_mover_parabolic_crossing_normalized d geometry hb path.start_color hat
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained
  obtain ⟨u,hu,hup,hun,hf',hker,hAP,hproj,T,hT⟩ :=
    h.replacement_contained_endpoint_sylow_projection d path hb B hB f hf hfQ hlarge hcontained
  let S := stabilizer d.radical a
  let A := (Z d.radical z).subgroupOf S
  let E₀ := (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)).subgroupOf S
  let f' := (MulAut.conj (f u)).toMonoidHom.comp f
  let P := pointParabolic.comap f'
  let L := pointLocal.comap f'
  let := finite_stabilizer d.radical a
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective _).symm
  have hk : IsPGroup 2 f.ker := by
    rw [hQeq]
    exact (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a path.start_color).comap_subtype
  have hk' : IsPGroup 2 f'.ker := by rw [hker]; exact hk
  obtain ⟨s,hs,hsp,hcross⟩ := hall c hct hne
  have hcross₀ : ¬ E₀.map f ⊓ (planeParabolic (F := B.Carrier)).pCoreIn 2 ≤
      (pointParabolic.map (MulAut.conj s).toMonoidHom).pCoreIn 2 := by
    intro hle
    apply hcross
    rw [core_preimage f hf hk,core_preimage f hf hk]
    intro x hx
    exact hle ⟨mem_map_of_mem f hx.1,hx.2⟩
  obtain ⟨w,hws,hwp,hwcross,hwgen,hwsupp⟩ :=
    NeighborRankOneProjection.exists_rankOne_projection B.card_eq
      (by rw [hB]; exact h.nonbinary) (A.map f') (E₀.map f) hproj s hs hcross₀
  let L₀ := (Ltilde d.radical a).subgroupOf S
  have hq : 2<Nat.card B.Carrier := by
    rw [B.card_eq,hB]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hL : L₀.map f=⊤ := by
    have he : L₀=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two hq
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨v,hv,hfv⟩ := (show (f u)⁻¹*w∈L₀.map f by rw [hL]; trivial)
  let t₁ := act d.radical v.val⁻¹ t
  let c₁ := act d.radical v.val⁻¹ c
  let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
    (Q d.radical t₁) (Nat.card F^2)).subgroupOf S
  have hva : act d.radical v.val⁻¹ a = a := S.inv_mem v.property
  have hat₁ : Adjacent d.radical a t₁ := by
    rw [←hva]
    exact (adjacent_act_iff d.radical v.val⁻¹ _ _).mpr hat
  have hct₁ : Adjacent d.radical c₁ t₁ :=
    (adjacent_act_iff d.radical v.val⁻¹ _ _).mpr hct
  have hmove (b : Vertex d.radical) :=
    mover_act d.radical v.val⁻¹ b t (Nat.card F^2)
  have hne₁ : Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
      (Q d.radical t₁) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t₁) (Nat.card F^2) := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj v.val).toMonoidHom) (MulAut.conj v.val).injective
    have hc := hmove c
    have ha := hmove a
    simp only [inv_inv] at hc
    simp only [hva,inv_inv] at ha
    exact hc.symm.trans (he.trans ha)
  have hfixed := h.replacement_unequal_selected_edge_fixed d geometry hb
    path.start_color hat hat₁ hct₁ hne₁
  have hES : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≤ S :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 a (adjacent_symm d.radical hat))
  have hES₁ : Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
      (Q d.radical t₁) (Nat.card F^2) ≤ S :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 a (adjacent_symm d.radical hat₁))
  have hEconj : E = E₀.map (MulAut.conj v).toMonoidHom := by
    apply map_injective S.subtype_injective
    rw [Subgroup.image_conjugate,map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hES₁]
    simpa only [c₁,t₁,Subgroup.coe_subtype,inv_inv] using mover_act d.radical v.val⁻¹ c t (Nat.card F^2)
  have hEimage : E.map f' = (E₀.map f).map (MulAut.conj w).toMonoidHom := by
    rw [hEconj,Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change f u*f (v*x*v⁻¹)*(f u)⁻¹=w*f x*w⁻¹
    rw [map_mul,map_mul,map_inv,hfv]
    group
  have hgen : (((A ⊔ E).map f').subgroupOf pointLocal).map pointQuotient = ⊤ := by
    rw [Subgroup.map_sup,hEimage]
    exact hwgen
  have hsupp : (A ⊔ E) ⊓ L ⊔ P.pCoreIn 2 = L := by
    rw [core_preimage f' hf' hk']
    apply lift_supplement f' hf'
    rw [Subgroup.map_sup,hEimage]
    exact hwsupp
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,⟨T,hT⟩,?_,hgen,hsupp⟩
  refine ⟨s,w,hs,hsp,?_,hws,?_,?_⟩
  · rw [hfv]
    group
  · rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj w).injective]
    exact comap_mono hwp
  · rw [core_preimage f' hf' hk',core_preimage f' hf' hk']
    intro hle
    apply hwcross
    rw [←hEimage]
    rintro y ⟨⟨x,hx,rfl⟩,hp⟩
    exact hle ⟨hx,hp⟩

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_rankOne_projection
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
            let P := pointParabolic.comap f'
            let L := pointLocal.comap f'
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
            ((A.map f').subgroupOf pointLocal).map pointQuotient =
              Matrix.SpecialLinearGroup.upperUnipotent B.Carrier ∧
            (∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype = A ⊔ P.pCoreIn 2) ∧
            (∃ s w : Sp B.Carrier, s∈planeLocal ∧ s∉pointParabolic ∧
              f u*f v=w ∧ w*s∈pointLocal ∧
              ((planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).comap f' ≤ L ∧
              ¬ E ⊓ ((planeParabolic.map (MulAut.conj w).toMonoidHom).comap f').pCoreIn 2 ≤
                P.pCoreIn 2) ∧
            (((A ⊔ E).map f').subgroupOf pointLocal).map pointQuotient = ⊤ ∧
            (A ⊔ E) ⊓ L ⊔ P.pCoreIn 2 = L) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_rankOne_projection_normalized d path hb hat hct hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
