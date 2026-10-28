module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedPointDichotomy
public import Theory.SpecificGroups.SymplecticFour.MoverNormalizer

/-!
# The actual neighboring mover determines the marked Sylow root pair

Retain the original point-dichotomy witnesses, quotient marking and full
kernel. In its central branch, the neighboring mover's whole-U index forces
it outside the original plane core. Conjugation by the same residual element
puts it in the endpoint join, so the model normalizer calculation applies
to the literal intersection with the marked plane core.

That intersection is a product of two distinct full roots. It is exactly
every source Sylow T₀ in the two marked parabolics, and the actual mover has
index two over its intersection with T₀. The whole-edge fixed-subgroup
comparison, endpoint projection and original nonbinary degree are retained
on these same witnesses.

Source: MS93 (5.5), printed pp.916--917. Applying (5.1) to derive full-Q
containment, the source intersection bound and individual/paired generation
remains necessary. This does not establish the terminal distance exclusion
or the minimum characteristic-replacement distance-two witness.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same contained-endpoint selector has a genuine marked root pair
and index-two mover action in the central-intersection branch. -/
theorem Input.replacement_contained_neighbor_root_pair_normalized
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
            (A ⊔ E) ⊓ L ⊔ P.pCoreIn 2 = L ∧
            let D := ((A ⊔ E).map f').subgroupOf pointLocal
            D = ⊤ ∨
              (D ⊓ pointRadical = center (pointLocal (F := B.Carrier)) ∧
                Nat.card (A.map f') = Nat.card B.Carrier^2 ∧
                (A.map f').subgroupOf pointLocal ⊓ pointRadical =
                  center (pointLocal (F := B.Carrier)) ∧
                D ⊓ (Matrix.SpecialLinearGroup.upperUnipotent B.Carrier).comap pointQuotient =
                  (A.map f').subgroupOf pointLocal ∧
                (∀ s w : Sp B.Carrier, s∈planeLocal → w*s∈pointLocal →
                  ∀ T₀ : Sylow 2 ((A ⊔ E).map f' ⊓
                    planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                      Subgroup (Sp B.Carrier)),
                    Nat.card T₀ = Nat.card B.Carrier^2 ∧
                      (((T₀ : Subgroup ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                          Subgroup (Sp B.Carrier))).map
                        ((A ⊔ E).map f' ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓
                          pointParabolic).subtype).subgroupOf pointLocal) ⊓ pointRadical =
                            center (pointLocal (F := B.Carrier))) ∧
                ∀ s w : Sp B.Carrier, s∈planeLocal → s∉pointParabolic →
                  f u*f v=w → w*s∈pointLocal →
                  ((planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).comap f' ≤ L →
                  ∃ r b : B.Carrier, b≠0 ∧
                    (((A ⊔ E).map f' ⊓
                      (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).map
                        (MulAut.conj w⁻¹).toMonoidHom =
                      CentralRootGeometry.SmallMovers.rootImage (some r) ⊔
                        CentralRootGeometry.SmallMovers.rootImage (some (r+b))) ∧
                    (((A ⊔ E).map f' ⊓
                      (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).relIndex (E.map f') = 2) ∧
                    (∀ T₀ : Sylow 2 ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp B.Carrier)),
                      (T₀ : Subgroup ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp B.Carrier))).map
                        ((A ⊔ E).map f' ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic).subtype =
                          (A ⊔ E).map f' ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2) ∧
                    ∀ e u₀ z₀ v₀ : B.Carrier,
                      (CentralRootGeometry.element e u₀ z₀ v₀).val ∈
                        ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                          (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f →
                        e=0 ∨ e=b)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_point_dichotomy_normalized d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,hD⟩ :=
    hall hcontained
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,?_⟩
  rcases hD with hD | ⟨hDR,hsize,hAR,hupper,hT₀⟩
  · exact Or.inl hD
  right
  refine ⟨hDR,hsize,hAR,hupper,hT₀,?_⟩
  intro s w hs hsp hw hws hcore
  let S := stabilizer d.radical a
  let A := (Z d.radical z).subgroupOf S
  let f' := (MulAut.conj (f u)).toMonoidHom.comp f
  let E₀ := (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)).subgroupOf S
  let t₁ := act d.radical v.val⁻¹ t
  let c₁ := act d.radical v.val⁻¹ c
  let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
    (Q d.radical t₁) (Nat.card F^2)).subgroupOf S
  have hES : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≤ S :=
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
  have hEimage : E.map f' = (E₀.map f).map (MulAut.conj w).toMonoidHom := by
    rw [hEconj,Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change f u*f (v*x*v⁻¹)*(f u)⁻¹=w*f x*w⁻¹
    rw [map_mul,map_mul,map_inv,←hw]
    group
  have hEU : E₀.map f ≤ unipotent :=
    (map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf
  have hout : ¬ E₀.map f ≤ (CentralRootGeometry.wing true).map unipotent.subtype := by
    intro hle
    let E₁ := (E₀.map f).subgroupOf unipotent
    have hE₁ : E₁.map unipotent.subtype = E₀.map f := map_subgroupOf_eq_of_le hEU
    have hwingle : E₁ ≤ CentralRootGeometry.wing true := by
      apply (map_le_map_iff_of_injective unipotent.subtype_injective).mp
      rwa [hE₁]
    have hmove := movingIndex_le_field_sq_of_le_wing E₁ hwingle
    rw [←binary_movingIndex] at hmove
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) E₁ ≤ _ at hmove
    rw [fixedCodim,fixedSpace_comp_map,hE₁] at hmove
    have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
    have hi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES,hindex] at hi
    have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
    have hbig := (h.replacement_unequal_individual_indices d geometry hb path.start_color
      hat hct hne).2
    change 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)) (E₀.map f) ≤ Nat.card B.Carrier^2 at hmove
    rw [←hi,hBF] at hmove
    exact hbig.not_ge hmove
  have hEJ : (E₀.map f).map (MulAut.conj w).toMonoidHom ≤ (A ⊔ E).map f' := by
    rw [←hEimage]
    exact map_mono le_sup_right
  have hcore' : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal := by
    intro x hx
    obtain ⟨y,rfl⟩ := hf' x
    exact hcore hx
  obtain ⟨r,b,hb',hpair,hsize',hindex',hcoords⟩ :=
    MoverNormalizer.marked_plane_intersection_root_pair B.card_eq
      (by rw [hB]; exact h.nonbinary) ((A ⊔ E).map f') (E₀.map f) hEU hout s w hs hsp hws hEJ hcore' hDR
  refine ⟨r,b,hb',hpair,?_,?_,hcoords⟩
  · rwa [←hEimage] at hindex'
  · intro T₀
    exact MoverNormalizer.marked_sylow_eq_plane_intersection ((A ⊔ E).map f') w hcore' hsize' T₀
      (hT₀ s w hs hws T₀).1

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_root_pair
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
            (A ⊔ E) ⊓ L ⊔ P.pCoreIn 2 = L ∧
            let D := ((A ⊔ E).map f').subgroupOf pointLocal
            D = ⊤ ∨
              (D ⊓ pointRadical = center (pointLocal (F := B.Carrier)) ∧
                Nat.card (A.map f') = Nat.card B.Carrier^2 ∧
                (A.map f').subgroupOf pointLocal ⊓ pointRadical =
                  center (pointLocal (F := B.Carrier)) ∧
                D ⊓ (Matrix.SpecialLinearGroup.upperUnipotent B.Carrier).comap pointQuotient =
                  (A.map f').subgroupOf pointLocal ∧
                (∀ s w : Sp B.Carrier, s∈planeLocal → w*s∈pointLocal →
                  ∀ T₀ : Sylow 2 ((A ⊔ E).map f' ⊓
                    planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                      Subgroup (Sp B.Carrier)),
                    Nat.card T₀ = Nat.card B.Carrier^2 ∧
                      (((T₀ : Subgroup ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                          Subgroup (Sp B.Carrier))).map
                        ((A ⊔ E).map f' ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓
                          pointParabolic).subtype).subgroupOf pointLocal) ⊓ pointRadical =
                            center (pointLocal (F := B.Carrier))) ∧
                ∀ s w : Sp B.Carrier, s∈planeLocal → s∉pointParabolic →
                  f u*f v=w → w*s∈pointLocal →
                  ((planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).comap f' ≤ L →
                  ∃ r b : B.Carrier, b≠0 ∧
                    (((A ⊔ E).map f' ⊓
                      (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).map
                        (MulAut.conj w⁻¹).toMonoidHom =
                      CentralRootGeometry.SmallMovers.rootImage (some r) ⊔
                        CentralRootGeometry.SmallMovers.rootImage (some (r+b))) ∧
                    (((A ⊔ E).map f' ⊓
                      (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).relIndex (E.map f') = 2) ∧
                    (∀ T₀ : Sylow 2 ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp B.Carrier)),
                      (T₀ : Subgroup ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp B.Carrier))).map
                        ((A ⊔ E).map f' ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic).subtype =
                          (A ⊔ E).map f' ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2) ∧
                    ∀ e u₀ z₀ v₀ : B.Carrier,
                      (CentralRootGeometry.element e u₀ z₀ v₀).val ∈
                        ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                          (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f →
                        e=0 ∨ e=b)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_root_pair_normalized d path hb hat hct hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
