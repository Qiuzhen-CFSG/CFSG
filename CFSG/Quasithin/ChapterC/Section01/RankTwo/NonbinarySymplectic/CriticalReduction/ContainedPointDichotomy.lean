module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedRankOneProjection
public import Theory.SpecificGroups.SymplecticFour.PointSupplement

/-!
# The point-radical dichotomy for the actual contained-endpoint selector

The same original-degree marking, residual elements and transported neighboring
mover used for the rank-one projection now give the point-local dichotomy.
If their local join is proper, its radical intersection is the whole center.
The original critical endpoint has exactly q² quotient images. Every Sylow
subgroup in the literal intersection with the two marked parabolics also has
order q² and contains the whole point-local center in its radical intersection.

The endpoint's size supplies the lower bound: the radical supplement moves
it into the marked plane stabilizer. Centrality and the SL₂ quotient supply
the upper bound. Thus the small-T₀ case is excluded here, without excluding
the equality boundary or assuming a central complement. The full original
quotient kernel, actual vertices and whole-edge fixed subgroup are retained.

Source: MS93 (5.5), printed pp.916--917. The remaining normalizer calculation
must use the actual unequal mover and (5.1) to produce the source root pair,
full-Q containment and intersection bound. Individual/paired generation,
complete fixed and path clauses, terminal exclusion and the minimum
characteristic-replacement distance-two witness remain separate obligations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The source point-radical dichotomy and exact marked Sylow boundary, for
the same endpoint, unequal mover, residual choices and original quotient map. -/
theorem Input.replacement_contained_neighbor_point_dichotomy_normalized
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
                ∀ s w : Sp B.Carrier, s∈planeLocal → w*s∈pointLocal →
                  ∀ T₀ : Sylow 2 ((A ⊔ E).map f' ⊓
                    planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                      Subgroup (Sp B.Carrier)),
                    Nat.card T₀ = Nat.card B.Carrier^2 ∧
                      (((T₀ : Subgroup ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                          Subgroup (Sp B.Carrier))).map
                        ((A ⊔ E).map f' ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓
                          pointParabolic).subtype).subgroupOf pointLocal) ⊓ pointRadical =
                            center (pointLocal (F := B.Carrier)))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_rankOne_projection_normalized d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp⟩ :=
    hall hcontained
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,?_⟩
  let S := stabilizer d.radical a
  let f' := (MulAut.conj (f u)).toMonoidHom.comp f
  let A := (Z d.radical z).subgroupOf S
  let t₁ := act d.radical v.val⁻¹ t
  let c₁ := act d.radical v.val⁻¹ c
  let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
    (Q d.radical t₁) (Nat.card F^2)).subgroupOf S
  let D := ((A ⊔ E).map f').subgroupOf pointLocal
  have hnB : 1<B.degree := by rw [hB]; exact h.nonbinary
  have hDsupp : D ⊔ pointRadical = ⊤ := by
    rw [←pointQuotient_ker,←comap_map_eq]
    change ((((A ⊔ E).map f').subgroupOf pointLocal).map pointQuotient).comap pointQuotient = ⊤
    rw [hgen,comap_top]
  rcases PointSupplement.supplement_dichotomy B.card_eq hnB D hDsupp with hD | hc
  · exact Or.inl hD
  right
  have hAU : A.map f' ≤ unipotent := hAP.trans (map_subtype_le _)
  have hAL : A.map f' ≤ pointLocal := hAU.trans inf_le_left
  let A₀ := (A.map f').subgroupOf pointLocal
  have hA₀ : A₀.map pointLocal.subtype = A.map f' := map_subgroupOf_eq_of_le hAL
  have hcardA : Nat.card A₀ = Nat.card (A.map f') := by
    rw [←card_map_of_injective pointLocal.subtype_injective,hA₀]
  have hlarge₀ : Nat.card B.Carrier^2 ≤ Nat.card A₀ := by
    rw [hcardA,←relIndex_ker,hker]
    have hh := relIndex_map_map_of_injective f.ker A S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le
      (path.endpoint_Z_le_start_stabilizer (by omega : 0<geometry.b d.radical))] at hh
    rw [←hh,B.card_eq,hB,←h.field_card]
    exact hlarge
  obtain ⟨hsize,hAR,hDR,hupper⟩ := PointSupplement.central_kernel_large_endpoint
    B.card_eq hnB D A₀ hc (comap_mono (map_mono le_sup_left)) hproj hlarge₀
  have hsize' : Nat.card (A.map f') = Nat.card B.Carrier^2 := by
    rwa [hcardA] at hsize
  refine ⟨hDR,hsize',hAR,hupper,?_⟩
  intro s w hs hws T₀
  exact PointSupplement.marked_sylow_at_bound B.card_eq hnB
    ((A ⊔ E).map f') (A.map f') (map_mono le_sup_left) hAL
    (hAU.trans (unipotent_le_borel.trans inf_le_right)) hsize' hDsupp hc s w hs hws T₀

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_point_dichotomy
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
                ∀ s w : Sp B.Carrier, s∈planeLocal → w*s∈pointLocal →
                  ∀ T₀ : Sylow 2 ((A ⊔ E).map f' ⊓
                    planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                      Subgroup (Sp B.Carrier)),
                    Nat.card T₀ = Nat.card B.Carrier^2 ∧
                      (((T₀ : Subgroup ((A ⊔ E).map f' ⊓
                        planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic :
                          Subgroup (Sp B.Carrier))).map
                        ((A ⊔ E).map f' ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓
                          pointParabolic).subtype).subgroupOf pointLocal) ⊓ pointRadical =
                            center (pointLocal (F := B.Carrier)))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_point_dichotomy_normalized d path hb hat hct hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
