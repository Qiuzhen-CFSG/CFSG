module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedKernelAlternative
public import Theory.SpecificGroups.SymplecticFour.PointPairGeneration

/-!
# Paired generation for the same contained-endpoint unequal mover

In the central-intersection branch, the actual marked T₀ and endpoint
have full rank-one image. A shear in the original plane radical makes
T₀, its conjugate, and that endpoint generate the whole point local.
The unequal mover moves this point, giving the entire symplectic quotient.

Lift this one shear to the original vertex residual. Full-Q containment
makes both generation identities lift through the entire quotient kernel.
The same original neighbor, residual elements, root pair, intersection bounds,
nonsplitting and whole-edge fixed-subgroup comparison are retained.
Source: MS93 (5.5)(c), printed pp.915--917. The full individual/paired
selector and its path compatibility, terminal exclusions and minimum
characteristic distance-two witness remain further source obligations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The central branch of the actual contained-endpoint selector has paired
generation with one original residual lift of a plane-radical shear. -/
theorem Input.replacement_contained_neighbor_paired_generation_normalized
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
                D ⊓ pointRadical = center (pointLocal (F := B.Carrier)) ∧
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
                    (∀ e u₀ z₀ v₀ : B.Carrier,
                      (CentralRootGeometry.element e u₀ z₀ v₀).val ∈
                        ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                          (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f →
                        e=0 ∨ e=b) ∧
                    ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
                      f' x = (pointRadicalElement (1:B.Carrier) 0 0).val ∧
                      f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                      f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                      let T := (A ⊔ E) ⊓
                        ((planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).comap f'
                      (A ⊔ T) ⊔ T.map (MulAut.conj x).toMonoidHom = L ∧
                        (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_kernel_alternative_normalized d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,hD⟩ :=
    hall hcontained
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,?_⟩
  rcases hD with hD | ⟨hQorig,hQsel,hcaporig,hcapsel,hnonsplit,hDR,hsize,hAR,hupper,hT₀,hroots⟩
  · exact Or.inl hD
  right
  refine ⟨hQorig,hQsel,hcaporig,hcapsel,hnonsplit,hDR,hsize,hAR,hupper,hT₀,?_⟩
  intro s w hs hsp hw hws hcore
  obtain ⟨r,b,hb',hpair,hidx,hTeq,hcoords⟩ := hroots s w hs hsp hw hws hcore
  refine ⟨r,b,hb',hpair,hidx,hTeq,hcoords,?_⟩
  let := finite_stabilizer d.radical a
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
  have hnB : 1<B.degree := by rw [hB]; exact h.nonbinary
  let C := (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2
  let W := (A ⊔ E).map f' ⊓ C
  let T := (A ⊔ E) ⊓ C.comap f'
  have hWL : W ≤ pointLocal := by
    apply inf_le_right.trans
    intro y hy
    obtain ⟨z,rfl⟩ := hf' y
    exact hcore hy
  have hWP : W ≤ (A.map f') ⊔ E.map f' := by
    rw [←Subgroup.map_sup]
    exact inf_le_left
  have hEP : E.map f' ≤ planeParabolic.map (MulAut.conj w).toMonoidHom := by
    rw [hEimage]
    apply map_mono
    exact ((map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf).trans
      (unipotent_le_borel.trans inf_le_right)
  have hEW : E.map f' ≤ normalizer (W : Set (Sp B.Carrier)) := by
    refine (le_inf ((map_mono le_sup_right).trans ((A ⊔ E).map f').le_normalizer) ?_).trans
      inf_normalizer_le_normalizer_inf
    exact (hEP.trans (planeParabolic.map (MulAut.conj w).toMonoidHom).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hE2 : IsPGroup 2 (E.map f') := by
    rw [hEimage]
    have hEU : E₀.map f ≤ unipotent :=
      (map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf
    exact ((unipotentSylow B.card_eq (by omega)).isPGroup'.to_le hEU).map _
  have hWsize : Nat.card W = Nat.card B.Carrier^2 := by
    rw [←card_map_of_injective (f := (MulAut.conj w⁻¹).toMonoidHom) (MulAut.conj w⁻¹).injective,hpair]
    change Nat.card ((rootFamily (some r)).map unipotent.subtype ⊔
      (rootFamily (some (r+b))).map unipotent.subtype : Subgroup (Sp B.Carrier)) = _
    rw [←Subgroup.map_sup,card_map_of_injective unipotent.subtype_injective]
    exact rootFamily_sup_card (by simpa using hb')
  have hmodel := PointPairGeneration.marked_pair_generate B.card_eq hnB
    (A.map f') (E.map f') W hAP hWL hWP hEW hE2
    ((isPGroup_pCoreIn 2 _).to_le inf_le_right) hWsize hsize hproj
    (by rw [←Subgroup.map_sup]; exact hgen)
    (by rw [←Subgroup.map_sup]; exact hupper)
    (by rw [←Subgroup.map_sup]; exact hDR.le) hidx
  let L₀ := (Ltilde d.radical a).subgroupOf S
  have hL : L₀.map f'=⊤ := by
    have he : L₀=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f' hf']
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two (by
      rw [B.card_eq,hB]
      exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary))
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨x,hx,hfx⟩ := (show (pointRadicalElement (1:B.Carrier) 0 0).val∈L₀.map f' by
    rw [hL]; trivial)
  have hxcore : f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 := by
    rw [hfx,pCoreIn,planeParabolic_core_map_eq_radical B.card_eq hnB]
    change (pointRadicalElement (1:B.Carrier) 0 0).val∈SymplecticConjugatePair.planeRadical
    rw [SymplecticConjugatePair.planeRadical_eq_wing]
    exact PointPairGeneration.shear_mem_plane
  have hxcore₀ : f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 := by
    have huN := (normalizer_le_normalizer_characteristic_image
      (planeParabolic (F := B.Carrier)) (pCore 2 _))
      (planeParabolic.le_normalizer (planeLocal_le hup))
    exact (mem_normalizer_iff.mp huN (f x)).mpr hxcore
  refine ⟨x,hx,hfx,hxcore,hxcore₀,?_⟩
  have hkE : f'.ker ≤ E := by
    rw [hker]
    intro y hy
    exact hQsel (hfQ ▸ mem_map_of_mem S.subtype hy)
  have hTm : T.map f'=W := by
    ext y
    constructor
    · rintro ⟨z,⟨hz,hzc⟩,rfl⟩
      exact ⟨mem_map_of_mem f' hz,hzc⟩
    · rintro ⟨⟨z,hz,rfl⟩,hc⟩
      exact ⟨z,⟨hz,hc⟩,rfl⟩
  have hkT : f'.ker ≤ T := le_inf (hkE.trans le_sup_right) (ker_le_comap _ _)
  constructor
  · have hm : ((A ⊔ T) ⊔ T.map (MulAut.conj x).toMonoidHom).map f'=pointLocal := by
      rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,hTm,hfx]
      exact hmodel.1
    exact (comap_map_eq_self (hkT.trans (le_sup_right.trans le_sup_left))).symm.trans
      (congrArg (Subgroup.comap f') hm)
  · have hm : ((A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom).map f'=⊤ := by
      rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,hfx]
      exact hmodel.2
    have hh := (comap_map_eq_self (hkE.trans (le_sup_right.trans le_sup_left))).symm.trans
      (congrArg (Subgroup.comap f') hm)
    exact hh.trans (comap_top f')

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_paired_generation
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
                D ⊓ pointRadical = center (pointLocal (F := B.Carrier)) ∧
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
                    (∀ e u₀ z₀ v₀ : B.Carrier,
                      (CentralRootGeometry.element e u₀ z₀ v₀).val ∈
                        ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                          (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f →
                        e=0 ∨ e=b) ∧
                    ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
                      f' x = (pointRadicalElement (1:B.Carrier) 0 0).val ∧
                      f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                      f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
                      let T := (A ⊔ E) ⊓
                        ((planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).comap f'
                      (A ⊔ T) ⊔ T.map (MulAut.conj x).toMonoidHom = L ∧
                        (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_paired_generation_normalized d path hb hat hct hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
