module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedNormalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootPairKernel

/-!
# The full-Q alternative at the actual contained-endpoint selector

In the central-intersection branch, the marked Sylow root pair and its
index-two mover action now force the entire original Q into the unequal
mover. Its intersection with the original mover has image order at most
q squared. Transport through the same residual conjugator proves both
clauses at the selected neighbor, and the original full-X fixed-index
comparison supplies the genuine nonsplitting conclusion.

Every previous endpoint, parabolic, quotient-kernel, root-pair and whole
edge-Z fixed-subgroup clause stays on the same witnesses. Source: MS93
(5.5)(c), printed pp.915--917. The local generation by T₀, its conjugate
and Y, the individual/paired generation alternative and compatible paths
still need proof. No distance-two replacement witness is asserted here.
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

/-- The same contained-endpoint selector has a genuine marked root pair
and full-Q, intersection and whole-X nonsplitting conclusions
in the central-intersection branch. -/
theorem Input.replacement_contained_neighbor_kernel_alternative_normalized
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
                    ∀ e u₀ z₀ v₀ : B.Carrier,
                      (CentralRootGeometry.element e u₀ z₀ v₀).val ∈
                        ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                          (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f →
                        e=0 ∨ e=b)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_root_pair_normalized d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,hD⟩ :=
    hall hcontained
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hproj,hSylow,hcross,hgen,hsupp,?_⟩
  rcases hD with hD | ⟨hDR,hsize,hAR,hupper,hT₀,hroots⟩
  · exact Or.inl hD
  right
  obtain ⟨s,w,hs,hsp,hw,hws,hcore,hcross'⟩ := hcross
  obtain ⟨r,b,hb',hpair,hidx,hTeq,hcoords⟩ := hroots s w hs hsp hw hws hcore
  let S := stabilizer d.radical a
  let A := (Z d.radical z).subgroupOf S
  let f' := (MulAut.conj (f u)).toMonoidHom.comp f
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E₀ := (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)).subgroupOf S
  let t₁ := act d.radical v.val⁻¹ t
  let c₁ := act d.radical v.val⁻¹ c
  let J₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t₁) (Nat.card F^2)
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
  have back (D : Subgroup (Sp B.Carrier)) :
      (D.map (MulAut.conj w).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom = D := by
    rw [Subgroup.map_map]
    have hh : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [hh,Subgroup.map_id]
  let C := (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2
  let W₀ := (A ⊔ E).map f' ⊓ C
  have hi : (rootImage (some r) ⊔ rootImage (some (r+b))).relIndex (E₀.map f) = 2 := by
    have hh := relIndex_map_map_of_injective W₀ (E.map f')
      (f := (MulAut.conj w⁻¹).toMonoidHom) (MulAut.conj w⁻¹).injective
    rw [hpair,hEimage,back] at hh
    have hi₀ : W₀.relIndex (E.map f') = 2 := hidx
    rw [hEimage] at hi₀
    exact hh.trans hi₀
  have hQorig := h.replacement_root_pair_index_two_kernel d geometry hb path.start_color
    hat hct B hB f hf hfQ hindex (some r) (some (r+b)) (by simpa using hb') hi
  have hC : C = ((CentralRootGeometry.wing true).map unipotent.subtype).map (MulAut.conj w).toMonoidHom := by
    dsimp only [C]
    rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj w).injective,pCoreIn,
      planeParabolic_core_map_eq_radical B.card_eq (by rw [hB]; exact h.nonbinary)]
    exact congrArg (Subgroup.map (MulAut.conj w).toMonoidHom)
      SymplecticConjugatePair.planeRadical_eq_wing
  have hEW : E₀.map f ⊓ (CentralRootGeometry.wing true).map unipotent.subtype ≤
      rootImage (some r) ⊔ rootImage (some (r+b)) := by
    have hh := map_mono (show E.map f' ⊓ C ≤ W₀ from
      inf_le_inf_right _ (map_mono le_sup_right)) (f := (MulAut.conj w⁻¹).toMonoidHom)
    rw [map_inf _ _ _ (MulAut.conj w⁻¹).injective,hEimage,hC,back,back,hpair] at hh
    exact hh
  have hWcard : Nat.card (rootImage (some r) ⊔ rootImage (some (r+b)) : Subgroup (Sp B.Carrier)) = Nat.card F^2 := by
    change Nat.card ((rootFamily (some r)).map unipotent.subtype ⊔
      (rootFamily (some (r+b))).map unipotent.subtype : Subgroup (Sp B.Carrier)) = _
    rw [←Subgroup.map_sup,card_map_of_injective unipotent.subtype_injective,
      rootFamily_sup_card (by simpa using hb'),B.card_eq,hB,h.field_card]
  have hcaporig := h.replacement_unequal_plane_intersection_bound d geometry hb path.start_color
    hat hct hne B hB f hfQ hTf hindex _ hWcard.le hEW
  have hvS := Ltilde_le_stabilizer a hv
  have hQa : (Q d.radical a).map (MulAut.conj v.val).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hvS)
  have hUa : (U d.radical a).map (MulAut.conj v.val).toMonoidHom = U d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (U_normalized a hvS)
  have hJconj : J.map (MulAut.conj v.val).toMonoidHom = J₁ := by
    dsimp only [J,J₁]
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj v.val).injective,hQa,hUa]
    simp only [t₁,Q_act,inv_inv]
  have hEconj' : (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)).map (MulAut.conj v.val).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
          (Q d.radical t₁) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj v.val).injective]
    simp only [c₁,t₁,U_act,Q_act,inv_inv]
  have hQselected : Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c₁)
      (Q d.radical c₁) (Q d.radical t₁) (Nat.card F^2) := by
    have hh := map_mono hQorig (f := (MulAut.conj v.val).toMonoidHom)
    rwa [hQa,hEconj'] at hh
  have hcapselected : (Q d.radical a).relIndex
      (J₁ ⊓ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)) ≤ Nat.card F^2 := by
    have hh := relIndex_map_map_of_injective (Q d.radical a)
      (J ⊓ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2))
      (f := (MulAut.conj v.val).toMonoidHom) (MulAut.conj v.val).injective
    rw [hQa,map_inf _ _ _ (MulAut.conj v.val).injective,hJconj,hEconj'] at hh
    exact hh.le.trans hcaporig
  have hnonsplit := h.replacement_unequal_kernel_nonsplitting d geometry hb path.start_color
    hat hct hne hQorig
  exact ⟨hQorig,hQselected,hcaporig,hcapselected,hnonsplit,hDR,hsize,hAR,hupper,hT₀,hroots⟩

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_kernel_alternative
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
                    ∀ e u₀ z₀ v₀ : B.Carrier,
                      (CentralRootGeometry.element e u₀ z₀ v₀).val ∈
                        ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
                          (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f →
                        e=0 ∨ e=b)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_kernel_alternative_normalized d path hb hat hct hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
