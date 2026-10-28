module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedIndividualGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.PairedChoice

/-!
# Whole-edge fixedness for the same individual or paired generators

In the literal branch J ≤ Q₁, the original edge Z centralizes the full
plane-core preimage. The selected mover generates the vertex stabilizer
with this preimage in both alternatives: individual residual generation
uses Q ≤ Q₁, while paired generation uses the very same shear in Q₁.
Conjugation by that shear preserves Q₁ and gives the second generation.
Thus both movers fix exactly the ambient-fixed subgroup of the entire
original edge Z. All central attachments are retained.

This joins the actual generation alternative to both clauses of MS93
(5.5)(b,c), pp.915--917, without choosing independent residual elements.
Generation by the selected edge and endpoint is retained on the same
witnesses. Its shear conjugate also generates: the endpoint image is fixed
in the quotient, and the entire kernel remains in that conjugated edge.
ContainedPairedPaths uses both identities to construct the two backward
paths. The terminal distance exclusion remains a further obligation.
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

private theorem edge_fixed_of_plane_generation
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f)
    (E : Subgroup (stabilizer d.radical a))
    (hgen : ((CentralRootGeometry.wing true).map unipotent.subtype).comap f ⊔ E = ⊤) :
    Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
      Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb ha hat
    B hB f hf hfQ hindex hJplane
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Ne.symm hh
  have htZ := adjacent_Z_le d.radical ha hat
  have htJ : Z d.radical t ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    intro z hz y hy
    rw [Z,if_neg ht] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 y ((Subgroup.SmallMover.join_le _ _ _ _) hy)
  have htD : Z d.radical t ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    fun z hz => (he ▸ (show z ∈ Z d.radical a ⊓ centralizer
      (J : Set (FreeAmalgam d.radical)) from ⟨htZ hz,htJ hz⟩)).2
  have hwhole := congrArg (Subgroup.map S.subtype) hgen
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hwhole
  apply le_antisymm
  · intro z hz
    refine ⟨hz.1,?_⟩
    have hD : D ≤ centralizer ({z} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (htD hz.1 y hy)
    have hE : E.map S.subtype ≤ centralizer ({z} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hz.2 y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le hD hE) (hwhole.symm ▸ hy))
  · exact inf_le_inf_left _ (centralizer_le (map_subtype_le E))

/-- Individual or exceptional paired generation and both full-edge fixed
clauses hold for the same selected neighbor and residual shear, in the literal
original smaller-mover plane-containment branch. -/
theorem Input.replacement_contained_neighbor_generation_edge_fixed_original_fixed_normalized
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
              A ⊔ (Q d.radical t₁).subgroupOf (stabilizer d.radical a) = ⊤ ∧
              A ⊔ ((Q d.radical t₁).subgroupOf (stabilizer d.radical a)).map
                (MulAut.conj x).toMonoidHom = ⊤ ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2)).map (MulAut.conj x.val).toMonoidHom : Set (FreeAmalgam d.radical)) =
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
    h.replacement_contained_neighbor_generation_alternative_with_edge_original_fixed_normalized d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained hJplane
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hedge,hD⟩ := hall hcontained
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,?_⟩
  let S := stabilizer d.radical a
  let A := (Z d.radical z).subgroupOf S
  let f' := (MulAut.conj (f u)).toMonoidHom.comp f
  let t₁ := act d.radical v.val⁻¹ t
  let c₁ := act d.radical v.val⁻¹ c
  let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
    (Q d.radical t₁) (Nat.card F^2)).subgroupOf S
  let D := ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f
  have hAD : A ≤ D := map_le_iff_le_comap.mp hcontained
  let T := (Q d.radical t₁).subgroupOf S
  have hTS : Q d.radical t ≤ S := fun _ hy => hy.2 a (adjacent_symm d.radical hat)
  have hTS₁ : Q d.radical t₁ ≤ S := fun _ hy => hy.2 a (adjacent_symm d.radical hat₁)
  have hTconj : T = ((Q d.radical t).subgroupOf S).map (MulAut.conj v).toMonoidHom := by
    apply map_injective S.subtype_injective
    rw [Subgroup.image_conjugate,map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hTS₁]
    simp only [t₁,Q_act,inv_inv,Subgroup.coe_subtype]
  have hfirst : A ⊔ T = ⊤ := by rw [hTconj]; exact (hedge hJplane).1
  let J₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t₁) (Nat.card F^2)
  have hJ₁ : J₁ = (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map (MulAut.conj v.val).toMonoidHom := by
    have hU : (U d.radical a).map (MulAut.conj v.val).toMonoidHom = U d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized a v.property)
    have hQ : (Q d.radical a).map (MulAut.conj v.val).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a v.property)
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj v.val).injective,hU,hQ]
    simp only [J₁,t₁,Q_act,inv_inv]
  have hOriginal : Z d.radical t ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical)) =
      Z d.radical t ⊓ centralizer (S : Set (FreeAmalgam d.radical)) := by
    rw [hJ₁]
    exact (hedge hJplane).2
  have original_shear (x : S) (hx : f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2) :=
    h.replacement_plane_shear_edge_fixed d geometry hb path.start_color hat B hB f hf hfQ hindex hJplane
      J₁ hOriginal x hx
  have hkT : f.ker ≤ T := by
    obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat₁
    have hQT : Q d.radical a ≤ Q d.radical t₁ := by
      rw [←hjQ,←hjR]
      exact map_mono (h.replacement_core_le d)
    intro y hy
    exact hQT (hfQ ▸ mem_map_of_mem S.subtype hy)
  have hkD : f.ker ≤ D := ker_le_comap _ _
  have hLQ : pResidual 2 S ⊔ f.ker = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,hfQ,←MonoidHom.range_eq_map,range_subtype]
    change Ltilde d.radical a ⊔ Q d.radical a = S
    obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have fixed_of_gen (C : Subgroup S) (hgen : D ⊔ C=⊤) :=
    edge_fixed_of_plane_generation h d geometry hb path.start_color hat B hB f hf hfQ hindex hJplane C hgen
  have hcore : (planeParabolic (F := B.Carrier)).pCoreIn 2 =
      (CentralRootGeometry.wing true).map unipotent.subtype := by
    rw [pCoreIn,planeParabolic_core_map_eq_radical B.card_eq (by rw [hB]; exact h.nonbinary)]
    exact SymplecticConjugatePair.planeRadical_eq_wing
  have second (x : S) (hx : f x ∈ (planeParabolic (F := B.Carrier)).pCoreIn 2) :
      A ⊔ T.map (MulAut.conj x).toMonoidHom = ⊤ := by
    have hAx : (A.map f).map (MulAut.conj (f x)).toMonoidHom = A.map f := by
      let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
      let := CentralRootGeometry.wing_elementary (F := B.Carrier) true
      let : IsElementaryAbelian 2 P := IsElementaryAbelian.map unipotent.subtype
      have hxP : f x ∈ P := by
        change f x ∈ (CentralRootGeometry.wing true).map unipotent.subtype
        rwa [←hcore]
      apply mem_normalizer_iff_map_conj_eq.mp
      exact centralizer_le_normalizer (A.map f : Set (Sp B.Carrier))
        ((centralizer_le hcontained) (P.le_centralizer hxP))
    have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hfirst
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj x).surjective] at hh
    have hi := congrArg (Subgroup.map f) hh
    rw [Subgroup.map_sup,Subgroup.image_conjugate,hAx,map_top_of_surjective _ hf] at hi
    have hkTx : f.ker ≤ T.map (MulAut.conj x).toMonoidHom := by
      intro y hy
      refine ⟨x⁻¹*y*x,hkT ?_,?_⟩
      · change f (x⁻¹*y*x)=1
        simp [show f y=1 from hy]
      · simp [MulAut.conj_apply,mul_assoc]
    have he := congrArg (Subgroup.comap f) hi
    rw [←Subgroup.map_sup,comap_map_eq_self (hkTx.trans le_sup_right),comap_top] at he
    exact he
  rcases hD with hi | ⟨hQorig,hQsel,hcaporig,hcapsel,hnonsplit,x,hx,hfx,hxc,hxc₀,hgen⟩
  · have hgen : D ⊔ E=⊤ := top_unique (by
      rw [←hLQ]
      exact sup_le (hi.trans (sup_le_sup_right hAD E)) (hkD.trans le_sup_left))
    have hc : (MulAut.conj (1:S)).toMonoidHom = MonoidHom.id S := by
      ext y
      simp
    have hEone : E.map (MulAut.conj (1:S)).toMonoidHom = E := by
      rw [hc,Subgroup.map_id]
    refine ⟨1,(Ltilde d.radical a).one_mem,?_,?_,hfirst,
      second 1 (by rw [map_one]; exact Subgroup.one_mem _),fixed_of_gen E hgen,?_,hOriginal,
      original_shear 1 (by rw [map_one]; exact Subgroup.one_mem _),Or.inl ⟨hi,?_⟩⟩
    · rw [map_one]; exact Subgroup.one_mem _
    · rw [map_one]; exact Subgroup.one_mem _
    · change Z d.radical t ⊓ centralizer ((E.map (MulAut.conj (1:S)).toMonoidHom).map
        S.subtype : Set (FreeAmalgam d.radical)) = _
      rw [hEone]
      exact fixed_of_gen E hgen
    · change pResidual 2 S ≤ A ⊔ E.map (MulAut.conj (1:S)).toMonoidHom
      rw [hEone]
      exact hi
  · have hxD : x∈D := by
      change f x∈(CentralRootGeometry.wing true).map unipotent.subtype
      rwa [←hcore]
    have hgenD : D ⊔ E=⊤ := by
      apply top_unique
      rw [←hgen]
      refine sup_le (sup_le_sup_right hAD E) ?_
      rintro y ⟨e,he,rfl⟩
      exact (D ⊔ E).mul_mem ((D ⊔ E).mul_mem ((show D ≤ D ⊔ E from le_sup_left) hxD) ((show E ≤ D ⊔ E from le_sup_right) he))
        ((D ⊔ E).inv_mem ((show D ≤ D ⊔ E from le_sup_left) hxD))
    have hgenDx : D ⊔ E.map (MulAut.conj x).toMonoidHom=⊤ := by
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgenD
      have hDmap : D.map (MulAut.conj x).toMonoidHom=D :=
        mem_normalizer_iff_map_conj_eq.mp (D.le_normalizer hxD)
      rw [Subgroup.map_sup,hDmap,←MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (MulAut.conj x).surjective] at hh
      exact hh
    exact ⟨x,hx,hxc,hxc₀,hfirst,second x hxc₀,fixed_of_gen E hgenD,fixed_of_gen _ hgenDx,hOriginal,original_shear x hxc₀,
      Or.inr ⟨hQorig,hQsel,hcaporig,hcapsel,hnonsplit,hgen⟩⟩

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_neighbor_generation_edge_fixed_original_fixed
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
              A ⊔ (Q d.radical t₁).subgroupOf (stabilizer d.radical a) = ⊤ ∧
              A ⊔ ((Q d.radical t₁).subgroupOf (stabilizer d.radical a)).map
                (MulAut.conj x).toMonoidHom = ⊤ ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2)).map (MulAut.conj x.val).toMonoidHom : Set (FreeAmalgam d.radical)) =
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
    h.replacement_contained_neighbor_generation_edge_fixed_original_fixed_normalized d path hb hat hct hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

/-- The original generation/fixed interface with its public statement preserved. -/
theorem Input.replacement_contained_neighbor_generation_edge_fixed
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
              A ⊔ (Q d.radical t₁).subgroupOf (stabilizer d.radical a) = ⊤ ∧
              A ⊔ ((Q d.radical t₁).subgroupOf (stabilizer d.radical a)).map
                (MulAut.conj x).toMonoidHom = ⊤ ∧
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
    h.replacement_contained_neighbor_generation_edge_fixed_original_fixed d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,?_⟩
  intro hcontained hJplane
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hedge₁,hedge₂,hfix₁,hfix₂,_,_,hD⟩ :=
    hall hcontained hJplane
  exact ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hedge₁,hedge₂,hfix₁,hfix₂,hD⟩

/-- Both fixed clauses with the original individual/paired public interface.
The stronger theorem retains generation by both selected edges as well. -/
theorem Input.replacement_contained_neighbor_generation_fixed
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
    h.replacement_contained_neighbor_generation_edge_fixed d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,?_⟩
  intro hcontained hJplane
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hedge₁,hedge₂,hfix₁,hfix₂,hD⟩ :=
    hall hcontained hJplane
  exact ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hfix₁,hfix₂,hD⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

/-!
# The actual backward path in the individual contained-image branch

Individual residual generation forces the endpoint to move the selected
neighbor seed: otherwise the residual and original Q normalize that seed,
contradicting its transported ambient nonnormality. Trapping that same seed
would force a field-sized endpoint image, contrary to the retained square
lower bound. The resulting backward path keeps every overlap and the original
B-relative U-index, together with the same two fixed-layer clauses.

Source: MS93 (5.5), (5.7)--(5.8), pp.915--920. The exceptional paired branch
retains its generation, full-Q and nonsplitting conclusions. Its two paths
are now supplied by ContainedPairedPaths; terminal exclusions and the final
minimum-replacement witness remain further obligations.
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

private theorem backward_of_individual
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (g : stabilizer d.radical a)
    (hres : pResidual 2 (stabilizer d.radical a) ≤
      (Z d.radical z).subgroupOf (stabilizer d.radical a) ⊔
        (Subgroup.SmallMover.join (U d.radical (act d.radical g.val⁻¹ c))
          (Q d.radical (act d.radical g.val⁻¹ c)) (Q d.radical (act d.radical g.val⁻¹ t))
          (Nat.card F^2)).subgroupOf (stabilizer d.radical a)) :
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
  have hES : Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
      (Q d.radical t₁) (Nat.card F^2) ≤ S :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 a (adjacent_symm d.radical hat₁))
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hres' := map_mono (f := S.subtype) hres
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hzS,map_subgroupOf_eq_of_le hES] at hres'
  change Ltilde d.radical a ≤ Z d.radical z ⊔ _ at hres'
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat₁
  have hQT : Q d.radical a ≤ Q d.radical t₁ := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hS : Ltilde d.radical a ⊔ Q d.radical a = S := by
    obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := SourceComparison.vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hwholeEdge : Q d.radical t₁ ⊔ Z d.radical z = S := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 a (adjacent_symm d.radical hat₁)) hzS
    · rw [←hS]
      exact sup_le (hres'.trans (sup_le le_sup_right
        ((Subgroup.SmallMover.join_le _ _ _ _).trans le_sup_left))) (hQT.trans le_sup_left)
  have hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hbad
    have hTN := edge_normalizes_neighbor_seed_join hat₁ hct₁
    have hwhole : S ≤ normalizer
        ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      rw [←hS]
      exact sup_le (hres'.trans (sup_le hbad
        ((Subgroup.SmallMover.join_le _ _ _ _).trans hTN))) (hQT.trans hTN)
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

/-- The individual branch of the same contained selector has an actual
backward critical path, retaining every overlap and the whole-edge fixed clauses.
The exceptional paired alternative remains explicitly available on those witnesses. -/
theorem Input.replacement_contained_neighbor_generation_paths
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
            (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c₁) =
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
            ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
              f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E ∧
                pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E.map (MulAut.conj x).toMonoidHom ∧
                Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
                ¬ Z d.radical z ≤ normalizer
                  ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
                (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
                  back.walk.getVert 1 = t₁ ∧
                  ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i)) ∨
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
    h.replacement_contained_neighbor_generation_fixed d path hb hat hct hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,?_⟩
  intro hcontained hJplane
  obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hfix₁,hfix₂,hD⟩ :=
    hall hcontained hJplane
  have hi := movingIndex_act geometry (d := c) (by omega) path.start_color v.val⁻¹
    ((stabilizer d.radical a).inv_mem v.property)
  refine ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,hi,x,hx,hxc,hxc₀,hfix₁,hfix₂,?_⟩
  rcases hD with ⟨hgen₁,hgen₂⟩ | hpair
  · obtain ⟨hwhole,hn,hback⟩ := backward_of_individual h d path hb hat hct hnormal hlarge v hgen₁
    exact Or.inl ⟨hgen₁,hgen₂,hwhole,hn,hback⟩
  · exact Or.inr hpair

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
