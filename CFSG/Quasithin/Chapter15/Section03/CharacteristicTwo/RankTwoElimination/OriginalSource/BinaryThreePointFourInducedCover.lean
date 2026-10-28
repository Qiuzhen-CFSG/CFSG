module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalSeed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourLinearSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourEndpointEquality
public import Theory.Representation.BinaryEndpointInduction.EndpointParabolicIdentification

/-!
# An induced cover of the original binary-four central span

The original natural eight, with its actual quotient marking, is carried to
one of the two literal endpoint coefficient systems. Its translates give a
surjection from the forty-five coset coordinates onto the unchanged original
central span. The point quotient action, its kernel, the original component,
and the exact inverse-actor intertwining equations are all retained.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryEndpointInduction

private theorem natural_section_coordinates
    {G : Type*} [Group G] (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (a : L →* SL(3,ZMod 2))
    (h : HasSectionModel L V ⊥ a (Representation.specialLinearNatural (k := ZMod 2) 3)) :
    L ≤ normalizer V ∧ ∃ η : Additive V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
      ∀ (l : L) (v w : V), (w : G)=l*(v:G)*(l:G)⁻¹ →
        η (Additive.ofMul w)=(a l).val *ᵥ η (Additive.ofMul v) := by
  obtain ⟨_,hLV,_,hn,e,he⟩ := h
  let := hn
  have hker : (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf V)).ker=⊥ := by
    rw [QuotientGroup.ker_mk',bot_subgroupOf]
  let E : V ≃* Multiplicative (Fin 3 → ZMod 2) :=
    (MulEquiv.ofBijective (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf V))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp hker,QuotientGroup.mk'_surjective _⟩).trans e
  let η := LinearEquiv.ofBijective (E.toMonoidHom.toAdditiveLeft.toZModLinearMap 2)
    E.bijective
  exact ⟨hLV,η,he⟩

private theorem cover_of_original_seed
    {G X : Type*} [Group G] [Group X] [Finite X]
    (C L V W : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hLC : L ≤ C) (hVW : V ≤ W)
    (q : C →* X) (B K : Subgroup X) (hBK : B ≤ K)
    (σ : Representation (ZMod 2) X (Additive W))
    (hσ : ∀ (x : C) (w : Additive W),
      ((σ (q x) w).toMul : G)=x*(w.toMul:G)*(x:G)⁻¹)
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun kv : K × Additive V =>
        σ kv.1.val ((inclusion hVW).toAdditive.toZModLinearMap 2 kv.2)))=⊤)
    (f : L →* B) (hf : Function.Surjective f)
    (hfq : ∀ l : L, (f l : X)=q ⟨l,hLC l.property⟩)
    (β : B →* SL(3,ZMod 2)) (hβ : Function.Surjective β) (hβk : β.ker=pCore 2 B)
    (hmodel : HasSectionModel L V ⊥ (β.comp f)
      (Representation.specialLinearNatural (k := ZMod 2) 3))
    (eK : K ≃* SL(4,ZMod 2))
    (heK : (B.subgroupOf K).map eK.toMonoidHom=endpointParabolic) :
    ∃ (dual : Bool) (F : (Fin 45 → ZMod 2) →ₗ[ZMod 2] Additive W),
      Function.Surjective F ∧ ∀ (a : Fin 6) (x : Fin 45 → ZMod 2),
        F (x ᵥ* inducedCosetMatrix dual a)=
          σ (eK.symm ((cosetActor a)⁻¹)).val (F x) := by
  let i := (inclusion hVW).toAdditive.toZModLinearMap 2
  obtain ⟨hLV,η,hη⟩ := natural_section_coordinates L V (β.comp f) hmodel
  let j := i.comp η.symm.toLinearMap
  let τ : Representation (ZMod 2) SL(4,ZMod 2) (Additive W) :=
    (σ.comp K.subtype).comp eK.symm.toMonoidHom
  let eB : B ≃* endpointParabolic :=
    (subgroupOfEquivOfLe hBK).symm.trans
      ((eK.subgroupMap (B.subgroupOf K)).trans (MulEquiv.subgroupCongr heK))
  let βP := β.comp eB.symm.toMonoidHom
  have hβP : Function.Surjective βP := hβ.comp eB.symm.surjective
  have hβPk : βP.ker=pCore 2 endpointParabolic := by
    change β.ker.comap eB.symm.toMonoidHom= _
    rw [hβk]
    exact (comap_equiv_eq_map_symm eB.symm _).trans (pCore_map_iso 2 eB)
  have haction (p : endpointParabolic) (v : Fin 3 → ZMod 2) :
      τ p.val (j v)=j ((βP p).val *ᵥ v) := by
    obtain ⟨l,hl⟩ := hf (eB.symm p)
    have hp : eB (f l)=p := by rw [hl,eB.apply_symm_apply]
    subst p
    let u : V := (η.symm v).toMul
    let u' : V := V.normalizerMonoidHom ⟨l,hLV l.property⟩ u
    have hu' : η (Additive.ofMul u')=(β (f l)).val *ᵥ v := by
      have hh := hη l u u' rfl
      change η (Additive.ofMul u')=(β (f l)).val *ᵥ η (η.symm v) at hh
      rwa [η.apply_symm_apply] at hh
    have hη' : η.symm ((β (f l)).val *ᵥ v)=Additive.ofMul u' := by
      rw [←hu',η.symm_apply_apply]
    have hactor : eK.symm (eB (f l)).val=⟨(f l : X),hBK (f l).property⟩ := by
      apply eK.injective
      rw [eK.apply_symm_apply]
      rfl
    change σ (eK.symm (eB (f l)).val).val (j v)=
      j ((β (eB.symm (eB (f l)))).val *ᵥ v)
    rw [hactor,eB.symm_apply_apply]
    change σ (f l : X) (i (η.symm v))=i (η.symm ((β (f l)).val *ᵥ v))
    rw [hfq,hη']
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hσ ⟨l,hLC l.property⟩ (i (η.symm v))
  obtain ⟨dual,changeSeed,hrange,hlocal⟩ := exists_seed_marking τ βP hβP hβPk j haction
  let j' := j.comp changeSeed.toLinearMap
  have hs : Submodule.span (ZMod 2)
      (Set.range (fun gv : SL(4,ZMod 2) × (Fin 3 → ZMod 2) => τ gv.1 (j' gv.2)))=⊤ := by
    apply top_unique
    rw [←hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k,v⟩,rfl⟩
    have hj : i v ∈ j.range := ⟨η v,by simp [j]⟩
    rw [←hrange] at hj
    obtain ⟨u,hu⟩ := hj
    apply Submodule.subset_span
    refine ⟨(eK k,u),?_⟩
    change σ (eK.symm (eK k)).val (j' u)=σ k.val (i v)
    rw [eK.symm_apply_apply]
    exact congrArg (σ k.val) hu
  exact ⟨dual,cosetLift τ j',cosetLift_surjective dual τ j' hlocal hs,
    cosetLift_intertwine dual τ j' hlocal⟩

variable {G : Type*} [Group G] [Finite G]

/-- The full original binary-four point data produce a surjective literal
induced cover, with the original quotient action and exact endpoint marking. -/
theorem binary_three_source_four_induced_cover
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    ∃ (hV : IsElementaryAbelian 2 V) (hW : IsElementaryAbelian 2 W) (hVW : V ≤ W),
      let := hV
      let := hW
      ∃ σ : Representation (ZMod 2) (C ⧸ pCore 2 C) (Additive W),
        let τ := σ.comp K.subtype
        Function.Injective τ ∧
        (∀ (x : C) (w : Additive W),
          ((σ (q x) w).toMul : G)=x*(w.toMul:G)*(x:G)⁻¹) ∧
        σ.ker=centralizer (K : Set (C ⧸ pCore 2 C)) ∧
        Submodule.span (ZMod 2)
          (Set.range (fun kv : K × Additive V =>
            τ kv.1 ((inclusion hVW).toAdditive.toZModLinearMap 2 kv.2)))=⊤ ∧
        ∃ eK : K ≃* SL(4,ZMod 2),
          (B.subgroupOf K).map eK.toMonoidHom=endpointParabolic ∧
          ∃ (dual : Bool) (F : (Fin 45 → ZMod 2) →ₗ[ZMod 2] Additive W),
            Function.Surjective F ∧ ∀ (a : Fin 6) (x : Fin 45 → ZMod 2),
              F (x ᵥ* inducedCosetMatrix dual a)=τ (eK.symm ((cosetActor a)⁻¹)) (F x) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨hV,hW,hVW,σ,hinj,hσ,hker,hspan⟩ := binary_three_source_four_linear_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  let := hV
  let := hW
  obtain ⟨_,_,_,a,v,_,hflag⟩ :=
    binary_three_point_four_endpoint_equality d c.L b z hLS P hP K hBK hm
  obtain ⟨eK,heK⟩ := exists_endpointParabolic_marking (B.subgroupOf K) a v hflag
  obtain ⟨common⟩ := t.commonFacts hc
  obtain ⟨f,β,hf,hfq,hβ,hβk,hmodel⟩ := binary_three_point_natural_seed d c.L b t common hb z hLC
  exact ⟨hV,hW,hVW,σ,hinj,hσ,hker,hspan,eK,heK,
    cover_of_original_seed C c.L V W hLC hVW q B K hBK σ hσ hspan
      f hf hfq β hβ hβk hmodel eK heK⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
