module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.TorusSource.Component
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
/-!
# Orienting the selected cubic without changing the original setup

The prescribed exchanger interchanges the two original block factors. If the
selected cubic is the second quotient axis, conjugate its block and containing
torus by that exchanger. The torus stays in the original Borel, and the moved
cubic is the first axis of the same original product projection. This preserves
the original L, T and FundamentalSetup throughout the terminal construction.

Source: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Stellmacher Chapter3.Section02 ChapterC ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original Sylow group normalizes the source Borel. -/
theorem source_original_sylow_normalizes_borel :
    (T : Subgroup G) ≤ normalizer (sourceOrbitBorel T L : Set G) := by
  intro t ht
  have hTf : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
  have hRf : (localOrbit T L).map (MulAut.conj t).toMonoidHom = localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((pResidual 2 (sourceOrbitSylowNormalizer T L)).map
    (sourceOrbitSylowNormalizer T L).subtype).map (MulAut.conj t).toMonoidHom = _
  rw [map_embedded_pResidual]
  have hN : (sourceOrbitSylowNormalizer T L).map (MulAut.conj t).toMonoidHom =
      sourceOrbitSylowNormalizer T L := by
    change (localOrbit T L ⊓ normalizer (((T : Subgroup G) ⊓ localOrbit T L : Subgroup G) : Set G)).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective, map_equiv_normalizer_eq,
      map_inf _ _ _ (MulAut.conj t).injective, hTf, hRf]
    rfl
  rw [hN]
  rfl

/-- Data retained by an explicit orientation of the selected block and torus.
The exact first axis uses the original quotient map, not a new product marking. -/
structure SourceOriginalOrientedTorus
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (K C P : Subgroup G) (s : G) : Prop where
  mem_sylow : s ∈ (T : Subgroup G)
  choice : s=1 ∨ s=t
  natural : IsL2EvenBlock (K.map (MulAut.conj s).toMonoidHom) 2
  core : pCore 2 (K.map (MulAut.conj s).toMonoidHom) =
    blockU (K.map (MulAut.conj s).toMonoidHom)
  center : Subgroup.center (K.map (MulAut.conj s).toMonoidHom)=⊥
  sylow : Chapter1.IsSylowIn 2
    (baumann (T : Subgroup G) ⊓ K.map (MulAut.conj s).toMonoidHom)
    (K.map (MulAut.conj s).toMonoidHom)
  normalized : baumann (T : Subgroup G) ≤
    normalizer (K.map (MulAut.conj s).toMonoidHom : Set G)
  escapes : ¬ K.map (MulAut.conj s).toMonoidHom ≤ D.maximalLocal
  distinct : K.map (MulAut.conj s).toMonoidHom ≠ L
  borel : C.map (MulAut.conj s).toMonoidHom ≤ sourceOrbitBorel T L
  torus_card : Nat.card (C.map (MulAut.conj s).toMonoidHom)=9
  torus_normalizes : C.map (MulAut.conj s).toMonoidHom ≤
    normalizer (K.map (MulAut.conj s).toMonoidHom : Set G)
  cubic_card : Nat.card (P.map (MulAut.conj s).toMonoidHom)=3
  cubic_block : P.map (MulAut.conj s).toMonoidHom ≤ K.map (MulAut.conj s).toMonoidHom
  cubic_original : P.map (MulAut.conj s).toMonoidHom ≤ L
  first_axis :
    let C' := C.map (MulAut.conj s).toMonoidHom
    let hCR : C' ≤ localOrbit T L := borel.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    ((MonoidHom.snd _ _).comp q).ker.map C'.subtype = P.map (MulAut.conj s).toMonoidHom

/-- Both choices of the selected literal axis admit an original-oriented torus. -/
theorem source_original_orient_selected_axis
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (K C P : Subgroup G) (hK : IsL2EvenBlock K 2) (hcoreK : pCore 2 K=blockU K)
    (hzK : center K=⊥)
    (hKS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G) ⊓ K) K)
    (hSK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ D.maximalLocal)
    (hCB : C ≤ sourceOrbitBorel T L) (hc : Nat.card C=9)
    (hPK : P ≤ K) (hP : Nat.card P=3) (hCN : C ≤ normalizer (K : Set G)) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    (P=((MonoidHom.snd _ _).comp q).ker.map C.subtype ∨
     P=((MonoidHom.fst _ _).comp q).ker.map C.subtype) →
    ∃ s : G, SourceOriginalOrientedTorus D e hn ht htn K C P s := by
  dsimp only
  intro hor
  obtain ⟨hD₁L,hD₂J,_,_,_,_⟩ :=
    source_original_borel_torus_axes D e hn ht htn hb hz C hCB hc
  have hPC : P ≤ C := by
    rcases hor with rfl | rfl <;> exact map_subtype_le _
  have hselect : ∃ s : G, s ∈ (T : Subgroup G) ∧ (s=1 ∨ s=t) ∧
      P.map (MulAut.conj s).toMonoidHom ≤ L := by
    rcases hor with he | he
    · refine ⟨1, one_mem _, Or.inl rfl, ?_⟩
      have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [hid,map_id,he]
      exact hD₁L
    · refine ⟨t, ht, Or.inr rfl, ?_⟩
      have hh := map_mono (f := (MulAut.conj t).toMonoidHom) (he ▸ hD₂J)
      rwa [conjugate_twice_eq_of_index_two L (T : Subgroup G) (normalizer (L : Set G))
        (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) inf_le_right ht] at hh
  obtain ⟨s,hs,hchoice,hPL⟩ := hselect
  let f := MulAut.conj s
  let K' := K.map f.toMonoidHom
  let C' := C.map f.toMonoidHom
  let P' := P.map f.toMonoidHom
  let a : K ≃* K' := f.subgroupMap K
  have hSf : (baumann (T : Subgroup G)).map f.toMonoidHom = baumann (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer hs))
  have hBf : (sourceOrbitBorel T L).map f.toMonoidHom = sourceOrbitBorel T L :=
    mem_normalizer_iff_map_conj_eq.mp (source_original_sylow_normalizes_borel hs)
  have hCB' : C' ≤ sourceOrbitBorel T L := by
    exact (map_mono hCB).trans_eq hBf
  have hc' : Nat.card C'=9 := by rw [card_map_of_injective f.injective]; exact hc
  have hP' : Nat.card P'=3 := by rw [card_map_of_injective f.injective]; exact hP
  have hRf : (localOrbit T L).map f.toMonoidHom=localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T hs)
  have hMf : D.maximalLocal.map f.toMonoidHom=D.maximalLocal := by
    change (normalizer (localOrbit T L : Set G)).map f.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hRf]
  have hout' : ¬ K' ≤ D.maximalLocal := by
    intro hh
    apply hout
    apply (map_le_map_iff_of_injective (f:=f.toMonoidHom) f.injective).mp
    exact hh.trans_eq hMf.symm
  have hcore' : pCore 2 K'=blockU K' := by
    rw [←pCore_map_iso 2 a,hcoreK,blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective _ a.surjective,blockU]
  have hz' : center K'=⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr a.symm ⟨k,hk⟩).property
    change a.symm k ∈ center K at hh
    rw [hzK,mem_bot] at hh
    exact mem_bot.mpr (a.symm.injective (hh.trans a.symm.map_one.symm))
  have hKS' := Chapter1.Section02.IndexTwo.isSylowIn_map hKS f.toMonoidHom
  rw [map_inf _ _ _ f.injective,hSf] at hKS'
  have hSK' : baumann (T : Subgroup G) ≤ normalizer (K' : Set G) := by
    have hh := map_mono (f:=f.toMonoidHom) hSK
    rwa [hSf,map_equiv_normalizer_eq] at hh
  have hCN' : C' ≤ normalizer (K' : Set G) := by
    have hh := map_mono (f:=f.toMonoidHom) hCN
    rwa [map_equiv_normalizer_eq] at hh
  refine ⟨s,⟨hs,hchoice,hK.of_mulEquiv a,hcore',hz',hKS',hSK',hout',?_,hCB',hc',hCN',
    hP',map_mono hPK,hPL,?_⟩⟩
  · intro he
    change K'=L at he
    apply hout'
    rw [he]
    exact (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  · let hCR' : C' ≤ localOrbit T L := hCB'.trans ((map_subtype_le _).trans inf_le_left)
    let q' := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR')
    let A' := ((MonoidHom.snd _ _).comp q').ker.map C'.subtype
    have hPA : P' ≤ A' := by
      intro p hp
      have hpC : p ∈ C' := map_mono hPC hp
      refine ⟨⟨p,hpC⟩,?_,rfl⟩
      change (originalA5ProductProjection D e hn ht htn ⟨p,hCR' hpC⟩).2 = 1
      have he := originalA5ProductProjection_first D e hn ht htn ⟨p,hPL hp⟩
      exact congrArg Prod.snd he
    have hA : Nat.card A'=3 :=
      (source_original_borel_torus_axes D e hn ht htn hb hz C' hCB' hc').2.2.1
    exact (eq_of_le_of_card_ge hPA (by rw [hA,hP'])).symm

/-- The oriented selected cubic gives the same literal Sylow and Borel in both blocks. -/
theorem SourceOriginalOrientedTorus.common_sylow_borel
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
    {hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)}
    {t : G} {ht : t ∈ (T : Subgroup G)} {htn : t ∉ normalizer (L : Set G)}
    {K C P : Subgroup G} {s : G}
    (O : SourceOriginalOrientedTorus D e hn ht htn K C P s)
    (hL : IsL2EvenBlock L 2) (hcoreL : pCore 2 L=blockU L)
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let K' := K.map (MulAut.conj s).toMonoidHom
    let P' := P.map (MulAut.conj s).toMonoidHom
    let S := baumann (T : Subgroup G)
    ⁅S,P'⁆=S ⊓ L ∧ ⁅S,P'⁆=S ⊓ K' ∧
      Chapter1.IsSylowIn 2 ⁅S,P'⁆ L ∧ Chapter1.IsSylowIn 2 ⁅S,P'⁆ K' ∧
      ⁅S,P'⁆ ⊔ P' ≤ L ⊓ K' ∧
      P' ≤ normalizer ((⁅S,P'⁆ : Subgroup G) : Set G) ∧
      (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
        normalizer ((⁅S,P'⁆ ⊔ P' : Subgroup G) : Set G) ∧
      ⁅S,P'⁆ ⊔ P'=L ⊓ normalizer ((⁅S,P'⁆ : Subgroup G) : Set G) ∧
      ⁅S,P'⁆ ⊔ P'=K' ⊓ normalizer ((⁅S,P'⁆ : Subgroup G) : Set G) := by
  let K' := K.map (MulAut.conj s).toMonoidHom
  let P' := P.map (MulAut.conj s).toMonoidHom
  let S := baumann (T : Subgroup G)
  have hPC : P' ≤ C.map (MulAut.conj s).toMonoidHom := by
    change P.map (MulAut.conj s).toMonoidHom ≤ _
    rw [←O.first_axis]
    exact map_subtype_le _
  have hPS : P' ≤ normalizer (S : Set G) :=
    hPC.trans (O.borel.trans (source_original_borel_normalizes_baumann hSO hS))
  have hne : P' ≠ ⊥ := by
    intro he
    have hh := O.cubic_card
    change Nat.card P'=3 at hh
    rw [he,card_bot] at hh
    contradiction
  obtain ⟨heL,hPL⟩ := source_original_natural_commutator_sylow D P'
    hL hcoreL hS O.cubic_original O.cubic_card hPS hSL
  obtain ⟨heK,hPK⟩ := IsL2EvenBlock.ambient_odd_commutator_sylow K' S P'
    O.natural O.core O.sylow O.cubic_block (by rw [O.cubic_card]; decide) hne hPS O.normalized
  have hPN : P' ≤ normalizer ((⁅S,P'⁆ : Subgroup G) : Set G) := by
    rw [heL]
    exact (le_inf hPS (O.cubic_original.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  refine ⟨heL,heK,hPL,hPK,?_,hPN,?_,?_,?_⟩
  · exact sup_le (le_inf (heL.le.trans inf_le_right) (heK.le.trans inf_le_right))
      (le_inf O.cubic_original O.cubic_block)
  · rw [heL]
    exact Chapter1.a5_sylow_cubic_borel_normalized L S P' _ e (heL ▸ hPL)
      O.cubic_original O.cubic_card hPS inf_le_right
      (inf_le_left.trans ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)))
  · exact Chapter1.a5_sylow_cubic_borel_eq_normalizer L ⁅S,P'⁆ P' e hPL
      O.cubic_original O.cubic_card hPN
  · obtain ⟨eK⟩ := O.natural.four_quotient_alternatingFive
    exact Chapter1.a5_sylow_cubic_borel_eq_normalizer K' ⁅S,P'⁆ P' eK hPK
      O.cubic_block O.cubic_card hPN

/-- The oriented data construct the actual proper common component with three-rank at most one. -/
theorem SourceOriginalOrientedTorus.terminal_component
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
    {hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)}
    {t : G} {ht : t ∈ (T : Subgroup G)} {htn : t ∉ normalizer (L : Set G)}
    {K C P : Subgroup G} {s : G}
    (O : SourceOriginalOrientedTorus D e hn ht htn K C P s)
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hL : IsL2EvenBlock L 2) (hcoreL : pCore 2 L=blockU L)
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let K' := K.map (MulAut.conj s).toMonoidHom
    let C' := C.map (MulAut.conj s).toMonoidHom
    let hCR : C' ≤ localOrbit T L := O.borel.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    let D₂ := ((MonoidHom.fst _ _).comp q).ker.map C'.subtype
    ∃! I : Subgroup G,
      I ∈ Chapter1.cComponentsIn
        (normalizer ((⁅baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G)) ∧
      L < I ∧ K' ≤ I ∧
      I ≤ centralizer ((⁅baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G) ∧
      primeRank 3 I ≤ 1 := by
  apply source_original_torus_first_axis_component D e hn ht htn hb hz hL hcoreL hSO hS hSL
    (K.map (MulAut.conj s).toMonoidHom) (C.map (MulAut.conj s).toMonoidHom)
    O.natural O.core O.sylow O.normalized O.escapes O.borel O.torus_card
  · rw [O.first_axis]
    exact O.cubic_block
  · exact (map_subtype_le _).trans O.torus_normalizes

/-- Either original quotient axis yields the terminal component while keeping D, L and T fixed. -/
theorem source_original_oriented_terminal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hL : IsL2EvenBlock L 2) (hcoreL : pCore 2 L=blockU L)
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    (K C P : Subgroup G) (hK : IsL2EvenBlock K 2) (hcoreK : pCore 2 K=blockU K)
    (hzK : center K=⊥)
    (hKS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G) ⊓ K) K)
    (hSK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ D.maximalLocal)
    (hCB : C ≤ sourceOrbitBorel T L) (hc : Nat.card C=9)
    (hPK : P ≤ K) (hP : Nat.card P=3) (hCN : C ≤ normalizer (K : Set G)) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    (P=((MonoidHom.snd _ _).comp q).ker.map C.subtype ∨
     P=((MonoidHom.fst _ _).comp q).ker.map C.subtype) →
    ∃ s : G, ∃ O : SourceOriginalOrientedTorus D e hn ht htn K C P s,
      let K' := K.map (MulAut.conj s).toMonoidHom
      let C' := C.map (MulAut.conj s).toMonoidHom
      let hCR' : C' ≤ localOrbit T L := O.borel.trans ((map_subtype_le _).trans inf_le_left)
      let q' := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR')
      let D₂ := ((MonoidHom.fst _ _).comp q').ker.map C'.subtype
      ∃! I : Subgroup G,
        I ∈ Chapter1.cComponentsIn
          (normalizer ((⁅baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G)) ∧
        L < I ∧ K' ≤ I ∧
        I ≤ centralizer ((⁅baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G) ∧
        primeRank 3 I ≤ 1 := by
  dsimp only
  intro hor
  obtain ⟨s,O⟩ := source_original_orient_selected_axis D e hn ht htn hb hz K C P
    hK hcoreK hzK hKS hSK hout hCB hc hPK hP hCN hor
  exact ⟨s,O,O.terminal_component hb hz hL hcoreL hSO hS hSL⟩
end CFSG.Quasithin.Chapter10
