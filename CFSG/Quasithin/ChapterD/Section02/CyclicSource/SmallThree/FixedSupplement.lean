module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.AmbientSeed
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.Support
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFixedSupplement
public import Theory.GroupTheory.PGroup.CentralProductCore
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Split
public import CFSG.Quasithin.ChapterD.Section02.JhatRestriction

/-!
# A fixed supplement before full Fitting movement

The canonical order-three planes split the original module into their moved
support and fixed space. Every original starred actor fixes one of these
summands. The two generated actor subgroups commute and are normal. On the
fixed side, any new two-dimensional cubic support would be an original
canonical factor and hence act trivially, so that side is the no-small-three
case. Its fixed-space theorem makes the original three-core fixed space
globally fixed. An ambient Sylow-fixed generating seed supplies the required
canonical-complement condition without assuming full movement or generation
by the restricted subgroup.

Source: Aschbacher--Smith D.2.25--29, printed pp.190--192, used on the original
Jhat in 15.1.2, first paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] [Group.IsSolvable G] [FiniteDimensional (ZMod 2) V] in
private theorem fixed_by_join' (W : Submodule (ZMod 2) V) (Q : Set (Subgroup G))
    (h : ∀ A ∈ Q, W ≤ fixedSpace ρ A) : W ≤ fixedSpace ρ (sSup Q) := by
  rw [sSup_eq_iSup',fixedSpace_iSup_family]
  exact le_iInf fun A => h A A.property

omit [Finite G] [Group.IsSolvable G] [FiniteDimensional (ZMod 2) V] in
private theorem commute_of_complement (hf : Function.Injective ρ)
    {K L : Subgroup G} {U W : Submodule (ZMod 2) V}
    (hspan : U ⊔ W = ⊤)
    (hsW : K ≤ subspaceStabilizer ρ W) (hsU : L ≤ subspaceStabilizer ρ U)
    (hKU : U ≤ fixedSpace ρ K) (hLW : W ≤ fixedSpace ρ L) :
    L ≤ centralizer (K : Set G) := by
  intro y hy x hx
  apply hf
  ext v
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ W from hspan ▸ Submodule.mem_top)
  have hxu : ρ x u = u := hKU hu ⟨x,hx⟩
  have hyw : ρ y w = w := hLW hw ⟨y,hy⟩
  have hxyu : ρ x (ρ y u) = ρ y u := hKU ((hsU hy u).mpr hu) ⟨x,hx⟩
  have hyxw : ρ y (ρ x w) = ρ x w := hLW ((hsW hx w).mpr hw) ⟨y,hy⟩
  simp only [map_mul,Module.End.mul_apply,map_add,hxu,hyw,hxyu,hyxw]

omit [Finite G] [Group.IsSolvable G] [FiniteDimensional (ZMod 2) V] in
private theorem commutator_top_eq_of_fixed_complement
    {W U : Submodule (ZMod 2) V} (hspan : W ⊔ U = ⊤)
    {X : Subgroup G} (hfix : U ≤ fixedSpace ρ X) :
    subspaceCommutator ρ ⊤ X = subspaceCommutator ρ W X := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    obtain ⟨w,hw,u,hu,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ U from hspan ▸ Submodule.mem_top)
    have he : ρ g u = u := hfix hu ⟨g,hg⟩
    rw [map_add,he,add_sub_add_right_eq_sub]
    exact Submodule.subset_span ⟨g,hg,w,hw,rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hg,v,Submodule.mem_top,rfl⟩

omit [Group.IsSolvable G] in
private theorem residual_side_no_smallThree (K : Subgroup G) [K.Normal]
    (U W : Submodule (ZMod 2) V)
    (hs : K ≤ subspaceStabilizer ρ W) (hspan : W ⊔ U = ⊤)
    (hKU : U ≤ fixedSpace ρ K)
    (hW : let := BinaryGroupAction.action ρ
      W = fixedSpace ρ (smallSupportGroup G (Multiplicative V) 1)) :
    ∀ X : Subgroup K, X ≤ pCore 3 K → Nat.card X = 3 →
      Module.finrank (ZMod 2)
        (subspaceCommutator (RatioDecomposition.side ρ K W hs) ⊤ X) ≠ 2 := by
  let := BinaryGroupAction.action ρ
  let Y := smallSupportGroup G (Multiplicative V) 1
  intro X hX hc hd
  have hcore : (pCore 3 K).map K.subtype ≤ pCore 3 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
  have hX3 : X.map K.subtype ≤ pCore 3 G := (Subgroup.map_mono hX).trans hcore
  have hcard : Nat.card (X.map K.subtype) = 3 := by
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hfix : U ≤ fixedSpace ρ (X.map K.subtype) :=
    hKU.trans (fixedSpace_antitone ρ (map_subtype_le X))
  have hm := subspaceCommutator_map_embedding (ρ.comp K.subtype)
    (RatioDecomposition.side ρ K W hs) (MonoidHom.id K) W.subtype
    (fun _ _ => rfl) X ⊤
  have he : subspaceCommutator ρ ⊤ (X.map K.subtype) =
      (subspaceCommutator (RatioDecomposition.side ρ K W hs) ⊤ X).map W.subtype := by
    rw [commutator_top_eq_of_fixed_complement ρ hspan hfix]
    simpa only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,
      subspaceCommutator_comp_map] using hm
  have hdim : Module.finrank (ZMod 2)
      (subspaceCommutator ρ ⊤ (X.map K.subtype)) = 2 := by
    rw [he,Submodule.finrank_map_subtype_eq]
    exact hd
  have hcan : X.map K.subtype ∈ smallSupportFactors G (Multiplicative V) 1 :=
    (x1_eq_canonical ρ) ▸ ⟨hX3,hcard,hdim⟩
  have hXY : X.map K.subtype ≤ Y := le_sSup hcan
  have hside : subspaceCommutator (RatioDecomposition.side ρ K W hs) ⊤ X = ⊥ := by
    apply le_bot_iff.mp
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    have hvY : (v:V) ∈ fixedSpace ρ Y := by
      change (v:V) ∈ fixedSpace ρ (smallSupportGroup G (Multiplicative V) 1)
      rw [←hW]
      exact v.property
    have he : ρ (g:G) (v:V) = (v:V) :=
      hvY ⟨g,hXY (mem_map_of_mem K.subtype hg)⟩
    have he' : RatioDecomposition.side ρ K W hs g v = v := Subtype.ext he
    rw [he',sub_self]
    exact Submodule.zero_mem _
  rw [hside,finrank_bot] at hd
  omega


/-- Separating the original canonical cubic support reduces its fixed side to
 the no-small-three source case, without any full-movement hypothesis. -/
theorem CoreHypotheses.threeCore_fixed_le_global_of_smallThree_complement
    (h : CoreHypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hfix : let := BinaryGroupAction.action ρ
      ∀ t ∈ smallSupportInvolutions ρ,
        t ∉ centralizer (smallSupportGroup G (Multiplicative V) 1 : Set G) →
        fixedSpace ρ (smallSupportGroup G (Multiplicative V) 1) ≤ fixedSpace ρ (zpowers t)) :
    fixedSpace ρ (pCore 3 G) ≤ fixedSpace ρ ⊤ := by
  classical
  let := BinaryGroupAction.action ρ
  let Y := smallSupportGroup G (Multiplicative V) 1
  let U := subspaceCommutator ρ ⊤ Y
  let W := fixedSpace ρ Y
  have hY3 : Y ≤ pCore 3 G := canonical_le_threeCore ρ
  have hodd : Odd (Nat.card Y) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).to_le hY3 |>.exists_card_eq
    exact hn ▸ (by decide : Odd 3).pow
  have hcompl : IsCompl U W := (ElementaryCore.SupportExclusion.moved_split ρ Y hodd).symm
  have hsU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U :=
    fun g _ v => subspaceCommutator_invariant_normalizer ρ (X := Y) (A := ⊤)
      (D := ⊤) (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      le_normalizer_of_normal (mem_top g) v
  have hsW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    exact fun g _ v hv => (normalFixed ρ Y).apply_mem_toSubmodule g hv
  have hdich : ∀ A ∈ QhatStar ρ, U ≤ fixedSpace ρ A ∨ W ≤ fixedSpace ρ A := by
    intro A hA
    obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
    have hsmall : t ∈ smallSupportInvolutions ρ := by
      refine ⟨ht,?_⟩
      change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
      rw [←fixedCodim_zpowers_eq_displacement_rank,he]
      have hh := (starred_codimension ρ hA (h.rank_one A hA)).trans_le h.ratio_le
      exact_mod_cast hh
    rw [←he]
    by_cases hc : t ∈ centralizer (Y : Set G)
    · exact Or.inl (canonical_support_fixed_of_centralizes ρ t
        (by simpa only [ht] using pow_orderOf_eq_one t) hc)
    · exact Or.inr (hfix t hsmall hc)
  let Q : Set (Subgroup G) := {A | A ∈ QhatStar ρ ∧ U ≤ fixedSpace ρ A}
  let R : Set (Subgroup G) := {A | A ∈ QhatStar ρ ∧ ¬ U ≤ fixedSpace ρ A}
  let K := sSup Q
  let L := sSup R
  have hKU : U ≤ fixedSpace ρ K := fixed_by_join' ρ U Q (fun _ h => h.2)
  have hLW : W ≤ fixedSpace ρ L := fixed_by_join' ρ W R
    (fun A hA => (hdich A hA.1).resolve_left hA.2)
  have hgen : K ⊔ L = ⊤ := by
    have he : Q ∪ R = QhatStar ρ := by
      ext A
      change (A ∈ QhatStar ρ ∧ U ≤ fixedSpace ρ A) ∨
        (A ∈ QhatStar ρ ∧ ¬ U ≤ fixedSpace ρ A) ↔ A ∈ QhatStar ρ
      tauto
    simpa only [K,L,←sSup_union,he,Jhat] using h.generated
  have hCK : L ≤ centralizer (K : Set G) := commute_of_complement ρ h.faithful
    hcompl.sup_eq_top (le_top.trans hsW) (le_top.trans hsU) hKU hLW
  let : K.Normal := normal_of_centralizing_sup_eq_top K L hgen hCK
  have hKP (p : ℕ) : (pCore p K).map K.subtype ≤ pCore p G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
  have hWK : K ≤ subspaceStabilizer ρ W := le_top.trans hsW
  by_cases hQ : Q.Nonempty
  · obtain ⟨A,hAQ⟩ := hQ
    have hAK : A ≤ K := le_sSup hAQ
    let ψ := RatioDecomposition.side ρ K W hWK
    have ht := RatioDecomposition.side_transport ρ hWK hcompl.symm.sup_eq_top hKU
      ⟨A,hAQ.1,hAK⟩
    have hψgen : Jhat ψ = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
      apply le_antisymm (map_subtype_le _)
      apply sSup_le
      intro B hB
      have hBK : B ≤ K := le_sSup hB
      have hB' : B.subgroupOf K ∈ QhatStar ψ :=
        (ht.2 _).mpr (by rw [map_subgroupOf_eq_of_le hBK]; exact hB.1)
      have hm := Subgroup.map_mono (le_sSup hB') (f := K.subtype)
      simpa only [Jhat,map_subgroupOf_eq_of_le hBK] using hm
    have hψ : CoreHypotheses ψ := by
      refine ⟨RatioDecomposition.side_faithful ρ h.faithful hWK
        hcompl.symm.sup_eq_top hKU,ht.1 ▸ h.ratio_le,hψgen,
        generalizedFitting_eq_fitting_of_solvable K,?_,?_⟩
      · rw [pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal,h.twoCore,
          MonoidHom.comap_bot]
        exact (MonoidHom.ker_eq_bot_iff K.subtype).mpr K.subtype_injective
      · intro B hB
        rw [←rank_map_injective K.subtype K.subtype_injective]
        exact h.rank_one _ ((ht.2 B).mp hB)
    have hψfive : ∀ B ∈ QhatStar ψ, ⁅pCore 5 K,B⁆ = ⊥ := by
      intro B hB
      apply (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
      rw [map_commutator]
      exact le_bot_iff.mp ((commutator_mono (hKP 5) le_rfl).trans_eq
        (hfive _ ((ht.2 B).mp hB)))
    have hNo := residual_side_no_smallThree ρ K U W hWK
      hcompl.symm.sup_eq_top hKU rfl
    have hψfixed := hψ.threeCore_fixed_le_global (ht.1.trans hq) hψfive hNo
    intro v hv
    have hvW : v ∈ W := fixedSpace_antitone ρ hY3 hv
    have hvψ : (⟨v,hvW⟩ : W) ∈ fixedSpace ψ (pCore 3 K) := by
      intro x
      apply Subtype.ext
      exact hv ⟨x,hKP 3 (mem_map_of_mem K.subtype x.property)⟩
    have hvK : v ∈ fixedSpace ρ K := by
      intro x
      exact congrArg Subtype.val (hψfixed hvψ ⟨x,mem_top x⟩)
    have hvL : v ∈ fixedSpace ρ L := hLW hvW
    have he : fixedSpace ρ (K ⊔ L) = fixedSpace ρ K ⊓ fixedSpace ρ L := by
      simpa only [iSup_bool_eq,Bool.false_eq_true,↓reduceIte,iInf_bool_eq] using
        fixedSpace_iSup_family ρ (fun b : Bool => if b then K else L)
    rw [←hgen,he]
    exact ⟨hvK,hvL⟩
  · have hKe : K = ⊥ := by
      change sSup Q = ⊥
      rw [Set.not_nonempty_iff_eq_empty.mp hQ,sSup_empty]
    have hLe : L = ⊤ := by simpa only [hKe,bot_sup_eq] using hgen
    rw [hLe] at hLW
    exact (fixedSpace_antitone ρ hY3).trans hLW


/-- The same fixed-space conclusion with the actual orbit-generating Sylow seed
in an ambient group; no seed generation inside H is assumed. -/
theorem CoreHypotheses.threeCore_fixed_le_global_of_ambient_seed
    {D : Type*} [Group D] [Finite D] [Group.IsSolvable D]
    (τ : Representation (ZMod 2) D V) (H : Subgroup D) [H.Normal]
    (h : CoreHypotheses (τ.comp H.subtype))
    (S : Sylow 2 D) (Z : Submodule (ZMod 2) V)
    (hseed : Z ≤ fixedSpace τ (S : Subgroup D))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ τ g v = w}=⊤)
    (hq : cubicRatio (τ.comp H.subtype) = 2)
    (hfive : ∀ A∈QhatStar (τ.comp H.subtype),⁅pCore 5 H,A⁆=⊥) :
    fixedSpace (τ.comp H.subtype) (pCore 3 H) ≤
      fixedSpace (τ.comp H.subtype) ⊤ := by
  apply h.threeCore_fixed_le_global_of_smallThree_complement (τ.comp H.subtype)
    hq hfive
  dsimp only
  intro t ht hc
  exact h.fixed_smallThree_complement_of_ambient_seed τ H S Z hseed hspan
    hfive hq (t := t) ht hc

/-- Coprime splitting of the original three-core now has a globally fixed
supplement even in the canonical small-three case. -/
theorem CoreHypotheses.threeCore_fixed_supplement_of_ambient_seed
    {D : Type*} [Group D] [Finite D] [Group.IsSolvable D]
    (τ : Representation (ZMod 2) D V) (H : Subgroup D) [H.Normal]
    (h : CoreHypotheses (τ.comp H.subtype))
    (S : Sylow 2 D) (Z : Submodule (ZMod 2) V)
    (hseed : Z ≤ fixedSpace τ (S : Subgroup D))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ τ g v = w}=⊤)
    (hq : cubicRatio (τ.comp H.subtype) = 2)
    (hfive : ∀ A∈QhatStar (τ.comp H.subtype),⁅pCore 5 H,A⁆=⊥) :
    subspaceCommutator (τ.comp H.subtype) ⊤ (pCore 3 H) ⊔
      fixedSpace (τ.comp H.subtype) ⊤ = ⊤ := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := H)).exists_card_eq
  have ho : Odd (Nat.card (pCore 3 H)) := by
    rw [hn]
    exact (by decide : Odd 3).pow
  have hc : IsCompl (fixedSpace (τ.comp H.subtype) (pCore 3 H))
      (subspaceCommutator (τ.comp H.subtype) ⊤ (pCore 3 H)) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := τ.comp H.subtype) ho)
  apply top_unique
  exact hc.symm.sup_eq_top.symm.le.trans
    (sup_le_sup_left (h.threeCore_fixed_le_global_of_ambient_seed τ H S Z hseed hspan hq hfive) _)

end CFSG.Quasithin.ChapterD.CyclicSource
