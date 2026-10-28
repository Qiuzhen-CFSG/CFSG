module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import Theory.SpecificGroups.PSL3.LocalResidualFixer
public import Theory.AtlasPort.LinearGroups.G2.LongLocalFixer
public import Theory.AtlasPort.LinearGroups.G2.ShortLocalCoreCenter
public import Theory.SpecificGroups.Triality.CentralLocalFixer
public import Theory.SpecificGroups.Triality.ArmsLocalCoreCenter
public import Theory.GroupTheory.PCoreImage

/-!
# Ordinary row exclusions before full-normalizer identification

The actual fixed-radical involution and full Sylow placement exclude both
PSL₃ parabolic residuals, including the field of order four. For G₂ and
genuine triality over larger binary fields, one residual has central
core center, contradicting the fully moved source module; the other has
trivial involutory fixer, contradicting the original fixed-radical action.
Every quotient uses the original K, and every local subgroup is the image
of the original L. The full source module is kept distinct from chosen V.

These are literal OutsideChoice applications under Hypothesis1221, without
the unresolved H = N_G(K) premise. They narrow that premise's ordinary
cases; they do not close the other carrier rows or global uniqueness.
Final source selection and its ordinary normalizer remain with
qt-d-1222-rankone-global-uniqueness, while nonblock construction retains
its independent owner.

Source: Aschbacher–Smith C.3.1 and 4.3.6, printed pp.149–151,614–615.
The row arguments adapt OrdinaryRecognitionPlacement/Exceptional at the
earlier source boundary and reuse their existing model rigidity theorems.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The full source module supplies a noncentral core center in the original L. -/
theorem ordinaryModule_local_data (c : OutsideChoice T L)
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    let W := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
    let A := W.subgroupOf L
    A ≠ ⊥ ∧ ⁅A,(⊤ : Subgroup L)⁆ = A ∧
      A ≤ (center (pCore 2 L)).map (pCore 2 L).subtype := by
  let W := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let A := W.subgroupOf L
  have hc := c.c28 D h
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  have hWL : W ≤ L := by simpa only [hs] using hc.module_le
  have hm : W = ⁅W,L⁆ := by simpa only [hs] using hc.module_commutator
  have hmap : A.map L.subtype = W := map_subgroupOf_eq_of_le hWL
  have hmove : ⁅A,(⊤ : Subgroup L)⁆ = A := by
    apply map_injective L.subtype_injective
    rw [map_commutator,hmap,←MonoidHom.range_eq_map,range_subtype]
    exact hm.symm
  have hA : A.Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [hm]
    exact normalizer_commutator_ge_right _ _
  have hAp : IsPGroup 2 A := hc.module_elementary.isPGroup.comap_subtype
  have hAcore : A ≤ pCore 2 L := le_sSup ⟨hA,hAp⟩
  have hLR : L.pCoreIn 2 ≤ c.intermediate.pCoreIn 2 := by
    apply pCoreIn_mono_of_normalizes le_sup_left
    exact sup_le L.le_normalizer
      (inf_le_left.trans ((source_core_section_intersection D h).le.trans
        (inf_le_right.trans inf_le_left)))
  refine ⟨?_,hmove,?_⟩
  · intro hz
    have hh := congrArg (map L.subtype) hz
    rw [hmap,Subgroup.map_bot] at hh
    exact hc.module_nontrivial hh
  · intro w hw
    refine ⟨⟨w,hAcore hw⟩,mem_center_iff.mpr ?_,rfl⟩
    intro r
    obtain ⟨z,hz,he⟩ := hc.module_le_center_radical hw
    have hh := congrArg (fun x : c.intermediate.pCoreIn 2 => (x : G))
      (mem_center_iff.mp hz ⟨(r : L),hLR (mem_map_of_mem L.subtype r.property)⟩)
    apply Subtype.ext
    apply Subtype.ext
    change (r : G) * (w : G) = (w : G) * (r : G)
    change (r : G) * (z : G) = (z : G) * (r : G) at hh
    change (z : G) = (w : G) at he
    rwa [he] at hh

/-- Central quotient transport preserves the full module's core-center obstruction. -/
theorem ordinary_model_core_center_not_central
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype)
    {J : Type*} [Group J] [Finite J] (e : (K ⧸ center K) ≃* J) :
    let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    ¬ (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map q
  change ¬ (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B
  let k : L ≃* c.ordinaryLocal K := (c.ordinaryLocalEquiv hLK).symm
  let f : L →* B := (q.subgroupMap (c.ordinaryLocal K)).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective (c.ordinaryLocal K)).comp k.surjective
  have hqker : q.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    have hz : (k l : K) ∈ center K := by
      rw [←hqker]
      exact hh
    apply mem_center_iff.mpr
    intro m
    apply k.injective
    simpa only [map_mul] using
      (Subtype.ext (mem_center_iff.mp hz (k m : K)) : k m * k l = k l * k m)
  have hkp : IsPGroup 2 f.ker := by
    have hp : IsPGroup 2 q.ker := by
      let := ho.2
      rw [hqker,IsQuasisimple.center_eq_pCore (ho.1.pPrimeCore_eq_bot (c.c28 D h).oddCore_eq_bot)]
      exact pCore_isPGroup
    have hker : f.ker = q.ker.comap ((c.ordinaryLocal K).subtype.comp k.toMonoidHom) := by
      ext x
      exact Subtype.ext_iff
    rw [hker]
    exact hp.comap_of_injective _ ((c.ordinaryLocal K).subtype_injective.comp k.injective)
  have hcore : (pCore 2 L).map f = pCore 2 B := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hkp,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  let A := (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)).subgroupOf L
  obtain ⟨hne,hmove,hcentral⟩ := c.ordinaryModule_local_data D h
  let N := A.map f
  have hNcore : N ≤ pCore 2 B := by
    rw [←hcore]
    exact map_mono (hcentral.trans (map_subtype_le _))
  have hNc : N ≤ centralizer (pCore 2 B : Set B) := by
    rintro _ ⟨w,hw,rfl⟩ r hr
    rw [←hcore] at hr
    obtain ⟨r,hr,rfl⟩ := hr
    obtain ⟨z,hz,rfl⟩ := hcentral hw
    have hh : r * (z : L) = (z : L) * r :=
      congrArg Subtype.val (mem_center_iff.mp hz ⟨r,hr⟩)
    change f r * f (z : L) = f (z : L) * f r
    simpa only [map_mul] using congrArg f hh
  have hNmove : ⁅N,(⊤ : Subgroup B)⁆ = N := by
    rw [show (⊤ : Subgroup B) = (⊤ : Subgroup L).map f from
      (map_top_of_surjective _ hf).symm,←map_commutator,hmove]
  intro hc
  have hNZ : N ≤ center B := by
    intro n hn
    exact hc ⟨⟨n,hNcore hn⟩,
      mem_center_iff.mpr (fun r => Subtype.ext (hNc hn r r.property)),rfl⟩
  have hNzero : N = ⊥ := hNmove.symm.trans
    (commutator_top_right_eq_bot_iff_le_center.mpr hNZ)
  have hAZ : A ≤ center L := ((map_eq_bot_iff A).mp hNzero).trans hk
  exact hne (hmove.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr hAZ))

/-- The original local image has nontrivial two-core, including before the
full-normalizer identification. -/
theorem ordinary_model_local_core_ne_bot
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype)
    {J : Type*} [Group J] [Finite J] (e : (K ⧸ center K) ≃* J) :
    pCore 2 ((c.ordinaryLocal K).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))) ≠ ⊥ := by
  intro hz
  apply c.ordinary_model_core_center_not_central D h K ho hLK e
  rintro _ ⟨z,_,rfl⟩
  have hz' : (z : (c.ordinaryLocal K).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))) = 1 :=
    mem_bot.mp (hz ▸ z.property)
  change (z : (c.ordinaryLocal K).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))) ∈ center _
  rw [hz']
  exact one_mem _

variable (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
include D h hpsl ho hLK hout hKN

/-- Both PSL₃ parabolic residuals are excluded from the raw source choice.
The actual marking follows from the unchanged full Sylow, not a callback. -/
theorem ordinary_no_pslThree
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (e : (K ⧸ center K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨P,_,hlocal,hproper⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.linear_three_local_placement
    hF hm S ((c.ordinaryLocal K).map f) hlocal hproper
  let e' := e.trans (MulAut.conj g)
  have he : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  have hmark : (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      Matrix.PSL3.LinearThree.pointLocal F ∨
      (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      Matrix.PSL3.LinearThree.lineLocal F := by
    simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg
  let A := (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  have hUA : Matrix.PSL3.LinearThree.unipotent F ≤ A := by
    rcases hmark with he | he
    · dsimp only [A]
      rw [he]
      exact Matrix.PSL3.LinearThree.unipotent_le_pointLocal F
    · dsimp only [A]
      rw [he]
      exact Matrix.PSL3.LinearThree.unipotent_le_lineLocal F
  obtain ⟨a,hao,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e'
  have ha := Matrix.PSL3.LinearThree.eq_one_of_fixes_nonsolvable_unipotent_overgroup
    (by omega : 0 < m) hF A hUA (c.ordinary_quotient_local_nonsolvable h K hLK e') a hfix
  simp only [ha,orderOf_one] at hao
  omega

/-- Both G₂ parabolic residuals are excluded from the original outside choice.
The short row contradicts the full module; the long row contradicts R₀'s action. -/
theorem ordinary_no_g2
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (e : (K ⧸ center K) ≃* Atlas.G2.Model F) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨P,_,hlocal,hproper⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.local_placement
    hq S ((c.ordinaryLocal K).map f) hlocal hproper
  let e' := e.trans (MulAut.conj g)
  have he : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  have hm : (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      Atlas.G2.LieParabolicSetup.local₁ ∨
      (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      Atlas.G2.LieParabolicSetup.local₂ := by
    simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg
  rcases hm with hm | hm
  · have hc := c.ordinary_model_core_center_not_central D h K ho hLK e'
    dsimp only at hc
    rw [hm] at hc
    exact hc Atlas.G2.LieParabolicSetup.local₁_core_center_le_center
  · obtain ⟨a,hao,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e'
    rw [hm] at hfix
    have ha := Atlas.G2.LieParabolicSetup.local₂_fixer_eq_one hq a hfix
    simp only [ha,orderOf_one] at hao
    omega

/-- Both genuine triality parabolic residuals are excluded before full
normalizer equality, retaining all central covers and the same local image. -/
theorem ordinary_no_triality_large
    (m : ℕ) (hm : 0 < m) (hq : 2 < 2 ^ m)
    (e : (K ⧸ center K) ≃* Triality.Standard.BinaryCarrier m hm) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨P,_,hlocal,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
  obtain ⟨g,a,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality.local_placement
    m hm hq S ((c.ordinaryLocal K).map f) hlocal
      (c.ordinary_model_local_core_ne_bot D h K ho hLK e)
  let e' := e.trans (MulAut.conj g)
  have he : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  have hmark : (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      Triality.Standard.Parabolics.localFactor (Triality.Standard.binaryParameters m hm) a := by
    simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg
  cases a with
  | arms =>
    have hc := c.ordinary_model_core_center_not_central D h K ho hLK e'
    dsimp only at hc
    rw [hmark] at hc
    exact hc (Triality.Standard.Parabolics.arms_core_center_le_center _ rfl)
  | central =>
    obtain ⟨a,hao,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e'
    have ha2 : a ^ 2 = 1 := hao ▸ pow_orderOf_eq_one a
    rw [hmark] at hfix
    have ha := Triality.Standard.Parabolics.central_local_involutory_fixer_eq_one m hm a ha2 hfix
    simp only [ha,orderOf_one] at hao
    omega

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
