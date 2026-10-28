module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFF
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import Theory.Representation.BinaryOffender.RankOneGeneratedRestriction
public import Theory.Representation.BinaryOffender.RankOneCentralizer

/-!
# Faithful models for the reduced transvection normal closures

In the abelian odd configuration, each nonidentity moving actor on W/Z_S
has rank-one displacement. Restrict its faithful reduced representation to
the literal orbit of that displacement. The restriction kernel meets the
actor's normal closure in a normal two-subgroup, hence trivially, and is
exactly the centralizer of that normal closure. In the restricted image,
the normal closure remains core-free and self-centralizing; consequently
the whole image has trivial two-core. The original SQTK cover descends to
this image, so all hypotheses of the proved G.6.4 are discharged.

The output retains the actual displacement subspace, the original normal
closure and its explicit isomorphism onto the classified closure. This does
not assert that the displacement orbit is the whole W/Z_S, nor that the
original W/<z> action has trivial two-core. These marked models feed the
component sieve in 6.1.19. That sieve, the amalgam contradiction, initial
naturalness and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith, 6.1.19, printed pp.674–675, and G.6.1–4,
printed pp.345–346.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- The actual displacement orbit and its faithful action image. -/
structure TransvectionOrbitModel (ρ : Representation (ZMod 2) D V) (t : D) where
  space : Subrepresentation ρ
  space_eq : space.toSubmodule = conjugateDisplacementSpan ρ t ⊤
  kernel_eq : space.toRepresentation.asGroupHom.ker =
    centralizer (normalClosure ({t} : Set D) : Set D)
  closure_injective : Function.Injective
    (space.toRepresentation.asGroupHom.subgroupMap (normalClosure ({t} : Set D)))
  core : pCore 2 space.toRepresentation.asGroupHom.range = ⊥
  generated : conjugateDisplacementSpan space.toRepresentation t ⊤ = ⊤
  rank_one : Module.finrank (ZMod 2)
    (LinearMap.range (space.toRepresentation t - LinearMap.id)) = 1
  classification :
    let q := space.toRepresentation.asGroupHom.rangeRestrict
    let τ : Representation (ZMod 2) space.toRepresentation.asGroupHom.range space.toSubmodule :=
      (Units.coeHom _).comp space.toRepresentation.asGroupHom.range.subtype
    ChapterG.Section06.Conclusion τ (q t)

private theorem centralizer_fixes_orbit
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (t : D)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1)
    (b : D) (hb : b ∈ centralizer (normalClosure ({t} : Set D) : Set D)) :
    ∀ w ∈ conjugateDisplacementSpan ρ t ⊤, ρ b w = w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, _, v, rfl⟩ := hw
    let a := g * t * g⁻¹
    have ha : a ∈ normalClosure ({t} : Set D) :=
      (inferInstance : (normalClosure ({t} : Set D)).Normal).conj_mem t
        (subset_normalClosure (Set.mem_singleton t)) g
    have hc : Commute a b := mem_centralizer_iff.mp hb a ha
    have har : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 := by
      have he := fixedCodim_zpowers_conj ρ t g
      simp only [fixedCodim_zpowers_eq_displacement_rank] at he
      exact he.trans hr
    have he : ρ g (ρ t v - v) = ρ a (ρ g v) - ρ g v := by
      simp only [a, map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [he]
    exact fixes_displacement_of_commute_rank_one ρ a b har hc _
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

/-- Restricting to the marked transvection's displacement orbit loses exactly
its normal-closure centralizer; the normal closure itself survives faithfully. -/
theorem transvection_orbit_model
    (h : ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple ρ)
    (t : D) (ht : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1) :
    Nonempty (TransvectionOrbitModel ρ t) := by
  let := h.finite_module
  obtain ⟨S,hS,hgen,hrS⟩ := rank_one_generated_restriction ρ h.faithful h.twoCore t ht1 hr
  let f := S.toRepresentation.asGroupHom
  let q := f.rangeRestrict
  let B := f.range
  let τ : Representation (ZMod 2) B S.toSubmodule := (Units.coeHom _).comp B.subtype
  let K := normalClosure ({t} : Set D)
  let N := f.ker
  have hNKtwo : IsPGroup 2 (N ⊓ K : Subgroup D) := by
    intro b
    refine ⟨1,?_⟩
    apply Subtype.ext
    change (b : D)^2=1
    apply h.faithful
    ext v
    have hv : ρ b v-v ∈ S.toSubmodule := by
      rw [hS,←commutator_conjugateSpanBy_zpowers,conjugateSpanBy_zpowers_top]
      exact Submodule.subset_span ⟨b,b.property.2,v,Submodule.mem_top,rfl⟩
    have he : S.toRepresentation b = 1 :=
      congrArg Units.val (show f b = 1 from b.property.1)
    have hh := congrArg (fun e : Module.End (ZMod 2) S.toSubmodule => e ⟨_,hv⟩) he
    have hfix : ρ b (ρ b v-v)=ρ b v-v := congrArg Subtype.val hh
    rw [map_sub,sub_eq_sub_iff_add_eq_add] at hfix
    have hbb : ρ b (ρ b v)=v := by
      have hz : ρ b (ρ b v)+v=0 := by simpa only [ZModModule.add_self] using hfix
      calc
        ρ b (ρ b v) = (ρ b (ρ b v)+v)+v := by rw [add_assoc,ZModModule.add_self,add_zero]
        _ = v := by rw [hz,zero_add]
    simpa only [pow_two,map_mul,map_one,Module.End.mul_apply,Module.End.one_apply] using hbb
  have hNK : N ⊓ K = ⊥ := by
    apply le_bot_iff.mp
    rw [←h.twoCore]
    exact le_sSup ⟨inferInstance,hNKtwo⟩
  have hker : N = centralizer (K : Set D) := by
    apply le_antisymm
    · exact commutator_eq_bot_iff_le_centralizer.mp
        (commutator_eq_bot_of_disjoint (disjoint_iff.mpr hNK))
    · intro b hb
      change f b = 1
      apply Units.ext
      ext w
      exact centralizer_fixes_orbit ρ t hr b hb w (hS ▸ w.property)
  have hfinj : Function.Injective (f.subgroupMap K) := by
    intro x y he
    have hd : (x : D)/(y : D) ∈ N ⊓ K := by
      refine ⟨?_,K.div_mem x.property y.property⟩
      change f ((x : D)/(y : D)) = 1
      have he' : f (x : D) = f (y : D) := congrArg Subtype.val he
      rw [map_div,he',div_self']
    exact Subtype.ext (div_eq_one.mp (hNK.le hd))
  have hqinj : Function.Injective (q.subgroupMap K) := by
    intro x y he
    apply hfinj
    apply Subtype.ext
    exact congrArg (fun b : K.map q => ((b : B) : (Module.End (ZMod 2) S.toSubmodule)ˣ)) he
  have hKcore : pCore 2 K = ⊥ := by
    have hm : (pCore 2 K).map K.subtype ≤ pCore 2 D :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    apply le_bot_iff.mp
    intro k hk
    exact Subtype.ext (mem_bot.mp (h.twoCore ▸ hm (mem_map_of_mem K.subtype hk)))
  have hKimage : pCore 2 (K.map q) = ⊥ := by
    let e := MulEquiv.ofBijective (q.subgroupMap K) ⟨hqinj,q.subgroupMap_surjective K⟩
    rw [←pCore_map_iso 2 e,hKcore,Subgroup.map_bot]
  have hτ : Function.Injective τ := by
    intro x y he
    exact Subtype.ext (Units.ext he)
  have hqsur : Function.Surjective q := f.rangeRestrict_surjective
  have hτgen : conjugateDisplacementSpan τ (q t) ⊤ = ⊤ := by
    rw [←hgen]
    apply congrArg (Submodule.span (ZMod 2))
    ext w
    constructor
    · rintro ⟨g,_,v,rfl⟩
      obtain ⟨b,rfl⟩ := hqsur g
      exact ⟨b,mem_top _,v,rfl⟩
    · rintro ⟨g,_,v,rfl⟩
      exact ⟨q g,mem_top _,v,rfl⟩
  have hτrank : Module.finrank (ZMod 2) (LinearMap.range (τ (q t)-LinearMap.id)) = 1 := hrS
  have hclosure : K.map q = normalClosure ({q t} : Set B) := by
    simpa only [Set.image_singleton] using map_normalClosure ({t} : Set D) q hqsur
  have hcentral : centralizer (K.map q : Set B) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro b hb
    apply hτ
    apply LinearMap.ext
    intro w
    have hh := centralizer_fixes_orbit τ (q t) hτrank b (hclosure ▸ hb) w
      (hτgen.symm ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) S.toSubmodule)))
    simpa only [map_one,Module.End.one_apply] using hh
  have hBcore : pCore 2 B = ⊥ := by
    let Q := (pCore 2 B).comap (K.map q).subtype
    have hQ : Q ≤ pCore 2 (K.map q) :=
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective _ (K.map q).subtype_injective⟩
    have hmeet : pCore 2 B ⊓ K.map q = ⊥ := by
      apply (eq_bot_iff_forall _).mpr
      rintro b ⟨hb,hbK⟩
      have hz : (⟨b,hbK⟩ : K.map q) ∈ (⊥ : Subgroup (K.map q)) :=
        hKimage ▸ hQ (show (⟨b,hbK⟩ : K.map q) ∈ Q from hb)
      exact congrArg Subtype.val (mem_bot.mp hz)
    let : (K.map q).Normal := (inferInstance : K.Normal).map q hqsur
    have hc : pCore 2 B ≤ centralizer (K.map q : Set B) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (commutator_eq_bot_of_disjoint (disjoint_iff.mpr hmeet))
    exact le_bot_iff.mp (hc.trans_eq hcentral)
  obtain ⟨cover⟩ := h.quotient
  let π : cover.Cover →* D := cover.equiv.toMonoidHom.comp (QuotientGroup.mk' cover.kernel)
  have hπ : Function.Surjective π := cover.equiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqt : q t ≠ 1 := by
    intro he
    have hh : τ (q t)-LinearMap.id = 0 := by rw [he,map_one]; exact sub_self _
    rw [hh,LinearMap.range_zero] at hτrank
    simp at hτrank
  have hsource : ChapterG.Section06.Hypotheses KnownSimple.IsKnownSimple τ (q t) (q.comp π) := {
    finite_group := Finite.of_surjective q hqsur
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := cover.sqtk
    quotient_surjective := hqsur.comp hπ
    twoCore := hBcore
    faithful := hτ
    involution := by rw [←map_pow,ht,map_one]
    nonidentity := hqt
    displacement_rank := hτrank.le.trans (by decide)
    generated := hτgen }
  exact ⟨⟨S,hS,hker,hfinj,hBcore,hgen,hrS,ChapterG.Section06.lemma_G_6_4 hsource hτrank⟩⟩

/-- The original normal closure is isomorphic to the classified normal closure,
through the literal restricted action map. -/
@[expose] def TransvectionOrbitModel.closureEquiv {t : D} (d : TransvectionOrbitModel ρ t) :
    normalClosure ({t} : Set D) ≃*
      normalClosure ({d.space.toRepresentation.asGroupHom.rangeRestrict t} :
        Set d.space.toRepresentation.asGroupHom.range) := by
  let f := d.space.toRepresentation.asGroupHom
  let q := f.rangeRestrict
  let K := normalClosure ({t} : Set D)
  have hi : Function.Injective (q.subgroupMap K) := by
    intro x y he
    apply d.closure_injective
    apply Subtype.ext
    exact congrArg (fun b : K.map q =>
      ((b : f.range) : (Module.End (ZMod 2) d.space.toSubmodule)ˣ)) he
  let e := MulEquiv.ofBijective (q.subgroupMap K) ⟨hi,q.subgroupMap_surjective K⟩
  have hm : K.map q = normalClosure ({q t} : Set f.range) := by
    simpa only [Set.image_singleton] using
      map_normalClosure ({t} : Set D) q f.rangeRestrict_surjective
  exact e.trans (MulEquiv.subgroupCongr hm)

omit [Finite D] in
/-- The closure equivalence retains the original operator, so the classified
factors belong to the action of this normal closure. -/
theorem TransvectionOrbitModel.closureEquiv_apply {t : D}
    (d : TransvectionOrbitModel ρ t) (k : normalClosure ({t} : Set D)) :
    (d.closureEquiv k : d.space.toRepresentation.asGroupHom.range) =
      d.space.toRepresentation.asGroupHom.rangeRestrict k := rfl

open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)

/-- Each nonidentity moving actor has the full G.6.4 model on its literal
normal-closure displacement orbit in W/Z_S. The normal closure embeds into
that model, with its exact centralizer as the restriction kernel. -/
theorem exists_reduced_transvection_models
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      ∃ (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hN : (Z.subgroupOf W).Normal),
      letI := hN
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := hX
        let A := (E.subgroupOf I).map σ
        let J := (P.subgroupOf I).map σ
        let θ : Representation (ZMod 2) J (Additive (W ⧸ Z.subgroupOf W)) :=
          Representation.ofElementaryAbelianAction
          (A := J) (G := W ⧸ Z.subgroupOf W) (p := 2)
        IsElementaryAbelian 2 A ∧ 1 < Nat.card A ∧ Nat.card A ≤ 4 ∧
        commutatorAction A (W ⧸ Z.subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W))) = 2 ∧
        commutatorAction₂ A (W ⧸ Z.subgroupOf W) = ⊥ ∧
        σ.ker = (commutatorPreimage I W Z).subgroupOf I ∧
        J = conjugateSpanBy A σ.range ∧ pCore 2 J = ⊥ ∧
        ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple θ ∧
        ChapterB.SourceInduction.NontrivialAdequateAlternative θ ∧
        ∀ t : J, (t : MulAut (W ⧸ Z.subgroupOf W)) ∈ A → t ≠ 1 →
          Module.finrank (ZMod 2) (LinearMap.range
            (θ t - LinearMap.id (R := ZMod 2) (M := Additive (W ⧸ Z.subgroupOf W)))) = 1 ∧
            Nonempty (TransvectionOrbitModel θ t) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hZ'W,hEW,hIW,hN,σ,hσ,hX,hA,hpos,hsize,
      hdisp,hcard,hquad,hker,hspan,hcore,hff,hclass,hrank⟩ :=
    d.exists_reduced_ff_action h hnat hE hs hNS hab
  let := hN
  let := hX
  let := hA
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hZ'W,hEW,hIW,hN,σ,hσ,hX,hA,hpos,hsize,
    hdisp,hcard,hquad,hker,hspan,hcore,hff,hclass,?_⟩
  intro t ht ht1
  have hr := hrank t ht ht1
  have ht2 : t^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ ht)
  exact ⟨hr,transvection_orbit_model hff t ht2 ht1 hr⟩

end NaturalEscapeGraph.OddConfiguration

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
