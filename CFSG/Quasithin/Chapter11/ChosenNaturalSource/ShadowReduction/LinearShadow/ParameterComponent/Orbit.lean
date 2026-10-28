module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.Reductions
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import Theory.Representation.BinaryConjugationSection.CentralKernel

/-!
# The active conjugate and its literal action in 11.3.4

The H-orbit of the original Sylow omega-center is constructed in the common
ambient group. B.2.14 proves that its intrinsic subgroup is reduced; B.6.8
then puts its Sylow centralizer in O₂(H). The counterexample reduction
W₀(T,V) ≰ O₂(H) therefore selects an actual conjugate V^g ≤ T acting
nontrivially on that orbit.

Conjugation descends through the literal quotient H/C_H(VH). Lifting
subgroups through that same projection and applying E.3.6 proves membership
of A* in the fixed-space family at s(G,V), giving 11.3.4(1).
The weak-closure escape itself makes the relative Sylow subgroup nonnormal.
No parameter equality or component recognition is assumed or concluded here.
The actual two-residual also supplements T and escapes N_G(L).

Source: Aschbacher--Smith, 11.3.3--4, printed p.771;
B.2.14, B.6.8 and E.3.6, printed pp.78,114,232
(combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- The actual ambient image of O²(H). -/
def residual (H : Subgroup G) : Subgroup G := (pResidual 2 H).map H.subtype

/-- The original Sylow supplements the actual two-residual. -/
theorem residual_sup_sylow (hTH : (T : Subgroup G) ≤ H) :
    residual H ⊔ (T : Subgroup G) = H := by
  have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype, residual] using hh

/-- Residual escape is forced by the literal outside-local hypothesis. -/
theorem residual_outside (h : Hypothesis1131At D S U₁ H) :
    ¬ residual H ≤ normalizer (L : Set G) := by
  intro hk
  apply h.outside.1.2
  rw [← residual_sup_sylow h.outside.1.1.2]
  exact sup_le hk D.sylow_normalizes_component

/-- The source Z = Ω₁(Z(T)), in the common ambient group. -/
def sourceZ (T : Sylow 2 G) : Subgroup G := omegaCenterIn (T : Subgroup G)

/-- The source VH is the actual H-conjugate span of Z. -/
def omegaOrbit (T : Sylow 2 G) (H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (sourceZ T) H

omit [Finite G] in
private theorem sourceZ_le : sourceZ T ≤ (T : Subgroup G) := map_subtype_le _

omit [Finite G] in
theorem omegaOrbit_eq_source : omegaOrbit T H = Source.conjugateSpan H (sourceZ T) :=
  conjugateSpanBy_eq_iSup_conj _ _

omit [Finite G] in
theorem omegaOrbit_le (hTH : (T : Subgroup G) ≤ H) : omegaOrbit T H ≤ H :=
  conjugateSpanBy_le_self (sourceZ_le.trans hTH)

omit [Finite G] in
theorem normalizes_omegaOrbit : H ≤ normalizer (omegaOrbit T H : Set G) :=
  le_normalizer_conjugateSpanBy _ _

instance omegaOrbit_relative_normal : ((omegaOrbit T H).subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer normalizes_omegaOrbit

omit [Finite G] in
private theorem intrinsic_omega_image (hTH : (T : Subgroup G) ≤ H) :
    (Stellmacher.omegaOneCenterAmbient (T.subtype hTH : Subgroup H)).map H.subtype =
      sourceZ T := by
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  rfl

omit [Finite G] in
private theorem orbit_intrinsic (hTH : (T : Subgroup G) ≤ H) :
    (normalClosure (Stellmacher.omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)).map
      H.subtype = omegaOrbit T H := by
  let Z := Stellmacher.omegaOneCenterAmbient (T.subtype hTH : Subgroup H)
  let W := normalClosure (Z : Set H)
  have hZ : Z.map H.subtype = sourceZ T := intrinsic_omega_image hTH
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    change W ≤ (omegaOrbit T H).subgroupOf H
    apply normalClosure_le_normal
    intro z hz
    change (z : G) ∈ omegaOrbit T H
    exact le_conjugateSpanBy _ _ (hZ ▸ mem_map_of_mem H.subtype hz)
  · apply conjugateSpanBy_le
    · rw [← hZ]
      exact map_mono le_normalClosure
    · exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le W)).mp
        (by simpa only [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using
          (inferInstance : W.Normal))

/-- B.2.14 on the actual H-orbit, with no module witness assumed. -/
theorem omegaOrbit_reduced (h : Hypothesis1131At D S U₁ H) :
    IsPReduced 2 ((omegaOrbit T H).subgroupOf H) := by
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T) h.outside.1.1)
  have hr := omegaCenter_normalClosure_reduced (T.subtype h.outside.1.1.2) hchar
  rw [← orbit_intrinsic h.outside.1.1.2, subgroupOf,
    comap_map_eq_self_of_injective H.subtype_injective]
  exact hr

/-- The orbit remains elementary abelian in the original ambient group. -/
theorem omegaOrbit_elementary (h : Hypothesis1131At D S U₁ H) :
    IsElementaryAbelian 2 (omegaOrbit T H) := by
  let := (omegaOrbit_reduced h).elementary
  have he := IsElementaryAbelian.map (p := 2) (A := (omegaOrbit T H).subgroupOf H) H.subtype
  rwa [map_subgroupOf_eq_of_le (omegaOrbit_le h.outside.1.1.2)] at he

/-- The omega orbit lies in the original Sylow subgroup. -/
theorem omegaOrbit_le_sylow (h : Hypothesis1131At D S U₁ H) : omegaOrbit T H ≤ T := by
  have hi := map_mono (f := H.subtype) (omegaOrbit_reduced h).le_pCore
  rw [map_subgroupOf_eq_of_le (omegaOrbit_le h.outside.1.1.2)] at hi
  have hq := map_mono (f := H.subtype)
    (pCore_isPGroup.le_sylow_of_normal (T.subtype h.outside.1.1.2))
  change (pCore 2 H).map H.subtype ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hq
  rw [map_subgroupOf_eq_of_le h.outside.1.1.2] at hq
  exact hi.trans hq

/-- The source movement condition gives a nontrivial action on VH. -/
theorem omegaOrbit_not_central (h : Hypothesis1131At D S U₁ H) :
    ¬ H ≤ centralizer (omegaOrbit T H : Set G) := by
  intro hc
  apply h.moves_omega_center
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  have hz : sourceZ T ≤ omegaOrbit T H := le_conjugateSpanBy _ _
  rw [sourceZ, omegaCenterIn_eq_omegaOneAmbient] at hz
  exact hc.trans (centralizer_le hz)

/-- The escaping weak closure makes H a minimal parabolic on its own carrier. -/
theorem outside_minimalParabolic (h : Hypothesis1131At D S U₁ H)
    (hw : ¬ Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    ChapterB.IsMinimalParabolicOver (T.subtype h.outside.1.1.2) ⊤ := by
  have hn : ¬ ((T : Subgroup G).subgroupOf H).Normal := by
    intro hn
    have hTQ : (T : Subgroup G) ≤ H.pCoreIn 2 :=
      le_pCoreIn_of_normalizes T.isPGroup' h.outside.1.1.2
        ((normal_subgroupOf_iff_le_normalizer h.outside.1.1.2).mp hn)
    apply hw
    rw [weakClosureZero_eq_indexed]
    exact (ChapterE.indexedWeakClosure_le _ _ _).trans hTQ
  have hp := Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component h.outside (.inr hn)
  obtain ⟨hTM, hcov, _⟩ := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component h.outside
  exact (ChapterB.intrinsic_minimalParabolic T H _ hp hTM hcov).1

/-- B.6.8 gives the precise centralizer bound needed to select A*. -/
theorem sylow_inf_orbit_centralizer_le_core (h : Hypothesis1131At D S U₁ H)
    (hw : ¬ Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    (T : Subgroup G) ⊓ centralizer (omegaOrbit T H : Set G) ≤ H.pCoreIn 2 := by
  let W := (omegaOrbit T H).subgroupOf H
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let P := T.subtype h.outside.1.1.2
  have hp := outside_minimalParabolic h hw
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply omegaOrbit_not_central h
    intro x hx w hw
    have hc : (⟨x,hx⟩ : H) ∈ C := by
      rw [← QuotientGroup.ker_mk' C, he]
      trivial
    exact congrArg H.subtype (hc ⟨w, omegaOrbit_le h.outside.1.1.2 hw⟩ hw)
  have hC := (ChapterB.minimalParabolic_reduced_image P hp q
    (QuotientGroup.mk'_surjective C) (omegaOrbit_reduced h).quotient_pCore_eq_bot hn).1
  rw [show q.ker = C from QuotientGroup.ker_mk' C] at hC
  have hCQ : (P : Subgroup H) ⊓ C ≤ pCore 2 H := by
    apply (inf_le_inf_left _ hC).trans
    exact (ChapterB.minimalParabolic_sylow_inf_core P hp).le
  intro x hx
  have hxQ : (⟨x,h.outside.1.1.2 hx.1⟩ : H) ∈ pCore 2 H := hCQ ⟨hx.1, by
    intro w hw
    exact Subtype.ext (hx.2 w hw)⟩
  exact mem_map_of_mem H.subtype hxQ

/-- The actual conjugate A = V^g in T acts nontrivially on VH. -/
theorem exists_active_conjugate (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaOrbit T H : Set G) := by
  by_contra hn
  push Not at hn
  apply weakClosure_not_le_core_of_counterexample h p hc
  apply sSup_le
  rintro A ⟨g,rfl,hg⟩
  exact (le_inf hg (hn g hg)).trans (sylow_inf_orbit_centralizer_le_core h
    (weakClosure_not_le_core_of_counterexample h p hc))

/-- The literal source H* = H / C_H(VH). -/
abbrev OrbitQuotient (T : Sylow 2 G) (H : Subgroup G) :=
  H ⧸ centralizer ((omegaOrbit T H).subgroupOf H : Set H)

/-- The original projection, before any group recognition. -/
def orbitProjection (T : Sylow 2 G) (H : Subgroup G) : H →* OrbitQuotient T H :=
  QuotientGroup.mk' _

omit [Finite G] in
private theorem mem_orbit_kernel (hTH : (T : Subgroup G) ≤ H) (x : H) :
    x ∈ (orbitProjection T H).ker ↔ (x : G) ∈ centralizer (omegaOrbit T H : Set G) := by
  rw [orbitProjection, QuotientGroup.ker_mk']
  constructor
  · intro hx u hu
    exact congrArg H.subtype (hx ⟨u, omegaOrbit_le hTH hu⟩ hu)
  · intro hx u hu
    exact Subtype.ext (hx u hu)

theorem exists_orbit_action (h : Hypothesis1131At D S U₁ H) :
    letI := omegaOrbit_elementary h
    ∃ ρ : Representation (ZMod 2) (OrbitQuotient T H) (Additive (omegaOrbit T H)),
      ∀ (x : H) (v : Additive (omegaOrbit T H)),
        ((ρ (orbitProjection T H x) v).toMul : G) = x * v.toMul * (x : G)⁻¹ := by
  let := omegaOrbit_elementary h
  exact Representation.BinaryConjugationSection.exists_action_of_central_kernel H
    (omegaOrbit T H) normalizes_omegaOrbit (orbitProjection T H)
    (QuotientGroup.mk'_surjective _) (fun x hx => (mem_orbit_kernel h.outside.1.1.2 x).mp hx)

/-- The conjugation action on the same original VH, through the literal quotient. -/
def orbitRepresentation (h : Hypothesis1131At D S U₁ H) :
    letI := omegaOrbit_elementary h
    Representation (ZMod 2) (OrbitQuotient T H) (Additive (omegaOrbit T H)) :=
  (exists_orbit_action h).choose

theorem orbitRepresentation_apply (h : Hypothesis1131At D S U₁ H)
    (x : H) (v : Additive (omegaOrbit T H)) :
    ((orbitRepresentation h (orbitProjection T H x) v).toMul : G) =
      x * v.toMul * (x : G)⁻¹ := (exists_orbit_action h).choose_spec x v

/-- The actual image of an ambient actor in H*. -/
def actorImage (T : Sylow 2 G) (H A : Subgroup G) : Subgroup (OrbitQuotient T H) :=
  (A.subgroupOf H).map (orbitProjection T H)

private theorem fixedSpace_actorImage (h : Hypothesis1131At D S U₁ H)
    (A : Subgroup G) (hAH : A ≤ H) (v : Additive (omegaOrbit T H)) :
    letI := omegaOrbit_elementary h
    v ∈ Representation.BinaryOffender.fixedSpace (orbitRepresentation h) (actorImage T H A) ↔
      (v.toMul : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hv a ha
    have he := congrArg (fun w : Additive (omegaOrbit T H) => (w.toMul : G))
      (hv ⟨orbitProjection T H ⟨a,hAH ha⟩, mem_map_of_mem _ ha⟩)
    change ((orbitRepresentation h (orbitProjection T H ⟨a,hAH ha⟩) v).toMul : G) =
      (v.toMul : G) at he
    rw [orbitRepresentation_apply] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hv a
    obtain ⟨x,hx,he⟩ := a.property
    change orbitRepresentation h a.val v = v
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [orbitRepresentation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hv x hx)

omit [Finite G] in
private theorem lift_actor_subgroup {A : Subgroup G} (hAH : A ≤ H)
    (B : Subgroup (OrbitQuotient T H)) (hB : B ≤ actorImage T H A) :
    ∃ C ≤ A, actorImage T H C = B ∧
      ChapterE.subgroupCorank A C = Nat.log 2 (B.relIndex (actorImage T H A)) := by
  let q := orbitProjection T H
  let C₀ := A.subgroupOf H ⊓ B.comap q
  let C := C₀.map H.subtype
  have hCA : C ≤ A := by rintro _ ⟨c,hc,rfl⟩; exact hc.1
  have hCH : C.subgroupOf H = C₀ := comap_map_eq_self_of_injective H.subtype_injective C₀
  have him : C₀.map q = B := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩; exact hx.2
    · intro b hb
      obtain ⟨x,hx,he⟩ := hB hb
      exact ⟨x,⟨hx, (show q x ∈ B from he.symm ▸ hb)⟩,he⟩
  refine ⟨C,hCA,?_,?_⟩
  · change (C.subgroupOf H).map q = B
    rw [hCH,him]
  · unfold ChapterE.subgroupCorank
    congr 1
    rw [← relIndex_subgroupOf (H := C) hAH,hCH]
    exact (inf_relIndex_left (A.subgroupOf H) (B.comap q)).trans
      (relIndex_comap B q (A.subgroupOf H))

/-- E.3.6 gives the source offender family on the literal centralizer quotient.
The image subgroup is A*, not an unrelated abstract elementary group. -/
theorem conjugate_fixedSpaceFamily (h : Hypothesis1131At D S U₁ H)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (g : G) (hg : W.map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ W.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaOrbit T H : Set G)) :
    letI := omegaOrbit_elementary h
    actorImage T H (W.map (MulAut.conj g).toMonoidHom) ∈
      ChapterE.fixedSpaceFamily (orbitRepresentation h) (ChapterE.globalS W).toNat := by
  let := omegaOrbit_elementary h
  let A := W.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ H := hg.trans h.outside.1.1.2
  have hA0 : A ≠ ⊥ := by
    intro he
    apply ha
    change A ≤ _
    rw [he]
    exact bot_le
  have hV0 : W ≠ ⊥ := by intro he; apply hA0; simp [A,he]
  have hs : ((ChapterE.globalS W).toNat : ℕ∞) = ChapterE.globalS W :=
    ENat.natCast_toNat (ChapterE.globalS_ne_top W)
  have hpos : 0 < (ChapterE.globalS W).toNat := by
    have hh := ChapterE.one_le_globalS W hV0
    rw [← hs] at hh
    exact Nat.zero_lt_of_lt (lt_of_lt_of_le (by decide : 0 < 1)
      (ENat.natCast_le_natCast.mp hh))
  have hnon : actorImage T H A ≠ ⊥ := by
    intro he
    apply ha
    intro a ha'
    apply (mem_orbit_kernel h.outside.1.1.2 ⟨a,hAH ha'⟩).mp
    exact mem_bot.mp (he ▸ mem_map_of_mem (orbitProjection T H) ha')
  let := IsElementaryAbelian.subgroupOf (p := 2) hAH
  refine ⟨hpos,⟨hnon,IsElementaryAbelian.map _⟩,?_⟩
  intro B hB hcor
  obtain ⟨C,hCA,hCB,hindex⟩ := lift_actor_subgroup hAH B hB
  have hc : (ChapterE.subgroupCorank A C : ℕ∞) < ChapterE.globalS A := by
    rw [ChapterE.globalS_map_equiv W (MulAut.conj g),← hs,hindex]
    exact_mod_cast hcor
  have hcentral := ChapterE.centralizer_inf_eq_of_corank_lt_globalS hCA hc
    (IsElementaryAbelian.isPGroup 2 (omegaOrbit T H))
  rw [← hCB]
  ext v
  rw [fixedSpace_actorImage h A hAH, fixedSpace_actorImage h C (hCA.trans hAH)]
  have he := congrArg (fun X : Subgroup G => (v.toMul : G) ∈ X) hcentral
  simpa only [mem_inf,v.toMul.property,true_and] using (iff_of_eq he).symm

/-- The original V-conjugate statement, with its public type unchanged. -/
theorem active_conjugate_fixedSpaceFamily (h : Hypothesis1131At D S U₁ H)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaOrbit T H : Set G)) :
    letI := D.elementary
    letI := omegaOrbit_elementary h
    actorImage T H (V.map (MulAut.conj g).toMonoidHom) ∈
      ChapterE.fixedSpaceFamily (orbitRepresentation h) (ChapterE.globalS V).toNat := by
  let := D.elementary
  exact conjugate_fixedSpaceFamily h V g hg ha

/-- The selected source conjugate, together with its actual offender statement. -/
theorem exists_source_offender (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H) :
    letI := D.elementary
    letI := omegaOrbit_elementary h
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      actorImage T H (V.map (MulAut.conj g).toMonoidHom) ∈
        ChapterE.fixedSpaceFamily (orbitRepresentation h) (ChapterE.globalS V).toNat := by
  let := D.elementary
  obtain ⟨g,hg,ha⟩ := exists_active_conjugate h p hc
  exact ⟨g,hg,active_conjugate_fixedSpaceFamily h g hg ha⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
