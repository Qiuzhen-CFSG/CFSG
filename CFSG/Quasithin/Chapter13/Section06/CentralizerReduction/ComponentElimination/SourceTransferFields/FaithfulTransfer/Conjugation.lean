module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.TwoCore

/-!
# Faithful local components under the specified conjugation

The embedded two-core, its omega-center, and its commutator all transport
through automorphisms. Consequently the actual faithful local family
transports with its Sylow subgroup. Pulling a component back and using
the induced isomorphism of its two-core quotient transports the universal
A₅ choice clause to every replacement component.

Here conjugation is literally `MulAut.conj g`, so a = g z g⁻¹ and the
Sylow subgroup is the image under that same homomorphism. The seed remains
a nonidentity element of its omega-center.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Hypothesis 13.3.1(4) and the final paragraph of 13.6.17, pp.884, 930–931.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ChapterA.Section04 Chapter1.Section02.Adequate ComponentSelection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The intrinsic module commutes with ambient automorphisms. -/
theorem intrinsic_module_map (X : Subgroup G) (e : MulAut G) :
    (intrinsicSignalizerModule X).map e.toMonoidHom =
      intrinsicSignalizerModule (X.map e.toMonoidHom) := by
  unfold intrinsicSignalizerModule
  rw [signalizerModule_eq_commutator_omegaCenter,
    signalizerModule_eq_commutator_omegaCenter, map_commutator,
    ← omegaOneCenterAmbient_map_injective _ e.injective]
  change ⁅X.map e.toMonoidHom, omegaOneCenterAmbient ((X.pCoreIn 2).map e.toMonoidHom)⁆ =
    ⁅X.map e.toMonoidHom, omegaOneCenterAmbient ((X.map e.toMonoidHom).pCoreIn 2)⁆
  rw [map_pCoreIn_of_injective 2 X e.toMonoidHom e.injective]

/-- Transport of the literal faithful family with its Sylow subgroup. -/
theorem faithful_map_iff (hE : IsEvenCharacteristic G) (T : Sylow 2 G)
    (e : MulAut G) (X : Subgroup G) :
    X.map e.toMonoidHom ∈ MainForward.faithfulLocalComponents
      (T.mapSurjective (f := e.toMonoidHom) e.surjective) ↔ X ∈ MainForward.faithfulLocalComponents T := by
  have hT := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T
  rw [mem_faithfulLocalComponents_iff_module _ (hE _),
    mem_faithfulLocalComponents_iff_module _ (hE _), hT,
    Chapter1.mem_L_map_iff e.toMonoidHom e.injective, ← intrinsic_module_map]
  exact and_congr Iff.rfl (not_congr
    ((intrinsicSignalizerModule X).map_eq_bot_iff_of_injective
      (f := e.toMonoidHom) e.injective))

/-- Transport Hypothesis 13.3.1(4), including its universal quantifier
and the actual two-core quotients, to any replacement choice. -/
theorem uniformA5Choice_map_replacement (hE : IsEvenCharacteristic G)
    (T : Sylow 2 G) (L X : Subgroup G) (e : MulAut G)
    (hchoice : UniformA5Choice T L)
    (hL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    UniformA5Choice (T.mapSurjective (f := e.toMonoidHom) e.surjective) X := by
  intro _ J hJ
  let B := J.map e.symm.toMonoidHom
  have he : B.map e.toMonoidHom = J := by simp [B, map_map]
  have hB : B ∈ MainForward.faithfulLocalComponents T :=
    (faithful_map_iff hE T e B).mp (he.symm ▸ hJ)
  obtain ⟨f⟩ := hchoice hL B hB
  let b : B ≃* J := (B.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he)
  exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans f⟩

/-- The same conjugation sends the central seed and the Sylow subgroup. -/
theorem conjugate_seed_mem_omegaCenter (T : Sylow 2 G) (g z : G)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    MulAut.conj g z ∈ omegaOneCenterAmbient
      ((T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective : Sylow 2 G) : Subgroup G) := by
  rw [Sylow.coe_mapSurjective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).surjective T,
    omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective]
  exact mem_map_of_mem _ hz

omit [Finite G] in
/-- Conjugation preserves the seed's nonidentity. -/
theorem conjugate_seed_ne_one (g z : G) (hz : z ≠ 1) : MulAut.conj g z ≠ 1 :=
  fun he => hz ((MulAut.conj g).injective (he.trans (map_one _).symm))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields

end
