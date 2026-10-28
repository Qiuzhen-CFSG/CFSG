module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration.CoreCover
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry
public import Theory.Representation.BinaryPermutation.Faithful
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalSource
/-!
# The nonabelian plane-residual core in the original natural setup

The literal A₆ quotient sends the original two-perfect plane actor X to
a conjugate of the genuine plane residual. Its natural action generates
V, and its two-core is nontrivial. Since V lies in T and T normalizes X,
this forces V=[V,X]≤O₂(X). The action kernel of X is a two-group by the
earlier cubic-plane kernel calculation, so O₂(X) maps onto the native
core. If O₂(X) were abelian, it would fix V and faithfulness would kill
that nontrivial image. This contradiction retains the actual X and V.

Only the preceding source plane actor, its cubic action and two-group
kernel are inputs; no core nonabelianness or module-generation conclusion
is assumed. Source: Aschbacher–Smith 13.5.4(6), printed p.916.
-/
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration
namespace CFSG.Quasithin.Chapter13.Section05.AmbientSource
private abbrev nativePlaneResidual := (pResidual 2 AlternatingAction.parabolic).map AlternatingAction.parabolic.subtype
private theorem native_plane_residual_generated :
    subspaceCommutator (alternatingNaturalRepresentation (Fin 6)) ⊤ nativePlaneResidual = ⊤ := by
  have h := generated_image (alternatingCoreRepresentation (Fin 6))
    (alternatingNaturalRepresentation (Fin 6)) (MonoidHom.id _)
    (coreToNatural (Fin 6)) coreToNatural_surjective
    (fun g v => Representation.IntertwiningMap.isIntertwining _ _ (alternatingCoreProjection (Fin 6)) g v)
    nativePlaneResidual core_residual_generated
  simpa only [Subgroup.map_id] using h
private theorem native_plane_residual_core_ne_bot : nativePlaneResidual.pCoreIn 2 ≠ ⊥ := by
  intro he
  have hm := congrArg (fun A : Subgroup (alternatingGroup (Fin 6)) =>
    A.map (alternatingGroup (Fin 6)).subtype) he
  rw [Subgroup.map_bot, map_pCoreIn_of_injective 2 _ _ (alternatingGroup (Fin 6)).subtype_injective] at hm
  have hr : nativePlaneResidual.map (alternatingGroup (Fin 6)).subtype =
      (pResidual 2 Theory.SpecificGroups.SymmetricSix.BinaryFlags.L2).map
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.L2.subtype := by
    unfold nativePlaneResidual
    rw [map_embedded_pResidual]
    have he : AlternatingAction.parabolic.map (alternatingGroup (Fin 6)).subtype =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.L2 := by
      change (Theory.SpecificGroups.SymmetricSix.synthemeStabilizer.subgroupOf
        (alternatingGroup (Fin 6))).map (alternatingGroup (Fin 6)).subtype = _
      rw [subgroupOf_map_subtype]
      rfl
    rw [he]
  rw [hr, Theory.SpecificGroups.SymmetricSix.BinaryFlags.L2_residual_core_eq_D0] at hm
  have hc := Theory.SpecificGroups.SymmetricSix.BinaryFlags.D0_card
  rw [hm, card_bot] at hc
  omega

private theorem native_plane_actor_generated (S : Sylow 2 (alternatingGroup (Fin 6)))
    (A : Subgroup (alternatingGroup (Fin 6))) (hA : IsPPerfect 2 A) (hne : A ≠ ⊥)
    (hn : (S : Subgroup (alternatingGroup (Fin 6))) ≤ normalizer (A : Set (alternatingGroup (Fin 6))))
    (E : Submodule (ZMod 2) (natural (Fin 6))) (hdim : Module.finrank (ZMod 2) E = 2)
    (hE : A ⊔ (S : Subgroup (alternatingGroup (Fin 6))) ≤
      subspaceStabilizer (alternatingNaturalRepresentation (Fin 6)) E) :
    subspaceCommutator (alternatingNaturalRepresentation (Fin 6)) ⊤ A = ⊤ ∧
      A.pCoreIn 2 ≠ ⊥ := by
  obtain ⟨g,rfl⟩ := residual_marking S A hA hne hn E hdim hE
  let ρ := alternatingNaturalRepresentation (Fin 6)
  constructor
  · exact generated_image ρ ρ (MulAut.conj g).toMonoidHom (ρ g)
      (fun v => ⟨ρ g⁻¹ v,ρ.self_inv_apply g v⟩)
      (fun x v => by
        change ρ g (ρ x v) = ρ (g * x * g⁻¹) (ρ g v)
        simp only [map_mul,Module.End.mul_apply]
        rw [ρ.inv_self_apply]) _ native_plane_residual_generated
  · rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    exact fun he => native_plane_residual_core_ne_bot
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp he)


open CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CFSG.Quasithin.Chapter13.Section07.NaturalAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d
private theorem source_sylow_local :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  obtain ⟨R,hR⟩ := (T.subtype d.normalizes_L).exists_subgroupOf_eq_of_normal
    (L.subgroupOf (normalizer (L : Set G)))
  let e := subgroupOfEquivOfLe L.le_normalizer
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (R : Subgroup _).map e.toMonoidHom = _
  rw [hR]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact hy
  · intro hx
    exact ⟨⟨⟨x,L.le_normalizer x.property⟩,x.property⟩,hx,rfl⟩

private theorem source_plane_image (X : Subgroup G) (hXL : X ≤ L)
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : letI := source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G)) :
    let f := d.local_quotient.toMonoidHom.comp ((QuotientGroup.mk' _).comp (inclusion hXL))
    IsPGroup 2 f.ker ∧
      subspaceCommutator (alternatingNaturalRepresentation (Fin 6)) ⊤ f.range = ⊤ ∧
      f.range.pCoreIn 2 ≠ ⊥ := by
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  let f := α.comp (inclusion hXL)
  have hα : Function.Surjective α :=
    d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hf (x : X) (v : V) :
      (d.coordinate (V.normalizerMonoidHom ⟨x.val,d.normalizes_V (mem_sup_left (hXL x.property))⟩ v)).toAdd =
        alternatingNaturalRepresentation (Fin 6) (f x) (d.coordinate v).toAdd :=
    d.conjugation (inclusion hXL x) v
  have hker : IsPGroup 2 f.ker := by
    apply hkX.comap_subtype.to_le
    intro x hx
    refine ⟨x.property,?_⟩
    apply mem_centralizer_iff.mpr
    intro e he
    have hh := hf x ⟨e,d.plane_le_seed.trans d.seed_le he⟩
    rw [show f x = 1 from hx,map_one,Module.End.one_apply] at hh
    have hh' := congrArg Subtype.val (d.coordinate.injective hh)
    change x.val * e * x.val⁻¹ = e at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have hrange : f.range = (X.subgroupOf L).map α := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨inclusion hXL x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
  have hne : f.range ≠ ⊥ := by
    intro hb
    have he : f.ker = ⊤ := by
      apply top_unique
      intro x _
      exact mem_bot.mp (hb ▸ (show f x ∈ f.range from ⟨x,rfl⟩))
    have hXp : IsPGroup 2 X := (he ▸ hker).of_equiv topEquiv
    have heX : X = ⊥ := by
      apply bot_unique
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun
        (hX.hom_eq_one_of_isPGroup hXp (MonoidHom.id X)) ⟨x,hx⟩)
    have hh := hx
    rw [heX] at hh
    simp at hh
  obtain ⟨S,hS⟩ := source_sylow_local d
  let Sbar := S.mapSurjective hα
  have hn : (Sbar : Subgroup (alternatingGroup (Fin 6))) ≤
      normalizer (f.range : Set (alternatingGroup (Fin 6))) := by
    rw [hrange]
    apply (map_mono (f := α) ?_).trans (le_normalizer_map α)
    apply le_normalizer_iff.mpr
    intro s hs x hx
    exact le_normalizer_iff.mp hTX s.val (show s ∈ (T : Subgroup G).subgroupOf L from hS ▸ hs) x.val hx
  have hp : IsPPerfect 2 f.range := hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hsE : f.range ⊔ (Sbar : Subgroup (alternatingGroup (Fin 6))) ≤
      subspaceStabilizer (alternatingNaturalRepresentation (Fin 6)) (image d E) := by
    apply sup_le
    · apply le_subspaceStabilizer
      rintro a ⟨x,rfl⟩ w ⟨v,hv,rfl⟩
      refine ⟨V.normalizerMonoidHom ⟨x.val,d.normalizes_V (mem_sup_left (hXL x.property))⟩ v,
        le_normalizer_iff.mp hXN x.val x.property v.val hv,hf x v⟩
    · apply le_subspaceStabilizer
      rintro a ⟨s,hs,rfl⟩ w ⟨v,hv,rfl⟩
      refine ⟨V.normalizerMonoidHom ⟨s.val,d.normalizes_V (mem_sup_left s.property)⟩ v,
        le_normalizer_iff.mp d.plane_stable s.val (show s ∈ (T : Subgroup G).subgroupOf L from hS ▸ hs) v.val hv,d.conjugation s v⟩
  exact ⟨hker,native_plane_actor_generated Sbar f.range hp hne hn (image d E)
    (image_dim d E (d.plane_le_seed.trans d.seed_le) 2 d.plane_card) hsE⟩


/-- Source 13.5.4(6), with commutator generation and the original module inside the same core. -/
theorem source_plane_residual_core_nonabelian (X : Subgroup G) (hXL : X ≤ L)
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : letI := source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G)) :
    ⁅V,X⁆ = V ∧ V ≤ X.pCoreIn 2 ∧ ¬ IsMulCommutative (X.pCoreIn 2) := by
  let := elementary d
  let f := d.local_quotient.toMonoidHom.comp ((QuotientGroup.mk' _).comp (inclusion hXL))
  obtain ⟨hker,hgen,hcore⟩ := source_plane_image d X hXL hXN hTX hX hx hkX
  have hf (x : X) (v : V) :
      (d.coordinate (V.normalizerMonoidHom ⟨x.val,d.normalizes_V (mem_sup_left (hXL x.property))⟩ v)).toAdd =
        alternatingNaturalRepresentation (Fin 6) (f x) (d.coordinate v).toAdd :=
    d.conjugation (inclusion hXL x) v
  have hXV := hXL.trans (le_sup_left.trans d.normalizes_V)
  have hCV : ⁅V,X⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hXV
  have hspan : subspaceCommutator (alternatingNaturalRepresentation (Fin 6)) ⊤ f.range ≤
      image d ⁅V,X⁆ := by
    apply Submodule.span_le.mpr
    rintro w ⟨a,⟨x,rfl⟩,w,_,rfl⟩
    obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    let c : V := V.normalizerMonoidHom
      ⟨x.val,d.normalizes_V (mem_sup_left (hXL x.property))⟩ v * v⁻¹
    refine ⟨c,?_,?_⟩
    · change x.val * v.val * x.val⁻¹ * v.val⁻¹ ∈ ⁅V,X⁆
      rw [commutator_comm V X]
      exact commutator_mem_commutator x.property v.property
    · change (d.coordinate c).toAdd = alternatingNaturalRepresentation (Fin 6) (f x) w - w
      change (d.coordinate (_ * _)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul,toAdd_inv,← sub_eq_add_neg]
      rw [hf,hv]
      rfl
  have hcomm : ⁅V,X⁆ = V := by
    apply le_antisymm hCV
    intro v hv
    obtain ⟨c,hc,hcv⟩ := hspan (hgen.symm ▸ (Submodule.mem_top :
      (d.coordinate ⟨v,hv⟩).toAdd ∈ (⊤ : Submodule (ZMod 2) (natural (Fin 6)))))
    have he : c = ⟨v,hv⟩ := d.coordinate.injective hcv
    have he' : c.val = v := congrArg Subtype.val he
    exact he' ▸ (show c.val ∈ ⁅V,X⁆ from hc)
  have hVX : V ≤ X := by
    rw [← hcomm]
    exact le_normalizer_iff_commutator_le_right.mp (d.chosen.le_sylow.trans hTX)
  have hVcore : V ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 V) hVX hXV
  refine ⟨hcomm,hVcore,?_⟩
  intro hab
  have hcV : X.pCoreIn 2 ≤ centralizer (V : Set G) := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp
      (commutator_self_eq_bot_iff.mpr hab)
    exact hh.trans (centralizer_le hVcore)
  have hmapbot : (pCore 2 X).map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    apply Subtype.ext
    apply naturalRepresentation_injective (Fin 6) (by decide)
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have he := hf x v
    have hxC : x.val ∈ centralizer (V : Set G) := hcV (mem_map_of_mem X.subtype hx)
    have hev : V.normalizerMonoidHom
        ⟨x.val,d.normalizes_V (mem_sup_left (hXL x.property))⟩ v = v := by
      apply Subtype.ext
      change x.val * v.val * x.val⁻¹ = v.val
      rw [← mem_centralizer_iff.mp hxC v.val v.property,mul_inv_cancel_right]
    rw [hev,hv] at he
    change alternatingNaturalRepresentation (Fin 6) (f x) w =
      alternatingNaturalRepresentation (Fin 6) 1 w
    rw [map_one,Module.End.one_apply]
    exact he.symm
  have hk : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have he := f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hk
  have hmap : (pCore 2 X).map f.rangeRestrict = pCore 2 f.range := by
    rw [← he,map_comap_eq_self_of_surjective f.rangeRestrict_surjective]
  have hm := congrArg (fun A : Subgroup f.range => A.map f.range.subtype) hmap
  rw [map_map] at hm
  exact hcore (hm.symm.trans hmapbot)


/-- The same nonabelianness stated for the intrinsic O₂(X), as used in 13.5.6. -/
theorem source_plane_intrinsic_core_nonabelian (X : Subgroup G) (hXL : X ≤ L)
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : letI := source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G)) :
    ¬ IsMulCommutative (pCore 2 X) := by
  intro ha
  let := ha
  exact (source_plane_residual_core_nonabelian d X hXL hXN hTX hX hx hkX).2.2
    (inferInstanceAs (IsMulCommutative ((pCore 2 X).map X.subtype)))

end CFSG.Quasithin.Chapter13.Section05.AmbientSource
