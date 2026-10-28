module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Configurations
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.Linear
public import Theory.SpecificGroups.SymplecticFour.Binary.DerivedFlagGeometry

/-!
# Compatible coordinates for the A₆ block and its original V₂-plane

The actual alternating-block representation identifies U(L)/C_U(L)(L) with
its natural binary module. Map the original V₂ through this full central
quotient. Its Y₊-fixed subgroup is trivial, so the map is injective on V₂ and
its image has dimension two. No central summand is removed or split off.

The small parabolic marking gives the image of M ∩ L order 24. Its Sylow
two-subgroup is therefore Sylow in A₆. Conjugate the actor isomorphism and
coefficient coordinates together so this parabolic contains the canonical
alternating flag group T₀. The transported V₂ is T₀-invariant, hence is the
canonical plane. The parabolic lies in its stabilizer, also of order 24,
which proves the required equality with the original quotient map.

This constructs the alternating alternative of `MarkedModels` from the
source inputs, with no coordinate, placement or stabilizer premise. The
five-case assembly and remaining core-centralization argument belong to
the parent tasks.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.31, printed p.1132 (PDF p.1149), using C.1.7, C.1.12, C.1.30–34
and B.5.3–6. The Sylow alignment follows the checked conjugacy argument in
`SymmetricSix.BinaryFlags.NaturalHyperplanes`; the matrix parabolic order
uses `SymplecticFour.Binary.DerivedFlagGeometry`.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover CentralCover.BlockModels
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly
namespace AlternatingCoordinates
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {L E : Subgroup G} {ρ : Representation (ZMod 2) A V}

/-- Restrict the full central quotient coordinates to the original subgroup. -/
noncomputable def planeMap (m : CenterModel L ρ) (hE : E ≤ coreCenter L) :
    E →* Multiplicative V := m.coordinates.comp (inclusion hE)

/-- The actual image subspace; no choice of a complement is made. -/
noncomputable def quotientPlane (m : CenterModel L ρ) (hE : E ≤ coreCenter L) :
    Submodule (ZMod 2) V :=
  AddSubgroup.toZModSubmodule 2 (planeMap m hE).range.toAddSubgroup'

/-- Membership retains an original subgroup element as its witness. -/
theorem mem_quotientPlane (m : CenterModel L ρ) (hE : E ≤ coreCenter L) (v : V) :
    v ∈ quotientPlane m hE ↔ ∃ z : E, planeMap m hE z = Multiplicative.ofAdd v := Iff.rfl

/-- A moving subgroup meets the central kernel trivially. -/
theorem planeMap_injective (m : CenterModel L ρ) (hE : E ≤ coreCenter L)
    {Y : Subgroup G} (hYL : Y ≤ L) (hf : E ⊓ centralizer (Y : Set G) = ⊥) :
    Function.Injective (planeMap m hE) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply _root_.eq_bot_iff.mpr
  intro z hz
  have hc : (z : G) ∈ centralizer (L : Set G) :=
    (m.coordinates_eq_one_iff (inclusion hE z)).mp hz
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp
    (hf ▸ And.intro z.property (centralizer_le hYL hc))))

/-- Injective quotient coordinates preserve the original subgroup order. -/
theorem quotientPlane_card (m : CenterModel L ρ) (hE : E ≤ coreCenter L)
    (hi : Function.Injective (planeMap m hE)) :
    Nat.card (quotientPlane m hE) = Nat.card E := by
  let e : E ≃* (planeMap m hE).range := MonoidHom.ofInjective hi
  exact (Nat.card_congr e.toEquiv).symm

/-- Every original normalizer element stabilizes the quotient image. -/
theorem quotientPlane_stable (m : CenterModel L ρ) (hE : E ≤ coreCenter L)
    (l : L) (hl : (l : G) ∈ normalizer (E : Set G)) :
    m.actorMap l ∈ BlockModels.planeStabilizer ρ (quotientPlane m hE) := by
  apply (mem_planeStabilizer_iff_map _ _ _).mpr
  have forward (l : L) (hl : (l : G) ∈ normalizer (E : Set G)) :
      (quotientPlane m hE).map (ρ (m.actorMap l)) ≤ quotientPlane m hE := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨z, hz⟩ := (mem_quotientPlane m hE v).mp hv
    let w : E := ⟨l * (z : G) * (l : G)⁻¹, (mem_normalizer_iff.mp hl _).mp z.property⟩
    apply (mem_quotientPlane m hE _).mpr
    refine ⟨w, ?_⟩
    change m.coordinates (centerConjugate L l (inclusion hE z)) = _
    rw [m.coordinates_conjugate]
    change Multiplicative.ofAdd (ρ (m.actorMap l) (planeMap m hE z).toAdd) = _
    rw [hz]
    rfl
  have hi := Submodule.map_mono (f := ρ (m.actorMap l))
    (forward l⁻¹ ((normalizer (E : Set G)).inv_mem hl))
  rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
    ← map_mul, mul_inv_cancel, map_one, map_one,
    Module.End.one_eq_id, Submodule.map_id] at hi
  exact le_antisymm (forward l hl) hi

/-- These coordinates use exactly the block fixed quotient, including its full kernel. -/
theorem planeMap_block_quotient (h : ChapterC.IsShort L)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction ρ))
    (hE : E ≤ coreCenter L) (z : E) :
    planeMap (centerModel h ρ m) hE z =
      m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L)
        ((blockCenterEquiv h).symm (inclusion hE z))) := by
  change m.moduleIso ((blockCenterQuotientEquiv h).symm
    (QuotientGroup.mk' (centerKernel L) (inclusion hE z))) = _
  conv_lhs => rw [← (blockCenterEquiv h).apply_symm_apply (inclusion hE z)]
  rw [← blockCenterQuotientEquiv_mk, MulEquiv.symm_apply_apply]

/-- Replace the action notation in C.1.12 by the identical multiplicative action. -/
noncomputable def blockModel (h : ChapterC.IsLinearBlockModel L ρ) :
    ChapterC.BlockModuleModel L (multiplicativeAction ρ) := Classical.choice (by
  obtain ⟨r, ⟨m⟩, hr⟩ := h
  have he : r = multiplicativeAction ρ := by
    ext a v
    exact congrArg Multiplicative.ofAdd (hr a v)
  exact ⟨he ▸ m⟩)

/-- Change actor and coefficient coordinates simultaneously, preserving equivariance. -/
noncomputable def conjugateModel
    (m : ChapterC.BlockModuleModel L (multiplicativeAction ρ)) (a : A) :
    ChapterC.BlockModuleModel L (multiplicativeAction ρ) where
  quotientIso := m.quotientIso.trans (MulAut.conj a)
  moduleIso := m.moduleIso.trans (multiplicativeAction ρ a)
  intertwining l u := by
    change multiplicativeAction ρ a (m.moduleIso _) = _
    rw [m.intertwining]
    change (multiplicativeAction ρ a * multiplicativeAction ρ
      (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l))) _ =
      (multiplicativeAction ρ (a * m.quotientIso (QuotientGroup.mk' (pCore 2 L) l) * a⁻¹) *
        multiplicativeAction ρ a) _
    rw [← map_mul, ← map_mul]
    congr 2
    group


open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

private def coordinateSwap : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5

private theorem map_flag_borel :
    (H1 ⊓ H2).map (MulAut.conj coordinateSwap).toMonoidHom = Theory.SpecificGroups.SymmetricSix.borel := by
  have hp : coordinateSwap • pair 4 5 = pair 0 1 := by decide
  have hs : coordinateSwap • baseSyntheme = baseSyntheme := by decide
  rw [Subgroup.map_inf _ _ _ (MulAut.conj coordinateSwap).injective]
  change (MulAction.stabilizer S (pair 4 5)).map _ ⊓
    (MulAction.stabilizer S baseSyntheme).map _ = Theory.SpecificGroups.SymmetricSix.borel
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hp, hs]
  rfl

private theorem T0_isPGroup : IsPGroup 2 T0 := by
  have hb : IsPGroup 2 Theory.SpecificGroups.SymmetricSix.borel := borelSylow.isPGroup'
  have hm : (H1 ⊓ H2) ≤ Theory.SpecificGroups.SymmetricSix.borel.comap (MulAut.conj coordinateSwap).toMonoidHom := by
    exact Subgroup.map_le_iff_le_comap.mp map_flag_borel.le
  exact (hb.comap_of_injective _ (MulAut.conj coordinateSwap).injective).to_le
    (inf_le_left.trans hm)

/-- An order-24 subgroup of A₆ admits coordinates containing the canonical flag group. -/
theorem conjugate_contains_T0 (P : Subgroup Alternating.Actor) (hc : Nat.card P = 24) :
    ∃ a : Alternating.Actor,
      T0.subgroupOf (alternatingGroup (Fin 6)) ≤ P.map (MulAut.conj a).toMonoidHom := by
  have hcard : Nat.card Alternating.Actor = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hidx : P.index = 15 := by
    have h := P.card_mul_index
    rw [hc, hcard] at h
    omega
  let R : Sylow 2 P := Classical.choice inferInstance
  let Q : Sylow 2 Alternating.Actor := (R.isPGroup'.map P.subtype).toSylow (by
    rw [index_map_subtype, hidx]
    exact Nat.Prime.not_dvd_mul Nat.prime_two R.not_dvd_index (by decide))
  obtain ⟨T, hT⟩ := (T0_isPGroup.comap_subtype (K := alternatingGroup (Fin 6))).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Alternating.Actor T Q
  have hQ : (T : Subgroup Alternating.Actor).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg (fun U : Sylow 2 Alternating.Actor => (U : Subgroup Alternating.Actor)) hg
  refine ⟨g⁻¹, ?_⟩
  intro t ht
  have htQ : g * t * g⁻¹ ∈ (Q : Subgroup Alternating.Actor) := by
    rw [← hQ]
    exact mem_map_of_mem _ (hT ht)
  have htP : g * t * g⁻¹ ∈ P := map_subtype_le (R : Subgroup P) htQ
  refine ⟨g * t * g⁻¹, htP, ?_⟩
  change g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t
  group

/-- The actual natural plane stabilizer is the order-24 syntheme stabilizer. -/
theorem canonical_stabilizer_card :
    Nat.card (BlockModels.planeStabilizer Alternating.action canonicalPlane) = 24 := by
  have he : BlockModels.planeStabilizer Alternating.action canonicalPlane =
      a6SynthemeStabilizer := by
    ext a
    exact (mem_planeStabilizer_iff_map _ _ _).trans (canonicalPlane_stabilizer a.val)
  rw [he]
  exact a6SynthemeStabilizer_order


variable [Finite G] {κ : GroupClass} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- Only the derived symplectic small marking has component order 360.
Its literal parabolics have order 24 under the same quotient map. -/
private theorem source_parabolic_card (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (m : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) :
    Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map
      (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))) = 24 := by
  obtain ⟨q, hq⟩ := ms.quotient
  let f := q.symm.trans m.quotientIso
  have ha : m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)) =
      f.toMonoidHom.comp (componentMap d c) := by
    apply MonoidHom.ext
    intro l
    change m.quotientIso (QuotientGroup.mk' (pCore 2 c.L) l) =
      m.quotientIso (q.symm (componentMap d c l))
    rw [← hq, q.symm_apply_apply]
  rw [ha, ← map_map, componentMap_parabolic_image, card_map_of_injective f.injective]
  have hc : Nat.card (d.starImage I c.L) = 360 := by
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup]
    norm_num
  cases hm with
  | linearThree m =>
    have hh := (Nat.card_congr m.equiv.toEquiv).trans Matrix.PSL3Two.card_SL
    omega
  | symplecticDerived m =>
    have hh := Theory.SpecificGroups.SymplecticFour.Binary.card_derivedParabolic m.node
    change Nat.card (Parabolics.symplecticDerivedParabolic m.node) = 24 at hh
    rw [← m.intersection, card_map_of_injective m.equiv.injective] at hh
    exact hh
  | g2Derived m =>
    have ho : Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
      rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.card_H
    have hh := (Nat.card_congr m.equiv.toEquiv).trans ho
    omega

/-- Construct simultaneous coordinates, retaining injectivity and the literal
quotient image of the original V₂. The central fixed subgroup remains intact. -/
theorem source_coordinates (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (h : ChapterC.IsAlternatingBlock c.L 6) :
    ∃ m : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action),
      let cm := centerModel h.2.1 Alternating.action m
      let W := quotientPlane cm s.plane_le_coreCenter
      Function.Injective (planeMap cm s.plane_le_coreCenter) ∧
      Module.finrank (ZMod 2) W = 2 ∧
      (∀ g ∈ T0, W.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = W) ∧
      ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap =
        BlockModels.planeStabilizer Alternating.action W := by
  let m := blockModel h.2.2
  let P := ((d.M ⊓ c.L).subgroupOf c.L).map
    (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))
  obtain ⟨a, ha⟩ := conjugate_contains_T0 P (source_parabolic_card s hm ms m)
  let m' := conjugateModel m a
  let cm := centerModel h.2.1 Alternating.action m'
  let W := quotientPlane cm s.plane_le_coreCenter
  have he : ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap =
      P.map (MulAut.conj a).toMonoidHom := by
    rw [map_map]
    rfl
  have hs : ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap ≤
      BlockModels.planeStabilizer Alternating.action W := by
    rintro _ ⟨l, hl, rfl⟩
    apply quotientPlane_stable cm s.plane_le_coreCenter
    have hh : (l : G) ∈ c.L ⊓ normalizer (d.V₂ : Set G) := s.component_parabolic ▸ hl
    exact hh.2
  have hi : Function.Injective (planeMap cm s.plane_le_coreCenter) :=
    planeMap_injective cm s.plane_le_coreCenter s.contains (s.line.plane_fixed_trivial d)
  have hd : Module.finrank (ZMod 2) W = 2 :=
    plane_dimension W ((quotientPlane_card cm s.plane_le_coreCenter hi).trans
      (d.action.card_plane _))
  have ht : ∀ g ∈ T0, W.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = W := by
    intro g hg
    let t : Alternating.Actor := ⟨g, hg.2⟩
    have hm : t ∈ ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap := by
      rw [he]
      exact ha hg
    exact (mem_planeStabilizer_iff_map _ _ t).mp (hs hm)
  refine ⟨m', hi, hd, ht, eq_of_le_of_card_ge hs ?_⟩
  change Nat.card (BlockModels.planeStabilizer Alternating.action W) ≤
    Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap)
  rw [canonicalPlane_unique W hd ht, canonical_stabilizer_card]
  exact (source_parabolic_card s hm ms m').ge

end AlternatingCoordinates

open AlternatingCoordinates

/-- The actual alternating source branch supplies its marked extension model.
All coordinates and the parabolic equality are derived from the source inputs. -/
theorem alternating_marked_models {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData κ d c) (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (_hb : ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)))
    (h : ChapterC.IsAlternatingBlock c.L 6) :
    MarkedModels c.L d.V₂ (d.M ⊓ c.L) := by
  obtain ⟨m, hi, hd, ht, hp⟩ := source_coordinates s hm ms h
  exact .alternating h.2.1 m _ hd ht hp

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly

end
