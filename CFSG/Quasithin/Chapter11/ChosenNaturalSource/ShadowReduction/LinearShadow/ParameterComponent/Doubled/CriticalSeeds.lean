module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.CriticalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# The critical action on the original chosen constituents

The A_{2n} image of a noncommuting doubled conjugate lies in the action
induced by L. Equality of the original automorphisms therefore makes this
conjugate preserve V itself. The same quotient marking shows that C_L(V)
and C_L(V_M) agree. Transporting these kernels in both directions proves
that the original seeds V and V^g already fail to commute.

The final consumer supplies these conclusions for the literal F.7.11 pair
in T. The common-field-line identification and its normalizer exclusion
remain to be proved; no weak-closure escape or parameter upper bound is
asserted here.

Source: Aschbacher--Smith, 11.3.6, printed p.772, second paragraph.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open CFSG.Quasithin.ChapterE
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace CriticalAction
variable {G : Type*} [Group G] [Finite G]

private theorem normalizes_of_inducedAutomizer_le {W A J U : Subgroup G}
    (hA : A ≤ normalizer (W : Set G)) (hU : U ≤ W)
    (hJ : J ≤ normalizer (U : Set G))
    (hI : inducedAutomizer W A ≤ inducedAutomizer W J) :
    A ≤ normalizer (U : Set G) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨u,hu,rfl⟩
    let aN : normalizer (W : Set G) := ⟨a,hA ha⟩
    have hi : W.normalizerMonoidHom.rangeRestrict aN ∈ inducedAutomizer W J :=
      hI (mem_map_of_mem _ ha)
    obtain ⟨j,hj,he⟩ := hi
    have heval := congrArg (fun f : Automizer W => (f.val ⟨u,hU hu⟩ : G)) he
    change (j:G)*u*(j:G)⁻¹ = a*u*a⁻¹ at heval
    change a*u*a⁻¹ ∈ U
    rw [←heval]
    exact (mem_normalizer_iff.mp (hJ hj) u).mp hu
  · rw [card_map_of_injective (MulAut.conj a).injective]

variable {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The actual E.3.10 image belongs to A_{2n}. -/
theorem conjugate_family (d : Coordinates D S) (g : G)
    (hn : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (fullModule L V : Set G))
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    letI := fullModule_elementary d
    inducedAutomizer (fullModule L V) ((fullModule L V).map (MulAut.conj g).toMonoidHom) ∈
      fixedSpaceFamily (automizerRepresentation (fullModule L V)) (2*S.field.degree) := by
  let := fullModule_elementary d
  have hs := LocalMinimum.globalS_eq d
  have hz : subgroupCorank ((fullModule L V).map (MulAut.conj g).toMonoidHom)
      ((fullModule L V).map (MulAut.conj g).toMonoidHom) = 0 := by
    simp only [subgroupCorank,relIndex_self]
    decide
  have hf := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (le_inf le_rfl hn) (by rw [hz,hs]; exact_mod_cast (by have := S.field.degree_pos; omega : 0 < 2*S.field.degree)) hne).2
  simpa only [hz,Nat.sub_zero,hs,ENat.toNat_mul,ENat.toNat_ofNat,ENat.toNat_natCast] using hf

/-- The conjugate's actual automizer is contained in that induced by L. -/
theorem conjugate_inducedAutomizer_le (d : Coordinates D S) (g : G)
    (hn : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (fullModule L V : Set G))
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    inducedAutomizer (fullModule L V) ((fullModule L V).map (MulAut.conj g).toMonoidHom) ≤
      inducedAutomizer (fullModule L V) L := by
  let := fullModule_elementary d
  obtain ⟨E,f,hfi,hE,hN,_,hL⟩ := LocalMinimum.automizer_marking_component d
  have hf := fixedSpaceFamily_map_of_equivariant
    (automizerRepresentation (fullModule L V)) (action S.field.Carrier) f hfi E hE
    (conjugate_family d g hn hne)
  have hinner := FixedFamily.family_le_component S.field.card_eq
    (by have := S.field.degree_pos; omega : 2 ≤ 2*S.field.degree)
    (by have := S.field.degree_pos; omega : S.field.degree < 2*S.field.degree) hf
    (by rintro _ ⟨a,ha,rfl⟩; exact hN ⟨a,rfl⟩)
  intro a ha
  have hm := hinner (mem_map_of_mem f ha)
  rw [←hL] at hm
  obtain ⟨b,hb,he⟩ := hm
  exact hfi he ▸ hb

/-- Natural placement preserves the original chosen constituent, without
replacing it by an arbitrary summand in shear coordinates. -/
theorem conjugate_normalizes_seed (d : Coordinates D S) (g : G)
    (hn : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (fullModule L V : Set G))
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) :=
  normalizes_of_inducedAutomizer_le hn seed_le_fullModule D.normalizes
    (conjugate_inducedAutomizer_le d g hn hne)

/-- Both original natural constituents are normalized by the opposite doubled
module. The assertion uses the same ambient conjugation on the seed and full module. -/
theorem pair_normalizes_seeds (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fullModule L V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hn := le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)
  refine ⟨conjugate_normalizes_seed d g hn hne,?_⟩
  have hcancel : ((fullModule L V).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = fullModule L V := by
    rw [offender_map_conj_map]
    simp only [inv_mul_cancel]
    have he : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext; simp
    rw [he,map_id]
  have hcancel' : ((fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = fullModule L V := by
    rw [offender_map_conj_map]
    simp only [mul_inv_cancel]
    have he : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext; simp
    rw [he,map_id]
  have hn' : (fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (fullModule L V : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hcomm.trans inf_le_right)
    rw [map_commutator,hcancel,commutator_comm] at hh
    exact hh
  have hne' : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) hz
    rw [map_commutator,hcancel',Subgroup.map_bot,commutator_comm] at hh
    exact hne hh
  have hh := (map_mono (f := (MulAut.conj g).toMonoidHom)
    (conjugate_normalizes_seed d g⁻¹ hn' hne')).trans (V.le_normalizer_map _)
  rwa [hcancel'] at hh

/-- The commutator of the original seeds lies in their actual intersection. -/
theorem seed_commutator_le_intersection (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨h₁,h₂⟩ := pair_normalizes_seeds d g hne hcomm
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp ((map_mono seed_le_fullModule).trans h₁))
    (le_normalizer_iff_commutator_le_right.mp (seed_le_fullModule.trans h₂))

/-- The chosen natural constituent and the full doubled module have the same
kernel on the original component L. -/
theorem component_seed_centralizer (d : Coordinates D S) :
    L ⊓ centralizer (V : Set G) = L ⊓ centralizer (fullModule L V : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le seed_le_fullModule))
  rintro l ⟨hl,hc⟩
  refine ⟨hl,?_⟩
  obtain ⟨m,⟨c⟩⟩ := d
  let q : L →* Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier :=
    m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let π : V →* Multiplicative (Fin 3 → S.field.Carrier) :=
    (LocalGeometry.Coordinates.sl3 m).projection
  have hq : q ⟨l,hl⟩ = 1 := by
    apply specialLinearNatural_injective 3
    rw [map_one]
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ : ∃ v : V, π v = Multiplicative.ofAdd w :=
      (LocalGeometry.Coordinates.sl3 m).projection_surjective (Multiplicative.ofAdd w)
    have he : (π (V.normalizerMonoidHom (inclusion D.normalizes ⟨l,hl⟩) v)).toAdd =
        specialLinearNatural 3 (q ⟨l,hl⟩) (π v).toAdd :=
      (LocalGeometry.Coordinates.sl3 m).projection_component_conjugation ⟨l,hl⟩ v
    have hfix : V.normalizerMonoidHom (inclusion D.normalizes ⟨l,hl⟩) v = v := by
      apply Subtype.ext
      change l*(v:G)*l⁻¹=(v:G)
      rw [← hc v v.property,mul_inv_cancel_right]
    rw [hfix,hv] at he
    exact he.symm
  have hi : Function.Injective c.coordinates := by
    apply c.coordinates.ker_eq_bot_iff.mp
    rw [c.kernel_eq,bot_subgroupOf]
  intro w hw
  change w ∈ Source.conjugateSpan (normalizer (L : Set G)) V at hw
  have he := c.equivariant ⟨l,hl⟩ ⟨w,hw⟩
  change _ = SL3DoubledNaturalOffenders.representation S.field.Carrier
    (q ⟨l,hl⟩) (c.coordinates ⟨w,hw⟩).toAdd at he
  rw [hq,map_one,Module.End.one_apply] at he
  have hh := congrArg Subtype.val (hi (Multiplicative.toAdd.injective he))
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Natural placement makes the kernel on the original seed equal the
kernel on the full module, for every subgroup of the same action image. -/
theorem seed_centralizer_of_inducedAutomizer_le (d : Coordinates D S)
    {A : Subgroup G} (hn : A ≤ normalizer (fullModule L V : Set G))
    (hI : inducedAutomizer (fullModule L V) A ≤ inducedAutomizer (fullModule L V) L) :
    A ⊓ centralizer (V : Set G) = A ⊓ centralizer (fullModule L V : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le seed_le_fullModule))
  rintro a ⟨ha,hac⟩
  refine ⟨ha,?_⟩
  let aN : normalizer (fullModule L V : Set G) := ⟨a,hn ha⟩
  have hi : (fullModule L V).normalizerMonoidHom.rangeRestrict aN ∈
      inducedAutomizer (fullModule L V) L := hI (mem_map_of_mem _ ha)
  obtain ⟨l,hl,he⟩ := hi
  have hev (v : fullModule L V) : (l:G)*(v:G)*(l:G)⁻¹=a*(v:G)*a⁻¹ :=
    congrArg (fun f : Automizer (fullModule L V) => (f.val v : G)) he
  have hlc : (l:G) ∈ centralizer (V : Set G) := by
    intro v hv
    have hh := hev ⟨v,seed_le_fullModule hv⟩
    rw [← hac v hv,mul_inv_cancel_right] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hlW : (l:G) ∈ centralizer (fullModule L V : Set G) :=
    ((component_seed_centralizer d).le ⟨hl,hlc⟩).2
  intro w hw
  have hh := (hev ⟨w,hw⟩).symm
  rw [← hlW w hw,mul_inv_cancel_right] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The active conjugate has precisely the same centralizer on V and V_M. -/
theorem conjugate_seed_centralizer (d : Coordinates D S) (g : G)
    (hn : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (fullModule L V : Set G))
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    (fullModule L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) =
      (fullModule L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (fullModule L V : Set G) :=
  seed_centralizer_of_inducedAutomizer_le d hn (conjugate_inducedAutomizer_le d g hn hne)

/-- Both reciprocal actions have the same kernel on the original constituent
as on its doubled module. -/
theorem pair_seed_centralizers (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    (fullModule L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) =
      (fullModule L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (fullModule L V : Set G) ∧
    fullModule L V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) =
      fullModule L V ⊓ centralizer ((fullModule L V).map (MulAut.conj g).toMonoidHom : Set G) := by
  have hn := le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)
  refine ⟨conjugate_seed_centralizer d g hn hne,?_⟩
  have hcancel : ((fullModule L V).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = fullModule L V := by
    rw [offender_map_conj_map,inv_mul_cancel]
    have he : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext; simp
    rw [he,map_id]
  have hcancel' : ((fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = fullModule L V := by
    rw [offender_map_conj_map,mul_inv_cancel]
    have he : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext; simp
    rw [he,map_id]
  have hn' : (fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (fullModule L V : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hcomm.trans inf_le_right)
    rw [map_commutator,hcancel,commutator_comm] at hh
    exact hh
  have hne' : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) hz
    rw [map_commutator,hcancel',Subgroup.map_bot,commutator_comm] at hh
    exact hne hh
  have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom)
    (conjugate_seed_centralizer d g⁻¹ hn' hne')
  rw [Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    Theory.GroupTheory.map_centralizer_equiv,Theory.GroupTheory.map_centralizer_equiv,hcancel'] at hh
  exact hh

/-- A noncommuting full critical pair already gives a noncommuting pair of
its original chosen seeds. No natural copy is substituted for either seed. -/
theorem pair_seed_commutator_ne_bot (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  intro hz
  obtain ⟨h₁,h₂⟩ := pair_seed_centralizers d g hne hcomm
  have hVC : V ≤ centralizer ((fullModule L V).map (MulAut.conj g).toMonoidHom : Set G) :=
    ((le_inf seed_le_fullModule (commutator_eq_bot_iff_le_centralizer.mp hz)).trans h₂.le).trans inf_le_right
  have hBC := le_centralizer_iff.mp hVC
  have hBW := ((le_inf le_rfl hBC).trans h₁.le).trans inf_le_right
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hBW))

end CriticalAction

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The actual F.7.11 pair has noncommuting original chosen constituents,
with both normalization and commutator containment proved. This is the
literal source input for the remaining common-line identification. -/
theorem exists_seed_critical_pair (h : Hypothesis1131At D S U₁ H)
    (d : Coordinates D S)
    (hw : indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    ∃ g : G, (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T ∧
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
        fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fullModule L V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨g,hg,hne,hcomm⟩ := exists_doubled_critical_pair d H h.outside.1.1.2 h.outside.1.2 hw
  exact ⟨g,hg,hne,hcomm,CriticalAction.pair_seed_commutator_ne_bot d g hne hcomm,
    CriticalAction.seed_commutator_le_intersection d g hne hcomm,
    CriticalAction.pair_normalizes_seeds d g hne hcomm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
