module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Line
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.MarkedLine.HallSpectrum

/-!
# The scalar and orbit calculation for the original first flag line

Cartan invariance makes the original field-line action scalar. Every nontrivial
odd subgroup of the actual residual Borel has the K-fixed space on Z. After
the preceding fixed-space step, the kernel of the line character would fix a
nontrivial point in V1 intersect Z, so the character is faithful. The actual
Hall order identifies its image with the full extracted torus. The binary
field-span theorem therefore gives the required additive orbit span from
all original V1 intersect Z points.

The final theorem applies these calculations to the existing line consumer,
proving V1 = [V1,D0] and V1 <= V_H. It retains the preceding fixed-space
conclusions and a permitted Cartan, both discharged by the common-action
assembly. No scalar-spectrum or orbit-span callback remains.

Source: Aschbacher--Smith, 11.3.7(5), printed p.773.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {F : BinaryField}

theorem line_scalar_of_normalizes
    (c : Coordinates D F) (f : InvariantFlag c)
    (d : L) (hd : (d : G) ∈ normalizer (f.Vi 0 : Set G)) :
    ∃ a : F.Carrier, ∀ w ∈ f.space 0, c.modelAction (c.quotientMap d) w = a • w := by
  let t : f.space 0 →ₗ[F.Carrier] f.space 0 :=
    ((c.modelAction (c.quotientMap d)).comp (f.space 0).subtype).codRestrict _ (by
      intro v
      exact ((c.mem_normalizer_preimage_iff _ d).mp hd v.val).mpr v.property)
  obtain ⟨a,ha,_⟩ := t.existsUnique_eq_smul_id_of_finrank_eq_one (f.dimension 0)
  refine ⟨a, fun w hw => ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun ha ⟨w,hw⟩)

theorem exists_moving_line_scalar_of_omega_fixed
    (c : Coordinates D F) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (A X : Subgroup G) (hX : IsCartan T L X) (hAX : A ≤ X)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hZfixed : omegaCenter T ⊓ centralizer (A : Set G) = ⊥) :
    ∃ d : L, (d : G) ∈ A ∧ ∃ a : F.Carrier, a ≠ 1 ∧
      ∀ w ∈ f.space 0, c.modelAction (c.quotientMap d) w = a • w := by
  have hAL : A ≤ L := hAX.trans (hX.1.trans inf_le_left)
  have hi : Function.Injective c.projection := by
    apply c.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfixed.le ⟨v.property, (c.projection_eq_one_iff v).mp hv⟩
  by_contra hnone
  have hcentral : f.Vi 0 ≤ centralizer (A : Set G) := by
    intro v hv d hd
    let d' : L := ⟨d,hAL hd⟩
    obtain ⟨a,ha⟩ := line_scalar_of_normalizes c f d'
      (f.cartan_normalizes hu hX 0 (hAX hd))
    have ha1 : a = 1 := by
      by_contra hn
      exact hnone ⟨d',hd,a,hn,ha⟩
    let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
    have he := c.projection_component_conjugation d' v'
    have hm : (c.projection v').toAdd ∈ f.space 0 := (c.mem_preimage _ v').mp hv
    rw [ha _ hm,ha1,one_smul] at he
    have he' := congrArg Subtype.val (hi (Multiplicative.toAdd.injective he))
    exact mul_inv_eq_iff_eq_mul.mp he'
  have hbot : f.Vi 0 ⊓ omegaCenter T = ⊥ := by
    apply bot_unique
    exact (le_inf inf_le_right (inf_le_left.trans hcentral)).trans hZfixed.le
  exact f.V_ne_bot 0 (subgroup_eq_bot_of_central_omega_disjoint (f.Vi 0)
    ((D.centralQuotientPreimage_le _).trans D.le_sylow) (f.invariant 0) hbot)

/-- Scalar values actually realized by elements of A on the original line. -/
def lineScalarValues (c : Coordinates D F) (f : InvariantFlag c) (A : Subgroup G) :
    Set F.Carrier :=
  {a | ∃ d : L, (d : G) ∈ A ∧
    ∀ w ∈ f.space 0, c.modelAction (c.quotientMap d) w = a • w}

/-- Additive generation by the realized scalars gives the required span of
all original omega-center points. No orbit-spanning vector is an input. -/
theorem source_orbit_span_of_scalar_span
    (c : Coordinates D F) (f : InvariantFlag c) (A : Subgroup G)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hscalars : AddSubgroup.closure (lineScalarValues c f A) = ⊤) :
    (f.space 0).toAddSubgroup ≤ AddSubgroup.closure
      {w : c.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧
        (d : G) ∈ A ∧ w = c.modelAction (c.quotientMap d) (c.projection z).toAdd} := by
  have hne : f.Vi 0 ⊓ omegaCenter T ≠ ⊥ := by
    intro hb
    exact f.V_ne_bot 0 (subgroup_eq_bot_of_central_omega_disjoint (f.Vi 0)
      ((D.centralQuotientPreimage_le _).trans D.le_sylow) (f.invariant 0) hb)
  obtain ⟨z,hz,hz1⟩ := (f.Vi 0 ⊓ omegaCenter T).bot_or_exists_ne_one.resolve_left hne
  let z' : V := ⟨z,D.centralQuotientPreimage_le _ hz.1⟩
  have hm : (c.projection z').toAdd ∈ f.space 0 := (c.mem_preimage _ z').mp hz.1
  let u : f.space 0 := ⟨(c.projection z').toAdd,hm⟩
  have hu : u ≠ 0 := by
    intro he
    have hp : c.projection z' = 1 := congrArg Subtype.val he
    exact hz1 (hfixed.le ⟨z'.property,(c.projection_eq_one_iff z').mp hp⟩)
  let Q : AddSubgroup c.Space := AddSubgroup.closure
    {w : c.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧
      (d : G) ∈ A ∧ w = c.modelAction (c.quotientMap d) (c.projection z).toAdd}
  let φ : F.Carrier →+ c.Space :=
    { toFun a := a • (c.projection z').toAdd
      map_zero' := zero_smul _ _
      map_add' a b := add_smul a b _ }
  have hcl : AddSubgroup.closure (lineScalarValues c f A) ≤ Q.comap φ := by
    apply (AddSubgroup.closure_le _).mpr
    rintro a ⟨d,hd,ha⟩
    exact AddSubgroup.subset_closure ⟨z',d,hz,hd,(ha _ hm).symm⟩
  intro w hw
  obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one (f.dimension 0) hu ⟨w,hw⟩
  have ha' : a ∈ AddSubgroup.closure (lineScalarValues c f A) := by
    rw [hscalars]
    trivial
  have hq : a • (c.projection z').toAdd ∈ Q := hcl ha'
  have he : a • (c.projection z').toAdd = w := congrArg Subtype.val ha
  change w ∈ Q
  rw [← he]
  exact hq

/-- The scalar character comes from the literal action on the original line. -/
theorem exists_line_character
    (c : Coordinates D F) (f : InvariantFlag c) (A : Subgroup G) (hAL : A ≤ L)
    (hn : A ≤ normalizer (f.Vi 0 : Set G)) :
    ∃ χ : A →* F.Carrierˣ, ∀ (d : A) (w : c.Space), w ∈ f.space 0 →
      c.modelAction (c.quotientMap (inclusion hAL d)) w = (χ d : F.Carrier) • w := by
  let ρ : A →* Module.End F.Carrier (f.space 0) :=
    { toFun d :=
        ((c.modelAction (c.quotientMap (inclusion hAL d))).comp
          (f.space 0).subtype).codRestrict _ (by
            intro v
            exact ((c.mem_normalizer_preimage_iff _ (inclusion hAL d)).mp
              (hn d.property) v.val).mpr v.property)
      map_one' := by ext v; simp
      map_mul' d e := by ext v; simp; rfl }
  let e : F.Carrier ≃+* Module.End F.Carrier (f.space 0) :=
    RingEquiv.ofBijective (algebraMap F.Carrier (Module.End F.Carrier (f.space 0)))
      (LinearEquiv.smul_id_of_finrank_eq_one (f.dimension 0)).bijective
  let χ := (e.symm.toMonoidHom.comp ρ).toHomUnits
  refine ⟨χ,?_⟩
  intro d w hw
  have he := LinearMap.congr_fun (e.apply_symm_apply (ρ d)) ⟨w,hw⟩
  exact (congrArg Subtype.val he).symm

variable {H : Subgroup G} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Every nontrivial odd subgroup of the actual Borel has the same omega
fixed space as K. This permits application to the kernel of a line character. -/
theorem source_odd_subgroup_omega_fixed
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (B : Subgroup G) (hB : B ≤ H ⊓ normalizer (L : Set G))
    (ho : Odd (Nat.card B)) (hne : B ≠ ⊥) :
    omegaCenter T ⊓ centralizer (B : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G) := by
  have hBK := Hall.odd_le_residual B (hB.trans inf_le_left) ho
  have hn : B.subgroupOf (outsideResidual H) ≤
      normalizer (Hall.residualSylow s : Set (outsideResidual H)) :=
    (comap_mono (hB.trans inf_le_right)).trans (Hall.residual_intersection_normalizes s c)
  have ho' : Odd (Nat.card (B.subgroupOf (outsideResidual H))) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv]
  have hne' : B.subgroupOf (outsideResidual H) ≠ ⊥ := by
    intro he
    apply hne
    have hh := congrArg (map (outsideResidual H).subtype) he
    simpa only [map_subgroupOf_eq_of_le hBK,Subgroup.map_bot] using hh
  obtain ⟨d,hd,b,a,ha,he⟩ := Hall.exists_conjugate_diagonal
    (Hall.quotientMap c) (Hall.quotientMap_surjective c) (Hall.residualSylow s)
    (by rw [Hall.quotientMap_ker]; exact pCore_isPGroup.le_sylow_of_normal _)
    (B.subgroupOf (outsideResidual H)) hn ho' hne'
  exact c.omega_fixed_eq_of_conjugate_diagonal B hBK d hd b a ha he

/-- A line character of an odd subgroup is faithful: its kernel would fix
the nontrivial intersection of the original line with Z. -/
theorem source_line_character_injective
    (cL : Coordinates D S.field) (f : InvariantFlag cL)
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (B : Subgroup G) (hB : B ≤ H ⊓ normalizer (L : Set G))
    (hBL : B ≤ L) (ho : Odd (Nat.card B))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hclosure : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (χ : B →* S.field.Carrierˣ)
    (hχ : ∀ (d : B) (w : cL.Space), w ∈ f.space 0 →
      cL.modelAction (cL.quotientMap (inclusion hBL d)) w = (χ d : S.field.Carrier) • w) :
    Function.Injective χ := by
  have hi : Function.Injective cL.projection := by
    apply cL.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfixed.le ⟨v.property,(cL.projection_eq_one_iff v).mp hv⟩
  let C := χ.ker.map B.subtype
  have hCB : C ≤ B := map_subtype_le _
  have hcentral : f.Vi 0 ≤ centralizer (C : Set G) := by
    intro v hv d hd
    obtain ⟨d',hd',rfl⟩ := hd
    let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
    have hm : (cL.projection v').toAdd ∈ f.space 0 := (cL.mem_preimage _ v').mp hv
    have he := cL.projection_component_conjugation (inclusion hBL d') v'
    rw [hχ d' _ hm,show χ d' = 1 from hd',Units.val_one,one_smul] at he
    exact mul_inv_eq_iff_eq_mul.mp
      (congrArg Subtype.val (hi (Multiplicative.toAdd.injective he)))
  have hC : C = ⊥ := by
    by_contra hne
    have he := source_odd_subgroup_omega_fixed s c C (hCB.trans hB)
      (ho.of_dvd_nat (card_dvd_of_le hCB)) hne
    have hz : omegaCenter T ⊓ centralizer (C : Set G) = ⊥ := by
      rw [he]
      exact bot_unique ((inf_le_inf_right _ (omegaCenter_le_closure T H)).trans hclosure.le)
    have hb : f.Vi 0 ⊓ omegaCenter T = ⊥ :=
      bot_unique ((le_inf inf_le_right (inf_le_left.trans hcentral)).trans hz.le)
    exact f.V_ne_bot 0 (subgroup_eq_bot_of_central_omega_disjoint (f.Vi 0)
      ((D.centralQuotientPreimage_le _).trans D.le_sylow) (f.invariant 0) hb)
  apply χ.ker_eq_bot_iff.mp
  apply (map_injective B.subtype_injective)
  simpa only [Subgroup.map_bot] using hC

private theorem units_subgroup_eq_of_card
    (U W : Subgroup S.field.Carrierˣ) (hc : Nat.card U = Nat.card W) : U = W := by
  let N := (powMonoidHom (Nat.card U) : S.field.Carrierˣ →* S.field.Carrierˣ).ker
  have hU : U ≤ N := by
    intro u hu
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨u,hu⟩ : U)))
  have hW : W ≤ N := by
    intro w hw
    change w ^ Nat.card U = 1
    rw [hc]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨w,hw⟩ : W)))
  have hN : Nat.card N = Nat.card U := by
    rw [IsCyclic.card_powMonoidHom_ker,Nat.gcd_eq_right U.card_subgroup_dvd_card]
  exact (eq_of_le_of_card_ge hU hN.le).trans
    (eq_of_le_of_card_ge hW (hN.trans hc).le).symm

private theorem extracted_card (A : Subgroup G) (e : A ≃* S.field.Carrierˣ) :
    Nat.card (oddCartanPart A) = Nat.card (torusCartanPart S.field) := by
  have hm :
      ((pResidual 3 A) ⊔ (omega₁ (pCore 3 A) (p := 3)).map (pCore 3 A).subtype).map
        e.toMonoidHom = torusCartanPart S.field := by
    rw [torusCartanPart,Subgroup.map_sup,map_pResidual,Subgroup.map_map]
    congr 1
    apply map_omega_eq_of_injective_of_range_eq
      (e.toMonoidHom.comp (pCore 3 A).subtype) (pCore 3 S.field.Carrierˣ).subtype
      (e.injective.comp (pCore 3 A).subtype_injective) (pCore 3 S.field.Carrierˣ).subtype_injective
    rw [MonoidHom.range_comp,range_subtype,range_subtype,pCore_map_iso]
  rw [oddCartanPart,card_map_of_injective A.subtype_injective,← hm,
    card_map_of_injective e.injective]

/-- Faithfulness recovers the entire scalar spectrum on the L-side original
line, using the actual Hall cardinality and the finite-field span theorem. -/
theorem source_line_scalar_span
    (cL : Coordinates D S.field) (f : InvariantFlag cL)
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L)
    (hn : oddCartanPart A ≤ normalizer (f.Vi 0 : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hclosure : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥) :
    AddSubgroup.closure (lineScalarValues cL f (oddCartanPart A)) = ⊤ := by
  obtain ⟨χ,hχ⟩ := exists_line_character cL f (oddCartanPart A) hAL hn
  have hoA : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have hi := source_line_character_injective cL f s c (oddCartanPart A)
    ((oddCartanPart_le A).trans hA) hAL
    (hoA.of_dvd_nat (card_dvd_of_le (oddCartanPart_le A))) hfixed hclosure χ hχ
  obtain ⟨e⟩ := Hall.source_hall_units_equiv s c A hA hHall
  have hrange : χ.range = torusCartanPart S.field := units_subgroup_eq_of_card _ _
    ((Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans (extracted_card A e))
  have hs : torusScalarSet S.field ⊆ lineScalarValues cL f (oddCartanPart A) := by
    rintro a ⟨u,rfl⟩
    obtain ⟨d,hd⟩ := (hrange.symm ▸ u.property : u.val ∈ χ.range)
    refine ⟨inclusion hAL d,d.property,?_⟩
    intro w hw
    rw [hχ d w hw,hd]
  apply top_unique
  rw [← torusScalarSet_additive_closure S.field]
  exact AddSubgroup.closure_mono hs

/-- Both concrete inputs to the original line consumer, with no scalar or
orbit-span assumption. The fixed-space premise is discharged by the preceding
Cartan comparison in the final common-action assembly. -/
theorem source_scalar_and_orbit_of_fixed_spaces
    (cL : Coordinates D S.field) (f : InvariantFlag cL) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hclosure : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥) :
    (∃ d : L, (d : G) ∈ oddCartanPart A ∧ ∃ a : S.field.Carrier, a ≠ 1 ∧
      ∀ w ∈ f.space 0, cL.modelAction (cL.quotientMap d) w = a • w) ∧
    (f.space 0).toAddSubgroup ≤ AddSubgroup.closure
      {w : cL.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧
        (d : G) ∈ oddCartanPart A ∧
        w = cL.modelAction (cL.quotientMap d) (cL.projection z).toAdd} := by
  have hz : omegaCenter T ⊓ centralizer (oddCartanPart A : Set G) = ⊥ := by
    rw [Hall.source_oddCartan_fixed s c A hA hHall]
    exact bot_unique ((inf_le_inf_right _ (omegaCenter_le_closure T H)).trans hclosure.le)
  exact ⟨exists_moving_line_scalar_of_omega_fixed cL f hu (oddCartanPart A) X
    hX hAX hfixed hz,source_orbit_span_of_scalar_span cL f (oddCartanPart A) hfixed
      (source_line_scalar_span cL f s c A hA hHall (hAX.trans (hX.1.trans inf_le_left))
        (hAX.trans (f.cartan_normalizes hu hX 0)) hfixed hclosure)⟩

/-- The original V1 commutator and containment follow from the preceding
fixed-space conclusions. All line scalar and orbit calculations are discharged. -/
theorem source_line_of_fixed_spaces
    (cL : Coordinates D S.field) (f : InvariantFlag cL) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hclosure : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥) :
    f.Vi 0 = ⁅f.Vi 0,oddCartanPart A⁆ ∧ f.Vi 0 ≤ omegaClosure T H := by
  obtain ⟨⟨d,hd,a,ha,hscalar⟩,hspan⟩ := source_scalar_and_orbit_of_fixed_spaces cL f hu
    s c A X hA hHall hX hAX hfixed hclosure
  exact source_line_of_scalar_and_orbit cL f hu A X (hA.trans inf_le_left)
    hX hAX hfixed d hd a ha hscalar hspan

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

