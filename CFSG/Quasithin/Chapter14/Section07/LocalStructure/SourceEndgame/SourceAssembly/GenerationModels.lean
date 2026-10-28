module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.Basic
public import Theory.Representation.SL2FourNaturalOrbits.PlaneOrbits.Determinant
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans

/-!
# Earlier marked-module inputs for the generation argument in 14.7.72

The original upper marking identifies the fixed space with VU₀/V₁. A genuine
cubic actor from the same L₁ multiplies the last natural coordinate by a
nontrivial element of F₄. Every nonzero binary subspace stable under that scalar
is the whole F₄-plane. Pulling back through the original coordinate homomorphism
therefore proves the required irreducibility of U/(VU₀). The same cubic has no
fixed vector on V/V₁, giving C_V(L₁)=V₁.

These are model consequences of the source marking and local actors, not
new 14.7.72 hypotheses. The terminal application builds the existing generation
input and discharges its three marked-module fields and S≤Q.
Source: Aschbacher–Smith, 14.7.65 and proof of 14.7.72, printed p.1076.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.GenerationModels
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
open SteinbergRecognition SteinbergRecognition.SourceGeneration
open SteinbergRecognition.ModuleRecognition.ParabolicSeed
open Matrix.SpecialLinearGroup
open Representation.SL2FourNatural.PlaneGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Descent with exactly the action used by the published generation consumer. -/
def descent (hc : d.SectionCentralizer) : d.ActionDescent :=
  ⟨d.descendedAction hc, d.descendedAction_apply hc⟩

/-- The first identity of 14.7.65 in the original coordinate image. -/
theorem upper_fixed (hc : d.SectionCentralizer) (mark : UpperMarking d)
    (sep : d.ModuleSeparation) (actors : LocalActors d) :
    SL2CentralExtension.upperFixed
      ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient)) =
        d.conjugationSection.imageSpace (V ⊔ d.U₀) := by
  rw [show d.conjugationSection.imageSpace (V ⊔ d.U₀) =
      tilde d V ⊔ d.projection.toLinearMap.ker by
    change tilde d (V ⊔ d.U₀) = _
    rw [tilde_sup d (Data.V_le_U F) d.U₀_le_U, tilde_U₀ d]]
  exact upper_eq_seed_sup_kernel d (descent d hc) mark sep actors

private def lastCoordinates : F.U →* Multiplicative SL2FourNatural.F :=
  (LinearMap.proj (R := ZMod 2) (ι := Fin 2) 1).toAddMonoidHom.toMultiplicative.comp
    (LocalAction.naturalCoordinates d)

private theorem lastCoordinates_ker (hc : d.SectionCentralizer) (mark : UpperMarking d)
    (sep : d.ModuleSeparation) (actors : LocalActors d) :
    (lastCoordinates d).ker = (V ⊔ d.U₀).subgroupOf F.U := by
  ext u
  change d.projection (d.conjugationSection.coordinates u).toAdd 1 = 0 ↔ (u : G) ∈ V ⊔ d.U₀
  rw [← MarkedSpans.mem_upper_iff d (descent d hc)]
  change _ ∈ SL2CentralExtension.upperFixed
    ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient)) ↔ _
  rw [upper_fixed d hc mark sep actors]
  exact coordinate_mem_iff d _ ((F.le_seed 1).trans le_sup_left) u

private theorem lastCoordinates_cubic (l : F.H) (a : SL2FourNatural.F) (ha : a ≠ 0)
    (he : d.qH l = alternatingActor d.naturalQuotient (diag2 a ha)) (u : F.U) :
    (lastCoordinates d ⟨(l : G) * u * (l : G)⁻¹,
      (mem_normalizer_iff.mp (d.conjugationSection.normalized l.property) u).mp u.property⟩).toAdd =
      a⁻¹ * (lastCoordinates d u).toAdd := by
  have h := LocalAction.naturalCoordinates_equivariant d l u
  rw [he] at h
  change (LocalAction.naturalCoordinates d _).toAdd 1 = _
  rw [h]
  change d.naturalQuotient.action (d.naturalQuotient.marking (diag2 a ha))
    (LocalAction.naturalCoordinates d u).toAdd 1 = _
  rw [d.naturalQuotient.restriction]
  simp [SL2FourNatural.action_apply, diag2_coe', Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    lastCoordinates]

private theorem cubic_spans : ∀ a x y : SL2FourNatural.F,
    a ≠ 0 → a ≠ 1 → x ≠ 0 →
    ∃ r t : ZMod 2, y = r • x + t • (a⁻¹ * x) := by
  intro a x y ha ha1 hx
  have hay : a⁻¹ * x ≠ 0 := mul_ne_zero (inv_ne_zero ha) hx
  have hne : x ≠ a⁻¹ * x := by
    intro h
    have he : (1 : SL2FourNatural.F) = a⁻¹ :=
      mul_right_cancel₀ hx ((one_mul x).trans h)
    exact ha1 (inv_eq_one.mp he.symm)
  have hcard : Nat.card SL2FourNatural.F = 4 := by
    rw [Nat.card_eq_fintype_card, SL2FourNatural.card_field]
  rcases four_span hcard ⟨(x, a⁻¹ * x), hx, hay, hne⟩ y
    with hy | hy | hy | hy
  · exact ⟨0, 0, by simpa using hy⟩
  · exact ⟨1, 0, by simpa using hy⟩
  · exact ⟨0, 1, by simpa using hy⟩
  · exact ⟨1, 1, by simpa using hy⟩

/-- The precise interval irreducibility needed before R∩U is known.
Its kernel is the literal VU₀, and the cubic belongs to the original L₁. -/
theorem section_irreducible (hc : d.SectionCentralizer) (mark : UpperMarking d)
    (sep : d.ModuleSeparation) (actors : LocalActors d) : SectionIrreducible d := by
  intro A hEA hAU hNA
  let q := lastCoordinates d
  let X : Submodule (ZMod 2) SL2FourNatural.F :=
    AddSubgroup.toZModSubmodule 2 ((A.subgroupOf F.U).map q).toAddSubgroup'
  have hk : q.ker ≤ A.subgroupOf F.U := by
    rw [lastCoordinates_ker d hc mark sep actors]
    exact subgroupOf_mono F.U hEA
  by_cases hX : X = ⊥
  · left
    apply le_antisymm ?_ hEA
    intro x hx
    have hm : (q ⟨x, hAU hx⟩).toAdd ∈ X := ⟨⟨x, hAU hx⟩, hx, rfl⟩
    rw [hX] at hm
    have hz : (⟨x, hAU hx⟩ : F.U) ∈ q.ker := hm
    rw [lastCoordinates_ker d hc mark sep actors] at hz
    exact hz
  · right
    obtain ⟨l, hl, a, ha, ha1, he⟩ := actors.cubic
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
    have hcub : a⁻¹ * x ∈ X := by
      change Multiplicative.ofAdd x ∈ (A.subgroupOf F.U).map q at hx
      obtain ⟨u, hu, huq⟩ := hx
      refine ⟨⟨(l : G) * u * (l : G)⁻¹,
        (mem_normalizer_iff.mp (d.conjugationSection.normalized l.property) u).mp u.property⟩,
        (mem_normalizer_iff.mp (hNA hl) u).mp hu, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [lastCoordinates_cubic d l a ha he, huq]
      rfl
    have htop : X = ⊤ := by
      apply top_unique
      intro y _
      obtain ⟨r, t, rfl⟩ := cubic_spans a x y ha ha1 hx0
      exact X.add_mem (X.smul_mem r hx) (X.smul_mem t hcub)
    apply le_antisymm hAU
    intro u hu
    have hm : (q ⟨u, hu⟩).toAdd ∈ X := by rw [htop]; trivial
    change q ⟨u, hu⟩ ∈ (A.subgroupOf F.U).map q at hm
    obtain ⟨v, hv, heq⟩ := hm
    have hker : v⁻¹ * ⟨u, hu⟩ ∈ q.ker := by
      change q (v⁻¹ * ⟨u, hu⟩) = 1
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have hmem := A.mul_mem hv (hk hker)
    change (v : G) * ((v : G)⁻¹ * u) ∈ A at hmem
    simpa only [mul_inv_cancel_left] using hmem

/-- The same cubic fixes only the point kernel in the original seed V. -/
theorem seed_fixed (hc : d.SectionCentralizer) (mark : UpperMarking d)
    (sep : d.ModuleSeparation) (actors : LocalActors d) :
    V ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1 := by
  apply le_antisymm
  · intro v hv
    let u : F.U := ⟨v, Data.V_le_U F hv.1⟩
    let w := (d.conjugationSection.coordinates u).toAdd
    have hw : w ∈ tilde d V := (coordinate_mem_iff d V (F.le_seed 1) u).mpr hv.1
    obtain ⟨l, hl, a, ha, ha1, he⟩ := actors.cubic
    have hf : d.action l w = w := by
      have hcj : (l : G) * v * (l : G)⁻¹ = v :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 l hl)
      have h := d.conjugationSection.equivariant l u
      have hj : (⟨(l : G) * u * (l : G)⁻¹,
        (mem_normalizer_iff.mp (d.conjugationSection.normalized l.property) u).mp u.property⟩ : F.U) = u :=
        Subtype.ext hcj
      rw [hj] at h
      exact h.symm
    obtain ⟨r, x, hx⟩ := (mem_upper_iff_point d (descent d hc) w).mp
      (seed_le_upper d (descent d hc) mark actors hw)
    have hz : cover d (descent d hc) (MarkedPartitions.point 0 ((a - 1) * x)) = 0 := by
      rw [← cubic_displacement d (descent d hc) l a ha he, hx, hf, sub_self]
    have hp := congrArg d.projection hz
    rw [cover_projection, MarkedPartitions.point_projection, map_zero] at hp
    have hx0 : x = 0 := (mul_eq_zero.mp (congrFun hp 0)).resolve_left (sub_ne_zero.mpr ha1)
    have hker : w ∈ d.projection.toLinearMap.ker := by
      change d.projection w = 0
      rw [← hx, cover_projection, MarkedPartitions.point_projection, hx0]
      funext i
      fin_cases i <;> rfl
    have hw0 : w = 0 := Submodule.disjoint_def.mp (seed_disjoint_kernel d sep) w hw hker
    exact (d.conjugationSection.coordinates_eq_one_iff u).mp hw0
  · exact le_inf (F.le_seed 1) ((le_centralizer_iff.mp d.H_centralizes_point).trans
      (centralizer_le ((F.Li_le L 1).trans inf_le_right)))


/-- The theorem-70 rank bound in the cardinal form used by rank-two exclusion. -/
theorem fixed_card_le_four (hrank : primeRank 2 d.U₀ ≤ 2) : Nat.card d.U₀ ≤ 4 := by
  let := finite_original d
  have hk := kernel_finrank_le_one d hrank
  rw [d.U₀_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  norm_num at hp
  omega

/-- Build the earlier-source record from one literal 66–70 path. All marked
module fields, the span containment and Sylow normalization are proved here.
The remaining source13 and68 implications are retained at their exact actors. -/
theorem earlier_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h13 : EarlierThirteen c) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hpoint : F.Vi 1 ≤ ⁅F.U, c.Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Earlier d c := {
  critical := e
  thirteen := h13
  upper_mark := mark
  upper_fixed := upper_fixed d e.sectionCentralizer mark e.separation actors
  point_commutator := hpoint
  irreducible := section_irreducible d e.sectionCentralizer mark e.separation actors
  span_le_Q := ChiefFactors.QKPlacement.S_le_Q d structural e.separation
  fixed_bound := fixed_card_le_four d hrank
  sylow_normalizes := d.natural.sylow_normalizes structural
  seed_fixed := seed_fixed d e.sectionCentralizer mark e.separation actors
  centralizer68 := h68 }

/-- The literal 71-centralizer→72-generation consumer, with its earlier marked
module hypotheses discharged instead of being repeated as final assumptions. -/
theorem generation_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h13 : EarlierThirteen c) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hpoint : F.Vi 1 ≤ ⁅F.U, c.Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Conclusion d :=
  generation d c (earlier_of_source d structural c e mark actors h13 hrank hpoint h68)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.GenerationModels
