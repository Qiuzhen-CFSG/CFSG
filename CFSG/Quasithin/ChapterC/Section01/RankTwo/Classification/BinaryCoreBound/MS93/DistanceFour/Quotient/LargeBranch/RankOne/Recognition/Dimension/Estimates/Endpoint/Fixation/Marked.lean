module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry.Parabolics

/-!
# A cubic and reflection in the same marked first parabolic

Choose a generator of an actual order-three subgroup of the source residual
which surjects onto its marked SL₂(2)' quotient. Its norm vectors are fixed
by that generator. The vanishing invariant spaces of the two literal source
sections first place these vectors in K/Z_alpha and then in Y/Z_alpha.
All actions use the original projection, including on both quotient spaces.

The actual S₄ identification of the first model parabolic supplies an
inverting involution. A small kernel-checked permutation calculation proves
that the cubic, reflection and intrinsic four-group generate the full
parabolic. The source frame identifies this four-group with the original
edge image, and intrinsic core alignment identifies the arbitrary compatible
seed frame's first actor with this same parabolic.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on printed p.905, (4.6.12)(1)--(2) on p.910, and the
full-actor fixation argument at the beginning of (4.6.12)(5), p.911.
-/

public section
open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Fixation

private abbrev S4 := Equiv.Perm (Fin 4)
set_option maxRecDepth 10000 in
private def fourCore : Subgroup S4 where
  carrier := {g | g.sign = 1 ∧ g ^ 2 = 1}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance : fourCore.Normal where
  conj_mem n hn g := by
    change n.sign = 1 ∧ n ^ 2 = 1 at hn
    change (g * n * g⁻¹).sign = 1 ∧ (g * n * g⁻¹) ^ 2 = 1
    constructor
    · simp only [map_mul, map_inv, hn.1, mul_one, mul_inv_cancel]
    · calc
        (g * n * g⁻¹) ^ 2 = g * n ^ 2 * g⁻¹ := by
          simp only [pow_two, mul_assoc, inv_mul_cancel_left]
        _ = 1 := by rw [hn.2, mul_one, mul_inv_cancel]

private theorem fourCore_le : fourCore ≤ pCore 2 S4 := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  intro x
  exact ⟨1, Subtype.ext (by simpa using x.property.2)⟩

set_option maxRecDepth 10000 in
private theorem reflection_calculation :
    ∀ t : S4, t ^ 3 = 1 → t ≠ 1 →
      ∃ b : S4, b ^ 2 = 1 ∧ b * t = t ^ 2 * b ∧
        ∀ g : S4, ∃ v : S4, (v.sign = 1 ∧ v ^ 2 = 1) ∧
          ∃ i : Fin 3, ∃ j : Fin 2, g = v * t ^ i.val * b ^ j.val := by
  decide +kernel

private theorem reflection_S4 (t : S4) (ht : t ^ 3 = 1) (hne : t ≠ 1) :
    ∃ b : S4, b ^ 2 = 1 ∧ b * t = t ^ 2 * b ∧
      (pCore 2 S4 ⊔ zpowers t) ⊔ zpowers b = ⊤ := by
  obtain ⟨b, hb, hbt, hgen⟩ := reflection_calculation t ht hne
  refine ⟨b, hb, hbt, top_unique ?_⟩
  intro g _
  obtain ⟨v, hv, i, j, rfl⟩ := hgen g
  apply mul_mem
  · apply mul_mem
    · exact (show pCore 2 S4 ≤ (pCore 2 S4 ⊔ zpowers t) ⊔ zpowers b from
        le_sup_left.trans le_sup_left) (fourCore_le hv)
    · exact (show zpowers t ≤ (pCore 2 S4 ⊔ zpowers t) ⊔ zpowers b from
        le_sup_right.trans le_sup_left) (pow_mem (mem_zpowers t) _)
  · exact (show zpowers b ≤ (pCore 2 S4 ⊔ zpowers t) ⊔ zpowers b from
      le_sup_right) (pow_mem (mem_zpowers b) _)

private theorem reflection_of_equiv {G : Type*} [Group G]
    (e : G ≃* S4) (t : G) (ht : t ^ 3 = 1) (hne : t ≠ 1) :
    ∃ b : G, b ^ 2 = 1 ∧ b * t = t ^ 2 * b ∧
      (pCore 2 G ⊔ zpowers t) ⊔ zpowers b = ⊤ := by
  obtain ⟨b, hb, hbt, hgen⟩ := reflection_S4 (e t)
    (by rw [← map_pow, ht, map_one]) (by simpa using hne)
  refine ⟨e.symm b, ?_, ?_, ?_⟩
  · rw [← map_pow, hb, map_one]
  · apply e.injective
    simpa only [map_mul, map_pow, e.apply_symm_apply] using hbt
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, Subgroup.map_sup, pCore_map_iso,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      map_top_of_surjective _ e.surjective]
    simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hgen

private theorem cubic_fixed {k G W : Type*} [Field k] [Group G]
    [AddCommGroup W] [Module k W] (ρ : Representation k G W)
    (t : G) (ht : t ^ 3 = 1) (v : W) :
    ρ t ((ρ t ^ 2 + ρ t + 1 : Module.End k W) v) =
      (ρ t ^ 2 + ρ t + 1 : Module.End k W) v := by
  have hcube : ρ t ^ 3 = 1 := by rw [← map_pow, ht, map_one]
  have hmul : ρ t * (ρ t ^ 2 + ρ t + 1) = ρ t ^ 2 + ρ t + 1 := by
    rw [mul_add, mul_add, ← pow_succ', hcube, mul_one, ← pow_two]
    abel
  exact LinearMap.congr_fun hmul v

open Flags.RankOne Sections
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem norm_mem_of_cubic
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (f : Sections.Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R)))
    (g : flagResidual source f.orientation) (hg : g ^ 3 = 1)
    (hgen : zpowers (markedResidualProjection source f g) = ⊤) :
    ∀ v : d.Space,
      (d.representation (source.projection ((residualEquiv source f.orientation).symm g)) ^ 2 +
        d.representation (source.projection ((residualEquiv source f.orientation).symm g)) + 1 :
          Module.End (ZMod 2) d.Space) v ∈ d.subspace (fixedPreimage s.middle) := by
  let t := source.projection ((residualEquiv source f.orientation).symm g)
  let c := markedResidualProjection source f g
  let K := d.subspace (intersection s.middle)
  let Y := d.subspace (fixedPreimage s.middle)
  let ρ₁ := firstCRepresentation common radius f hb s hbc d
  let ρ₂ := secondCRepresentation common radius f hb s hbc d
  have ht : t ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, hg, map_one,
      Subgroup.coe_one, map_one]
  intro v
  let w := (d.representation t ^ 2 + d.representation t + 1 : Module.End (ZMod 2) d.Space) v
  have hw : d.representation t w = w := cubic_fixed d.representation t ht v
  have hfirst : ρ₁ c (K.mkQ w) = K.mkQ w := by
    rw [firstCRepresentation_apply]
    change K.mkQ (d.representation t w) = K.mkQ w
    rw [hw]
  have h₁ : K.mkQ w ∈ ρ₁.invariants :=
    (ρ₁.mem_invariants_iff_of_forall_mem_zpowers c
      (fun x => hgen ▸ mem_top x) _).mpr hfirst
  rw [firstCRepresentation_invariants_eq_bot common radius f hb s hbc d] at h₁
  have hwK : w ∈ K := (Submodule.Quotient.mk_eq_zero K).mp h₁
  let wK : K := ⟨w, hwK⟩
  let J := Y.comap K.subtype
  have hsecond : ρ₂ c (J.mkQ wK) = J.mkQ wK := by
    rw [secondCRepresentation_apply]
    change J.mkQ ⟨d.representation t w, _⟩ = J.mkQ wK
    congr 1
    exact Subtype.ext hw
  have h₂ : J.mkQ wK ∈ ρ₂.invariants :=
    (ρ₂.mem_invariants_iff_of_forall_mem_zpowers c
      (fun x => hgen ▸ mem_top x) _).mpr hsecond
  rw [secondCRepresentation_invariants_eq_bot common radius f hb s hbc d] at h₂
  exact (Submodule.Quotient.mk_eq_zero J).mp h₂

private theorem exists_marked_generator (source : LocalSource L R) (f : Sections.Frame source) :
    ∃ g : flagResidual source f.orientation, g ^ 3 = 1 ∧
      zpowers (markedResidualProjection source f g) = ⊤ := by
  let : Finite (flagResidual source f.orientation) :=
    Finite.of_injective (residualEquiv source f.orientation).symm
      (residualEquiv source f.orientation).symm.injective
  obtain ⟨T, hT, hTmap⟩ := exists_marked_cubic source f
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic T := isCyclic_of_prime_card hT
  obtain ⟨g, hg⟩ := T.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have ho : orderOf g = 3 := by rw [← Nat.card_zpowers, hg, hT]
  refine ⟨g, ?_, ?_⟩
  · rw [← ho]; exact pow_orderOf_eq_one g
  · rw [← MonoidHom.map_zpowers, hg, hTmap]

private theorem model_core_eq_edge (source : LocalSource L R) (f : Sections.Frame source) :
    (modelParabolic source.flag f.orientation).pCoreIn 2 = R.map source.projection := by
  have hk : (parabolic source.projection source.flag f.orientation).pCoreIn 2 = R := by
    apply Subgroup.map_injective (f := embedM R) (embedM_injective R)
    exact f.edge_kernel.trans (Q_beta R)
  have he := congrArg (Subgroup.map source.projection) hk
  rw [map_pCoreIn_of_ker_isPGroup source.projection
    (by rw [source.projection_kernel]; exact pCore_isPGroup)] at he
  rwa [parabolic, map_comap_eq_self_of_surjective source.projection_surjective] at he

/-- The marked cubic/reflection data for the arbitrary supplied compatible
seed frame. The two natural source sections force the cubic norm into the
literal Y; the full parabolic is generated by the same cubic, an inverting
involution, and the original edge image. -/
theorem exists_cubicData
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) : Nonempty (CubicData d f s.middle) := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  obtain ⟨g, hg, hgen⟩ := exists_marked_generator source k
  let x := (residualEquiv source k.orientation).symm g
  let t := source.projection x
  let P := modelParabolic source.flag k.orientation
  let tP : P := modelResidualMap source k x
  have ht : t ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, hg, map_one,
      Subgroup.coe_one, map_one]
  have htP : tP ^ 3 = 1 := Subtype.ext ht
  have htPne : tP ≠ 1 := by
    intro he
    have hc : markedResidualProjection source k g = 1 := by
      apply Subtype.ext
      change quotientModelMap source k tP = 1
      rw [he, map_one]
    have hbad : (⊥ : Subgroup BinarySL2Residual.C) = ⊤ := by
      simpa only [hc, zpowers_one_eq_bot] using hgen
    have hcard := congrArg (fun A : Subgroup BinarySL2Residual.C => Nat.card A) hbad
    rw [Subgroup.card_bot, Subgroup.card_top, sl2_twoResidual_card] at hcard
    contradiction
  obtain ⟨bP, hbP, hinv, hfull⟩ := reflection_of_equiv
    (modelParabolicEquivSymmetric source.flag k.orientation) tP htP htPne
  refine ⟨{
    cubic := t
    reflection := (bP : SL)
    cube := ht
    square := congrArg Subtype.val hbP
    inverts := congrArg Subtype.val hinv
    norm_mem := norm_mem_of_cubic common radius k hb s hbc d g hg hgen
    generates := ?_ }⟩
  have hP : (f.actor false).map source.projection = P := by
    rw [f.actor_eq, f.first_parabolic_eq_flag s hf k.orientation k.edge_kernel]
    exact map_comap_eq_self_of_surjective source.projection_surjective _
  rw [hP]
  have hfull' := congrArg (Subgroup.map P.subtype) hfull
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at hfull'
  change (P.pCoreIn 2 ⊔ zpowers t) ⊔ zpowers (bP : SL) = P at hfull'
  rw [model_core_eq_edge source k] at hfull'
  exact hfull'.ge

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Fixation
