module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LocalLayers

/-!
# The literal target of the higher commutator map

The source target is Z_a/(Z_a ∩ Z(G_a)), with normality relative to Z_a.
CommonFacts splits Z_a as U_a times its residual-fixed subgroup. The local
source generation identifies that fixed subgroup with Z_a ∩ Z(G_a).
Consequently the actual inclusion of U_a induces an isomorphism onto the
target. Its coordinates use precisely the supplied natural marking, and
its action is induced by ambient conjugation through embedM.

This proves the target identification; it constructs neither the moving
quotient nor a nonzero commutator pairing into this target.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (4.5.4)(iv), p.899.
-/

public section


open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open DistanceFour.Linear
variable {M : Type*} [Group M] {R L : Subgroup M}

/-- The relative subgroup Z_a ∩ Z(G_a), inside Z_a. -/
@[expose] noncomputable def centralDenominator (R : Subgroup M) : Subgroup (Z R (alpha R)) :=
  (center (stabilizer R (alpha R))).comap (inclusion (Z_le_stabilizer R (alpha R)))

/-- Compare the native denominator with the literal ambient intersection. -/
theorem centralDenominator_eq : centralDenominator R =
    (Z R (alpha R) ⊓ (center (stabilizer R (alpha R))).map
      (stabilizer R (alpha R)).subtype).subgroupOf (Z R (alpha R)) := by
  ext z
  constructor
  · intro hz
    exact ⟨z.property, ⟨inclusion (Z_le_stabilizer R (alpha R)) z, hz, rfl⟩⟩
  · rintro ⟨_,w,hw,he⟩
    have hh : w = inclusion (Z_le_stabilizer R (alpha R)) z := Subtype.ext he
    change inclusion (Z_le_stabilizer R (alpha R)) z ∈ center (stabilizer R (alpha R))
    rw [← hh]
    exact hw

instance centralDenominator_normal : (centralDenominator R).Normal := by
  unfold centralDenominator
  infer_instance

/-- The literal target of the printed commutator map on p.899. -/
abbrev CentralQuotient (R : Subgroup M) := Z R (alpha R) ⧸ centralDenominator R

/-- The canonical projection onto the literal target. -/
@[expose] noncomputable def centralQuotientMap (R : Subgroup M) : Z R (alpha R) →* CentralQuotient R :=
  QuotientGroup.mk' (centralDenominator R)

private def zConjugate (m : M) : Z R (alpha R) →* Z R (alpha R) where
  toFun z := ⟨embedM R m * (z : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp (Z_normalized R (alpha R)) _ (by
      rw [alpha, stabilizer_m_base]; exact ⟨m,rfl⟩) _ z.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private theorem zConjugate_fixed (m : M) (z : Z R (alpha R))
    (hz : z ∈ centralDenominator R) : zConjugate m z = z := by
  apply Subtype.ext
  have h := congrArg Subtype.val ((mem_center_iff.mp hz)
    ⟨embedM R m, by rw [alpha,stabilizer_m_base]; exact ⟨m,rfl⟩⟩)
  change embedM R m * (z : FreeAmalgam R) * (embedM R m)⁻¹ = (z : FreeAmalgam R)
  change embedM R m * (z : FreeAmalgam R) = (z : FreeAmalgam R) * embedM R m at h
  rw [h, mul_inv_cancel_right]

/-- Ambient conjugation by the original embedded local group on the target. -/
noncomputable def centralConjugate (m : M) : CentralQuotient R →* CentralQuotient R :=
  QuotientGroup.map _ _ (zConjugate m) (by
    intro z hz
    change zConjugate m z ∈ centralDenominator R
    rw [zConjugate_fixed m z hz]
    exact hz)

/-- The quotient action is induced by the literal ambient conjugation. -/
theorem centralConjugate_mk (m : M) (z z' : Z R (alpha R))
    (h : (z' : FreeAmalgam R) = embedM R m * (z : FreeAmalgam R) * (embedM R m)⁻¹) :
    centralConjugate m (centralQuotientMap R z) = centralQuotientMap R z' := by
  have hh : zConjugate m z = z' := Subtype.ext h.symm
  change centralQuotientMap R (zConjugate m z) = centralQuotientMap R z'
  rw [hh]

variable [Finite M] {geometry : Geometry R} {source : LocalSource L R}
  (common : CommonFacts R source geometry)

include common in
private theorem fixed_eq_denominator :
    (Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))).subgroupOf
      (Z R (alpha R)) = centralDenominator R := by
  ext z
  constructor
  · intro hz
    have hc : (z : FreeAmalgam R) ∈ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) :=
      ((source.X_fixed_eq_stabilizer_fixed (alpha R) rfl).le
        ⟨by rw [common.X_eq_Z (alpha R) rfl]; exact z.property, hz.2⟩).2
    apply mem_center_iff.mpr
    intro m
    apply Subtype.ext
    exact hc m m.property
  · intro hz
    refine ⟨z.property, ?_⟩
    intro l hl
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨l,Ltilde_le_stabilizer _ hl⟩)

private noncomputable def uToCentralQuotient : U R (alpha R) →* CentralQuotient R :=
  (centralQuotientMap R).comp (inclusion (U_le_Z R (alpha R)))

include common in
private theorem uToCentralQuotient_bijective : Function.Bijective (uToCentralQuotient (R := R)) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro u hu
    have huN : inclusion (U_le_Z R (alpha R)) u ∈ centralDenominator R :=
      (QuotientGroup.eq_one_iff _).mp hu
    rw [← fixed_eq_denominator common] at huN
    exact Subtype.ext (disjoint_iff_inf_le.mp common.disjoint ⟨u.property, huN⟩)
  · let U₀ := (U R (alpha R)).subgroupOf (Z R (alpha R))
    let F₀ := (Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))).subgroupOf
      (Z R (alpha R))
    have hF : F₀ = centralDenominator R := fixed_eq_denominator common
    let : F₀.Normal := by rw [hF]; infer_instance
    have hsup : U₀ ⊔ F₀ = ⊤ := by
      rw [← subgroupOf_sup (U_le_Z R (alpha R)) inf_le_left, ← common.decomposition]
      exact subgroupOf_self _
    intro q
    induction q using QuotientGroup.induction_on with
    | H z =>
      obtain ⟨u, hu, f, hf, huf⟩ := mem_sup_of_normal_right.mp
        (show z ∈ U₀ ⊔ F₀ by rw [hsup]; trivial)
      refine ⟨⟨u, hu⟩, ?_⟩
      change centralQuotientMap R u = centralQuotientMap R z
      rw [← huf, map_mul]
      have hf1 : centralQuotientMap R f = 1 :=
        (QuotientGroup.eq_one_iff f).mpr (hF ▸ hf)
      rw [hf1, mul_one]

/-- The target is the same marked natural U_a, using the actual inclusion of U_a. -/
noncomputable def centralQuotientCoordinates : CentralQuotient R ≃* Multiplicative W :=
  (MulEquiv.ofBijective (uToCentralQuotient (R := R))
    (uToCentralQuotient_bijective common)).symm.trans common.natural.equiv

private theorem coordinates_u (u : U R (alpha R)) :
    centralQuotientCoordinates common (uToCentralQuotient u) = common.natural.equiv u := by
  exact congrArg common.natural.equiv
    ((MulEquiv.ofBijective (uToCentralQuotient (R := R))
      (uToCentralQuotient_bijective common)).symm_apply_apply u)

/-- The natural identification uses the actual quotient image of U_a. -/
theorem centralQuotientCoordinates_mk_U (u : U R (alpha R)) :
    centralQuotientCoordinates common
      (centralQuotientMap R (inclusion (U_le_Z R (alpha R)) u)) = common.natural.equiv u :=
  coordinates_u common u

/-- The quotient coordinates retain CommonFacts.natural.marking and source.projection. -/
theorem centralQuotientCoordinates_action (m : M) (q : CentralQuotient R) :
    (centralQuotientCoordinates common (centralConjugate m q)).toAdd =
      (common.natural.marking (source.projection m)).val.mulVec
        (centralQuotientCoordinates common q).toAdd := by
  obtain ⟨u,rfl⟩ := (uToCentralQuotient_bijective common).surjective q
  let v : U R (alpha R) := ⟨embedM R m * (u : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp common.natural.normalized _ ⟨m,rfl⟩ _ u.property⟩
  have hv : centralConjugate m (uToCentralQuotient u) = uToCentralQuotient v := rfl
  rw [hv,coordinates_u,coordinates_u]
  exact common.natural.action m u v rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
