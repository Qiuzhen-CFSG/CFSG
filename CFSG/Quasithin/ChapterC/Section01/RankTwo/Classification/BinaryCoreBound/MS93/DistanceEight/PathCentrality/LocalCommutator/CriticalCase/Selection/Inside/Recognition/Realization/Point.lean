module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization.PointData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Natural
public import Theory.Representation.SpecialLinearThreeTransitivity

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization

/-!
# Marking the actual quotient point in MS93 (4.4.1)(2)

The image of Z_c in G_c/D_c is exactly the embedded image of U_c. Thus a
point x in Z_c D_c outside D_c has a nonzero natural coordinate vector, with
an actual lift in U_c. Injectivity on U_c turns centralizing xD_c into fixing
that vector. Its stabilizer is self-normalizing: two elementary matrices
fix only the standard nonzero point, and transitivity transports this fact.
Surjective preimage and relative-normalizer identities then identify the
literal K_0 and K of the source with the same marked point-stabilizer preimage.

The final application supplies the marking to the existing construction of
EscapingConfiguration on the actual local-span head. It uses no later natural
section, recognition theorem, or faithfulness premise.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1)(2), printed p.891, and (1.6), printed pp.845--847.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
open Escape.PairingControl.FirstPairing

open Orientation.QuotientApplication
private def t01 : SL := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
private def t02 : SL := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

private theorem base_fixed : ∀ w : Fin 3 → ZMod 2, w ≠ 0 →
    t01 • w = w → t02 • w = w → w = ![1, 0, 0] := by
  decide +kernel

private theorem fixed_by_stabilizer (v w : Fin 3 → ZMod 2)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (h : ∀ s : SL, s • v = v → s • w = w) : w = v := by
  obtain ⟨k, hk⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three ![1, 0, 0] v
    (by decide) hv
  change k • (![1, 0, 0] : Fin 3 → ZMod 2) = v at hk
  have hs (s : SL) (hs : s • (![1, 0, 0] : Fin 3 → ZMod 2) = ![1, 0, 0]) :
      s • (k⁻¹ • w) = k⁻¹ • w := by
    have hh := h (k * s * k⁻¹) (by rw [← hk]; simp only [mul_smul, inv_smul_smul, hs])
    have hh' := congrArg (fun z => k⁻¹ • z) hh
    simpa only [mul_smul, inv_smul_smul] using hh'
  have hn : k⁻¹ • w ≠ 0 := by
    intro hz
    apply hw
    have hh := congrArg (fun z => k • z) hz
    simpa only [smul_inv_smul, smul_zero] using hh
  have he := base_fixed (k⁻¹ • w) hn (hs t01 (by decide)) (hs t02 (by decide))
  have hh := congrArg (fun z => k • z) he
  simpa only [smul_inv_smul, hk] using hh

private theorem stabilizer_normalizer (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    normalizer (MulAction.stabilizer SL v : Set SL) = MulAction.stabilizer SL v := by
  apply le_antisymm _ (MulAction.stabilizer SL v).le_normalizer
  intro g hg
  apply fixed_by_stabilizer v (g • v) hv
  · intro hz
    apply hv
    have hh := congrArg (fun z => g⁻¹ • z) hz
    simpa only [inv_smul_smul, smul_zero] using hh
  · intro s hs
    have hm := (mem_normalizer_iff.mp
      ((normalizer (MulAction.stabilizer SL v : Set SL)).inv_mem hg) s).mp
        (show s ∈ MulAction.stabilizer SL v from hs)
    simp only [inv_inv, MulAction.mem_stabilizer_iff] at hm
    have hh := congrArg (fun z => g • z) hm
    simpa only [mul_smul, smul_inv_smul] using hh


private theorem markedPointStabilizer_normalizer (marking : SL ≃* SL)
    (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    normalizer (markedPointStabilizer marking v : Set SL) =
      markedPointStabilizer marking v := by
  rw [markedPointStabilizer,
    ← comap_normalizer_eq_of_surjective _ marking.surjective]
  exact congrArg (fun H : Subgroup SL => H.comap marking.toMonoidHom)
    (stabilizer_normalizer v hv)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem exists_point_lift (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false) (x : stabilizer R c)
    (hxZ : (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c) :
    ∃ u : (U R c).subgroupOf (stabilizer R c),
      quotientMap c (u : stabilizer R c) = quotientMap c x := by
  have hp : (x : FreeAmalgam R) ∈
      (Z R c : Set (FreeAmalgam R)) * (fixedCore R c : Set (FreeAmalgam R)) := by
    rw [← join_fixedCore_eq_mul R (Z R c) (Z_le_stabilizer R c)]
    exact hxZ
  obtain ⟨z, hz, d, hd, hzd⟩ := hp
  let zS : stabilizer R c := ⟨z, Z_le_stabilizer R c hz⟩
  let dS : stabilizer R c := ⟨d, hd.1.1⟩
  have hxd : zS * dS = x := Subtype.ext hzd
  have hdπ : quotientMap c dS = 1 := (QuotientGroup.eq_one_iff dS).mpr hd
  have hxπ : quotientMap c x = quotientMap c zS := by
    rw [← hxd, map_mul, hdπ, mul_one]
  have hzπ : quotientMap c x ∈ quotientImage c (Z R c) := by
    rw [hxπ]
    exact mem_map_of_mem _ hz
  rw [quotientImage_Z_eq_U (moduleFacts common) c hc] at hzπ
  obtain ⟨u, hu, he⟩ := hzπ
  exact ⟨⟨u, hu⟩, he⟩

private theorem pointCentralizer_coordinates (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false) (x : stabilizer R c)
    (n : RankOnePairing.NaturalFactor (localProjection source c hc) ⊤
      ((U R c).subgroupOf (stabilizer R c)) ⊥)
    (u : (U R c).subgroupOf (stabilizer R c))
    (hu : quotientMap c (u : stabilizer R c) = quotientMap c x)
    (g : stabilizer R c) :
    (g : FreeAmalgam R) ∈ pointCentralizer c x ↔
      localProjection source c hc g ∈
        markedPointStabilizer n.marking (n.coordinates u).toAdd := by
  let v : (U R c).subgroupOf (stabilizer R c) :=
    ⟨g * (u : stabilizer R c) * g⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top g)) _).mp u.property⟩
  have hact := n.action g (mem_top g) u v rfl
  have hq : quotientMap c (v : stabilizer R c) = quotientMap c (u : stabilizer R c) ↔
      v = u := by
    constructor
    · intro he
      apply (naturalImageMap_bijective (moduleFacts common) c hc).injective
      exact Subtype.ext he
    · intro he
      rw [he]
  rw [mem_pointCentralizer_iff, mem_markedPointStabilizer]
  change quotientMap c g * quotientMap c x = quotientMap c x * quotientMap c g ↔ _
  rw [← hu]
  have hcomm : quotientMap c g * quotientMap c (u : stabilizer R c) =
      quotientMap c (u : stabilizer R c) * quotientMap c g ↔ v = u := by
    rw [← hq]
    change _ ↔ quotientMap c (g * (u : stabilizer R c) * g⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
  rw [hcomm, ← hact]
  constructor
  · intro he
    rw [he]
  · intro he
    exact n.equivOfBot.injective (congrArg Multiplicative.ofAdd he)

private theorem pointNormalizer_coordinates (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false) (x : stabilizer R c)
    (n : RankOnePairing.NaturalFactor (localProjection source c hc) ⊤
      ((U R c).subgroupOf (stabilizer R c)) ⊥)
    (u : (U R c).subgroupOf (stabilizer R c))
    (hu : quotientMap c (u : stabilizer R c) = quotientMap c x)
    (hne : (n.coordinates u).toAdd ≠ 0) (g : stabilizer R c) :
    (g : FreeAmalgam R) ∈ pointNormalizer c x ↔
      localProjection source c hc g ∈
        markedPointStabilizer n.marking (n.coordinates u).toAdd := by
  let K := markedPointStabilizer n.marking (n.coordinates u).toAdd
  have hK : (pointCentralizer c x).subgroupOf (stabilizer R c) =
      K.comap (localProjection source c hc) := by
    ext y
    exact pointCentralizer_coordinates source geometry common hc x n u hu y
  have hN : normalizer ((pointCentralizer c x).subgroupOf (stabilizer R c) :
      Set (stabilizer R c)) = K.comap (localProjection source c hc) := by
    rw [hK, ← comap_normalizer_eq_of_surjective K (localProjection_surjective source c hc),
      markedPointStabilizer_normalizer n.marking _ hne]
  change ((g : FreeAmalgam R) ∈ stabilizer R c ∧
    (g : FreeAmalgam R) ∈ normalizer (pointCentralizer c x : Set (FreeAmalgam R))) ↔ _
  rw [and_iff_right g.property]
  change g ∈ (normalizer (pointCentralizer c x : Set (FreeAmalgam R))).subgroupOf
    (stabilizer R c) ↔ _
  rw [subgroupOf_normalizer_eq (pointCentralizer_le_stabilizer c x), hN]
  rfl

/-- Mark the actual point xD_c in the natural subgroup U_c, retaining the
literal relative normalizer used in MS93 (4.4.1)(2). -/
theorem localPointMarking_nonempty (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false) (x : stabilizer R c)
    (hxD : (x : FreeAmalgam R) ∉ fixedCore R c)
    (hxZ : (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c) :
    Nonempty (LocalPointMarking source c hc x) := by
  obtain ⟨n⟩ := Orientation.naturalU_nonempty (moduleFacts common) c hc
    (localProjection source c hc) (localProjection_surjective source c hc)
    (localProjection_kernel source c hc)
  obtain ⟨u, hu⟩ := exists_point_lift source geometry common hc x hxZ
  have hne : (n.coordinates u).toAdd ≠ 0 := by
    intro hz
    have he : n.coordinates u = 1 := congrArg Multiplicative.ofAdd hz
    have hu1 : u = 1 := n.equivOfBot.injective (he.trans (map_one n.coordinates).symm)
    have hq := quotient_point_ne_one c x hxD
    change quotientMap c x ≠ 1 at hq
    apply hq
    rw [← hu, hu1, coe_one, map_one]
  exact ⟨{ naturalU := n
           lift := u
           quotient_eq := hu
           nonzero := hne
           normalizer := pointNormalizer_coordinates source geometry common hc x n u hu hne }⟩


/-- The original quotient point supplies the marking required by the existing
local-span construction of the input to MS93 (1.6). -/
theorem escapingConfiguration_nonempty_of_quotientPoint (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c e : Vertex R}
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (x : stabilizer R c)
    (hxD : (x : FreeAmalgam R) ∉ fixedCore R c)
    (hxZ : (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c)
    (hsmall : (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2) :
    Nonempty (EscapingConfiguration (spanHeadAction source geometry a c hc)) := by
  obtain ⟨point⟩ := localPointMarking_nonempty source geometry common hc x hxD hxZ
  exact escapingConfiguration_nonempty_of_markedPoint source geometry common hb hc hd p x
    point hsmall

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
