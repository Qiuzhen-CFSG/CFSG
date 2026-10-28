module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant.Transport

/-!
# The actual natural plane in the opposite branch of MS93 (4.4.1)

The supplied parabolic normalizes the moving cyclic displacement K and has
zero fixed subgroup on U_c. The earlier edge bound makes K elementary of
order at most four, and the natural section bounds [K,Ltilde_c] by Z_c.

In the literal quotient G_c/D_c, adjoin the natural Z-image to the image of
K. Small residual localization places that image in the natural subgroup.
The given marking identifies the selected parabolic with a line parabolic,
whose two-residual has zero fixed space. Its nontrivial action on K forces
K = [K,O²(P)]. Since D_c centralizes O²(P), this equality removes the fixed
core error and puts K inside the actual U_c. Orders one and two would force
K to be fixed by P, so its order is four.

The final consumer supplies these two conclusions to the proved algebraic
edge assembly. Existence of the ParabolicSeed remains with its separate
producer; no escape counterexample or favorable pairing is used here.

The central-error and order-two normalizer arguments adapt
FirstPairing/Orientation/QuotientApplication/Verification/CommutatorBounds/
CyclicLocalization/Layer.lean. The small invariant and fixed-kernel lifting
arguments reuse FirstPairing/StepThree/RankOne/SmallInvariant.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), printed
pp.890–891, the deduction after normalization by a conjugate of F₂.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
open RankOnePairing Escape.PairingControl.FirstPairing
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction ModelProof
open Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant
open Escape.PairingControl.FirstPairing.Orientation.QuotientApplication

private theorem natural_fixed_iff {G : Type*} [Group G]
    {π : G →* SL} {Z : Subgroup G} (n : NaturalFactor π ⊤ Z ⊥)
    (P : Subgroup G) :
    Z ⊓ centralizer (P : Set G) = ⊥ ↔
      fixedSpace ((P.map π).map n.marking.toMonoidHom) = ⊥ := by
  have hfixed (z : Z) : (z : G) ∈ centralizer (P : Set G) ↔
      n.coordinates z ∈ fixedSpace ((P.map π).map n.marking.toMonoidHom) := by
    constructor
    · intro hz g hg
      obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := hg
      have hh := n.action p (mem_top _) z z (by
        rw [hz p hp, mul_inv_cancel_right])
      exact hh.symm
    · intro hz p hp
      let z' : Z := ⟨p * (z : G) * p⁻¹,
        (mem_normalizer_iff.mp (n.normalized (mem_top p)) z).mp z.property⟩
      have hh : n.coordinates z' = n.coordinates z :=
        (n.action p (mem_top _) z z' rfl).trans
          (hz _ (mem_map_of_mem _ (mem_map_of_mem π hp)))
      have he := congrArg Subtype.val (n.equivOfBot.injective hh)
      exact mul_inv_eq_iff_eq_mul.mp he
  constructor
  · intro hz
    apply le_bot_iff.mp
    intro v hv
    obtain ⟨z, rfl⟩ := n.surjective v
    have he : z = 1 := Subtype.ext (hz.le ⟨z.property, (hfixed z).mpr hv⟩)
    simp only [he, map_one, mem_bot]
  · intro hz
    apply le_bot_iff.mp
    rintro z ⟨hzZ, hzP⟩
    have hh : n.coordinates ⟨z, hzZ⟩ = 1 := hz.le ((hfixed ⟨z,hzZ⟩).mp hzP)
    exact congrArg Subtype.val (n.equivOfBot.injective (hh.trans (map_one _).symm))

private theorem marked_residual_fixed (σ : MulAut SL) (flag : SL) (i : Bool)
    (hf : fixedSpace (markedParabolic σ flag i) = ⊥) :
    fixedSpace (Matrix.PSL3Two.MarkedAutomorphisms.residual
      (markedParabolic σ flag i)) = ⊥ := by
  open Matrix.PSL3Two.MarkedAutomorphisms in
  obtain ⟨k, ⟨hp, _⟩ | ⟨hp, _⟩⟩ := marked_pair σ flag i
  · have hle := map_mono (f := (vectorAction k).toMonoidHom) line_fixed_by_point
    rw [← fixedSpace_conj, ← hp, hf] at hle
    have he : pointLine = ⊥ := (map_eq_bot_iff_of_injective _ (vectorAction k).injective).mp
      (le_bot_iff.mp hle)
    have hh := line_card
    rw [he, card_bot] at hh
    omega
  · have he : markedParabolic σ flag i = modelParabolic k true := hp
    rw [he]
    exact line_residual_fixed_eq_bot k

private theorem centralizes_of_central_error {G : Type*} [Group G] [Finite G]
    (P E D : Subgroup G) [D.Normal] (hp : IsPGroup 2 P)
    (he : IsPPerfect 2 E) (hDP : D ≤ P) (hDE : ⁅D,E⁆ = ⊥)
    (x : G) (hx : x ∈ P) (hcomm : ∀ y ∈ E, ⁅x,y⁆ ∈ D) :
    x ∈ centralizer (E : Set G) := by
  let N := commutatorPreimage P E D
  have hDN : D ≤ N := le_commutatorPreimage hDP (hDE.le.trans bot_le)
  have hNE : ⁅N,E⁆ ≤ D := commutator_commutatorPreimage_le P E D le_normalizer_of_normal
  have hn : E ≤ normalizer N :=
    le_normalizer_iff_commutator_le_left.mpr (hNE.trans hDN)
  have hz : ⁅N,E⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent E N he
      (hp.to_le (commutatorPreimage_le P E D)) hn]
    exact le_bot_iff.mp ((commutator_mono hNE le_rfl).trans hDE.le)
  apply commutator_eq_bot_iff_le_centralizer.mp hz
  change x ∈ commutatorPreimage P E D
  rw [commutatorPreimage_eq_inf_comap_centralizer]
  refine ⟨hx, ?_⟩
  rintro _ ⟨y,hy,rfl⟩
  have hc : ⁅QuotientGroup.mk' D x, QuotientGroup.mk' D y⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm y hy)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem quotient_residual_fixed (source : LocalSource L R)
    (c : Vertex R) (hc : color R c = false) :
    quotientImage c (Q R c) ⊓ centralizer
      (quotientImage c (Ltilde R c) : Set (LocalQuotient c)) = ⊥ := by
  let := finite_stabilizer R c
  apply bot_unique
  rintro x ⟨⟨q,hq,rfl⟩,hfix⟩
  have hDE : ⁅denominator c,pResidual 2 (stabilizer R c)⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [denominator_eq]
    exact inf_le_right
  have hcomm : ∀ y ∈ pResidual 2 (stabilizer R c), ⁅q,y⁆ ∈ denominator c := by
    intro y hy
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientMap c ⁅q,y⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (hfix _ (mem_map_of_mem _ (show y ∈ (Ltilde R c).subgroupOf (stabilizer R c) by
      rw [Ltilde_subgroupOf]; exact hy))).symm
  have hfix' := centralizes_of_central_error ((Q R c).subgroupOf (stabilizer R c))
    (pResidual 2 (stabilizer R c)) (denominator c)
    (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
    (isPPerfect_pResidual 2) (by rw [denominator_eq]; exact inf_le_left) hDE q hq hcomm
  apply (QuotientGroup.eq_one_iff q).mpr
  rw [denominator_eq]
  exact ⟨hq,hfix'⟩

private theorem small_le_U (common : CommonFacts R source geometry)
    {a c : Vertex R} (hc : color R c = false) (f : FrameAt a c)
    (flag : SL) (side : Bool) (K : Subgroup (FreeAmalgam R))
    (hKQ : K ≤ Q R c) (hKe : IsElementaryAbelian 2 K) (hcard : Nat.card K ≤ 4)
    (hcomm : ⁅K,Ltilde R c⁆ ≤ Z R c)
    (hn : (parabolic f.sectionData.projection flag side).map (stabilizer R c).subtype ≤
      normalizer (K : Set (FreeAmalgam R)))
    (hnot : ¬ K ≤ fixedCore R c)
    (hf : (U R c).subgroupOf (stabilizer R c) ⊓
      centralizer (parabolic f.sectionData.projection flag side : Set (stabilizer R c)) = ⊥) :
    K ≤ U R c := by
  let S := stabilizer R c
  let := finite_stabilizer R c
  let π := f.projection
  let q := quotientMap c
  let P := parabolic f.sectionData.projection flag side
  let T := (pResidual 2 P).map P.subtype
  let K₀ := K.subgroupOf S
  let U₀ := (U R c).subgroupOf S
  let Q₁ := quotientImage c (Q R c)
  let Z₁ := quotientImage c (Z R c)
  let K₁ := quotientImage c K
  let E := quotientImage c (Ltilde R c)
  have hKS : K ≤ S := hKQ.trans (fun _ hx => hx.1)
  have hQS : Q R c ≤ S := fun _ hx => hx.1
  let : Finite K := Finite.of_injective (inclusion hKS) (inclusion_injective _)
  let : IsElementaryAbelian 2 K := hKe
  let : IsElementaryAbelian 2 K₀ := IsElementaryAbelian.subgroupOf hKS
  let : IsElementaryAbelian 2 K₁ := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (Z R c) := geometry.Z_elementary (by
    have := common.large_distance; omega) c hc
  let : IsElementaryAbelian 2 ((Z R c).subgroupOf S) :=
    IsElementaryAbelian.subgroupOf (Z_le_stabilizer R c)
  let : IsElementaryAbelian 2 Z₁ := IsElementaryAbelian.map _
  let : Q₁.Normal := quotientImage_normal c (Q R c) (Q_normalized R c)
  let : Z₁.Normal := quotientImage_normal c (Z R c) (Z_normalized R c)
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (U_normalized c)
  have hπ : Function.Surjective π :=
    quotientProjection_surjective c _ f.sectionData.module_section.projection_surjective _
  have hker : π.ker = Q₁ := quotientProjection_kernel c _ _
  have hP : P.map f.sectionData.projection = modelParabolic flag side :=
    map_comap_eq_self_of_surjective f.sectionData.module_section.projection_surjective _
  have hPq : P.map q = parabolic π flag side := by
    change ((modelParabolic flag side).comap (π.comp q)).map q = _
    rw [← comap_comap, map_comap_eq_self_of_surjective
      (show Function.Surjective q from QuotientGroup.mk'_surjective _)]
    rfl
  have hPN : P ≤ normalizer (K₀ : Set S) := by
    intro g hg
    exact (le_normalizer_comap S.subtype)
      (hn (mem_map_of_mem _ hg))
  have hPN₁ : parabolic π flag side ≤ normalizer (K₁ : Set (LocalQuotient c)) := by
    rw [← hPq]
    exact (map_mono hPN).trans (le_normalizer_map q)
  have hQN₁ : Q₁ ≤ normalizer (K₁ : Set (LocalQuotient c)) := by
    apply le_trans ?_ hPN₁
    rw [← hker]
    exact ker_le_comap _ _
  have hE : E = component π flag := by
    change quotientImage c (Ltilde R c) = component π flag
    rw [component, rankOne_parabolic_generation π hπ
      (quotientProjection_kernel_isPGroup source c hc _ _),
      quotientImage, Ltilde_subgroupOf, quotientMap,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  have hgen : E ⊔ Q₁ = ⊤ := by
    have hg := congrArg (fun H => quotientImage c H) (source.local_generation c hc)
    simp only [quotientImage] at hg
    rw [subgroupOf_sup (Ltilde_le_stabilizer c) hQS, Subgroup.map_sup,
      subgroupOf_self, map_top_of_surjective _
        (show Function.Surjective (quotientMap c) from QuotientGroup.mk'_surjective _)] at hg
    exact hg
  have hcard₁ : Nat.card K₁ ≤ 4 := by
    apply (Nat.le_of_dvd (Nat.card_pos (α := K₀)) (K₀.card_map_dvd q)).trans
    rw [Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv]
    exact hcard
  have hKE : ⁅K₁,E⁆ ≤ Z₁ := by
    rw [← quotientImage_commutator c K (Ltilde R c) hKS (Ltilde_le_stabilizer c)]
    exact map_mono (comap_mono hcomm)
  have hZQ : Z R c ≤ Q R c := (Z_le_VBall R c 2).trans
    (geometry.V_le_Q common.large_distance c hc)
  have hZcentral : Z₁ ≤ centralizer (Q₁ : Set (LocalQuotient c)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← quotientImage_commutator c (Z R c) (Q R c) (Z_le_stabilizer R c) hQS,
      geometry.centralizes c hc]
    simp [quotientImage]
  have himage : K₁ ≤ Z₁ := by
    apply small_residual_le_natural π hπ Q₁ E Z₁ K₁ hker
      (hE ▸ component_map π hπ flag) hgen (f.naturalZ common hc)
      (map_mono (comap_mono hZQ)) (map_mono (comap_mono hKQ))
      ((Q_isPGroup R source.two_group source.core_le c hc).comap_subtype.map q)
      hQN₁ hZcentral hKE (quotient_residual_fixed source c hc) flag side hcard₁
    exact (comap_mono (map_subtype_le _)).trans hPN₁
  have hfmodel : fixedSpace (markedParabolic f.naturalU.marking flag side) = ⊥ := by
    have hh := (natural_fixed_iff f.naturalU P).mp hf
    rw [hP] at hh
    exact hh
  have hTmodel : ((T.map q).map π).map (f.naturalZ common hc).marking.toMonoidHom =
      Matrix.PSL3Two.MarkedAutomorphisms.residual
        (markedParabolic f.naturalU.marking flag side) := by
    rw [map_map T π q]
    change (T.map f.sectionData.projection).map f.naturalU.marking.toMonoidHom = _
    rw [map_embedded_pResidual, map_embedded_pResidual, hP]
    rfl
  have hTfixed : Z₁ ⊓ centralizer (T.map q : Set (LocalQuotient c)) = ⊥ := by
    apply (natural_fixed_iff (f.naturalZ common hc) (T.map q)).mpr
    rw [hTmodel]
    exact marked_residual_fixed _ _ _ hfmodel
  have hTperfect : IsPPerfect 2 T := isPPerfect_embedded_pResidual 2 P
  have hKU : K₀ ≤ U₀ := by
    apply small_le_of_image_le q K₀ U₀ T
      (IsElementaryAbelian.isPGroup 2 K₀) hTperfect
      ((map_subtype_le _).trans hPN)
    · rw [Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv]
      exact hcard
    · exact himage.trans_eq (quotientImage_Z_eq_U (moduleFacts common) c hc)
    · change (quotientMap c).ker ≤ centralizer (T : Set S)
      rw [quotientMap, QuotientGroup.ker_mk', denominator_eq]
      exact inf_le_right.trans (centralizer_le (map_pResidual_le 2 P.subtype))
    · intro hz
      apply hnot
      apply (quotientImage_eq_bot_iff c K hKS).mp
      exact le_bot_iff.mp ((le_inf himage hz).trans hTfixed.le)
  intro k hk
  exact hKU (show (⟨k,hKS hk⟩ : S) ∈ K₀ from hk)

private theorem normalizer_centralizes_small {G : Type*} [Group G]
    (D : Subgroup G) [Finite D] (hD : Nat.card D ≤ 2) :
    normalizer (D : Set G) ≤ centralizer (D : Set G) := by
  by_cases hsmall : Nat.card D ≤ 1
  · rw [eq_bot_of_card_le D hsmall]
    intro g _ x hx
    have hxone : x = 1 := hx
    simp [hxone]
  · have htwo : Nat.card D = 2 := by omega
    obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp htwo
    intro g hg x hx
    by_cases hxone : x = 1
    · simp [hxone]
    let xD : D := ⟨x, hx⟩
    let yD : D := ⟨g * x * g⁻¹, (hg x).mp hx⟩
    have hyne : yD ≠ 1 := by
      intro hy
      apply hxone
      have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
      have hh := congrArg (fun a : G => g⁻¹ * a * g) hy'
      simpa [mul_assoc] using hh
    have heq : yD = xD := (hzuniq yD hyne).trans (hzuniq xD (by
      intro hx'; exact hxone (congrArg Subtype.val hx'))).symm
    have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
    have hh := congrArg (fun a : G => a * g) heq'
    simpa [mul_assoc] using hh.symm

/-- The normalized moving displacement is a plane in the actual natural U_c. -/
theorem ParabolicSeed.displacement_plane (common : CommonFacts R source geometry)
    {a c : Vertex R} (hb : 4 < geometry.b R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (f : FrameAt a c)
    (_hop : ¬ f.SameOrientation) (p : ParabolicSeed geometry f) :
    ⁅zpowers p.element,Q R c⁆ ≤ U R c ∧
      Nat.card (⁅zpowers p.element,Q R c⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  let K := ⁅zpowers p.element,Q R c⁆
  let D := ⁅Z R a,Q R c⁆
  have hKD : K ≤ D := commutator_mono (zpowers_le.mpr p.element_mem) le_rfl
  have hKa : K ≤ Z R a :=
    (hKD.trans (displacement_le_U common ha hd)).trans (U_le_Z R a)
  let := finite_stabilizer R a
  let : Finite D := Finite.of_injective
    (inclusion (((displacement_le_U common ha hd).trans (U_le_Z R a)).trans
      (Z_le_stabilizer R a))) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKD) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary (by omega) a ha
  have hKe : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le hKa
  have hcard : Nat.card K ≤ 4 :=
    (Nat.card_le_card_of_injective (inclusion hKD) (inclusion_injective _)).trans
      (displacement_card_le_four common ha hd)
  have hKW : K ≤ ⁅localZSpan R a c,Q R c⁆ := commutator_mono
    ((zpowers_le.mpr p.element_mem).trans (Z_le_localZSpan R a c)) le_rfl
  have hKQ : K ≤ Q R c := (hKW.trans (span_commutator_le_span a c)).trans
    ((span_le_kernel_intersection hc hd hb).trans inf_le_right)
  have hcomm : ⁅K,Ltilde R c⁆ ≤ Z R c :=
    (commutator_mono hKW le_rfl).trans f.triple_le_Z
  have hKU : K ≤ U R c := small_le_U common hc f p.flag p.side K hKQ hKe hcard
    hcomm p.displacement_normalized p.moving p.natural_fixed_eq_bot
  refine ⟨hKU, ?_⟩
  change Nat.card K = 4
  by_contra hne
  have htwo : Nat.card K ≤ 2 := by
    let : IsElementaryAbelian 2 K := hKe
    rcases (IsElementaryAbelian.isPGroup 2 K).card_eq_or_dvd with h | h <;> omega
  have hfix : K ≤ centralizer
      ((parabolic f.sectionData.projection p.flag p.side).map (stabilizer R c).subtype :
        Set (FreeAmalgam R)) := le_centralizer_iff.mp
    (p.displacement_normalized.trans (normalizer_centralizes_small K htwo))
  apply p.moving
  intro k hk
  have hkc : k ∈ stabilizer R c := (U_le_Z R c).trans (Z_le_stabilizer R c) (hKU hk)
  have he : (⟨k,hkc⟩ : stabilizer R c) = 1 := p.natural_fixed_eq_bot.le
    ⟨hKU hk, fun g hg => Subtype.ext (hfix hk g (mem_map_of_mem _ hg))⟩
  have hk1 : k = 1 := congrArg Subtype.val he
  simpa only [hk1] using (fixedCore R c).one_mem

/-- The supplied parabolic seed gives the initial edge identities and the
relative kernel centralizer product, via the actual natural plane. -/
theorem ParabolicSeed.edgeData_nonempty (common : CommonFacts R source geometry)
    {a c : Vertex R} (hb : 4 < geometry.b R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (f : FrameAt a c)
    (hop : ¬ f.SameOrientation) (p : ParabolicSeed geometry f) :
    Nonempty (EdgeData a c) := by
  obtain ⟨hU,hfour⟩ := p.displacement_plane common hb ha hc hd f hop
  exact p.toMovingSeed.edgeData_of_natural_plane common ha hc hU hfour

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
