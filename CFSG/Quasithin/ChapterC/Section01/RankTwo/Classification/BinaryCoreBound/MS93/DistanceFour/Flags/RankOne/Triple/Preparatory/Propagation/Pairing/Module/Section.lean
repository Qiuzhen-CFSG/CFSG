module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Inputs

/-!
# The literal fixed denominator of the midpoint span

The seed commutator bound makes the radical in the single natural section
exactly Z_alpha. On its global fixed preimage, two-residual commutator
idempotence improves fixation modulo Z_alpha to fixation modulo U_alpha.
Conversely, generation by the component and the quotient kernel gives the
full fixed condition. Thus the denominator required by (1.7) is identified
without replacing it by an assumed quotient kernel.

The direct-sum decomposition then extends the actual moving coordinates to
the whole span, with the same marking and conjugation equation. The edge
index and the bad midpoint triple show that the midpoint image modulo
Z_alpha has order two. Selecting its parabolic orientation and transporting
that line remain separate representation arguments.

Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
(4.6.8), claim (2), printed p.906; (1.7), pp.847--848.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
/-- Extend moving coordinates across a normal summand on which they vanish.
The intersection is the exact intrinsic kernel, and the extended map retains
the original marking and the action of every ambient element. -/
noncomputable def extendNaturalAcrossFixed {G : Type*} [Group G] {π : G →* SL}
    {A H N C : Subgroup G} [C.Normal]
    (n : NaturalFactor π ⊤ A N) (hcover : H = A ⊔ C)
    (hinter : A ⊓ C = N) (hH : (⊤ : Subgroup G) ≤ normalizer H) :
    NaturalFactor π ⊤ H C := by
  have hAH : A ≤ H := hcover ▸ le_sup_left
  have hCH : C ≤ H := hcover ▸ le_sup_right
  have factor (x : H) : ∃ a : A, ∃ c : C, (a : G) * (c : G) = x := by
    obtain ⟨a, ha, c, hc, he⟩ := mem_sup_of_normal_right.mp (show (x : G) ∈ A ⊔ C from by rw [← hcover]; exact x.property)
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, he⟩
  let q := QuotientGroup.mk' (C.subgroupOf H)
  let f := q.comp (inclusion hAH)
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf H) v
    obtain ⟨a, c, he⟩ := factor x
    refine ⟨a, ?_⟩
    change q (inclusion hAH a) = q x
    have he' : inclusion hAH a * inclusion hCH c = x := Subtype.ext he
    have hc : q (inclusion hCH c) = 1 := (QuotientGroup.eq_one_iff _).mpr c.property
    rw [← he', map_mul, hc, mul_one]
  have hk : f.ker ≤ n.coordinates.ker := by
    intro a ha
    rw [n.kernel]
    have hc : inclusion hAH a ∈ C.subgroupOf H := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact ha
    change (a : G) ∈ N
    rw [← hinter]
    exact ⟨a.property, hc⟩
  let F := f.liftOfSurjective hf ⟨n.coordinates, hk⟩
  let coordinates := F.comp q
  have hA (a : A) : coordinates (inclusion hAH a) = n.coordinates a :=
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨n.coordinates, hk⟩ a
  have hC (c : C) : coordinates (inclusion hCH c) = 1 := by
    change F (q (inclusion hCH c)) = 1
    rw [show q (inclusion hCH c) = 1 from (QuotientGroup.eq_one_iff _).mpr c.property,
      map_one]
  have hproduct (x : H) (a : A) (c : C) (he : (a : G) * (c : G) = x) :
      coordinates x = n.coordinates a := by
    have he' : inclusion hAH a * inclusion hCH c = x := Subtype.ext he
    rw [← he', map_mul, hA, hC, mul_one]
  refine {
    marking := n.marking
    coordinates := coordinates
    surjective := ?_
    kernel := ?_
    normalized := hH
    action := ?_ }
  · intro v
    obtain ⟨a, ha⟩ := n.surjective v
    exact ⟨inclusion hAH a, (hA a).trans ha⟩
  · ext x
    change coordinates x = 1 ↔ (x : G) ∈ C
    obtain ⟨a, c, he⟩ := factor x
    rw [hproduct x a c he, ← MonoidHom.mem_ker, n.kernel]
    change (a : G) ∈ N ↔ (x : G) ∈ C
    constructor
    · intro ha
      rw [← hinter] at ha
      rw [← he]
      exact C.mul_mem ha.2 c.property
    · intro hx
      have ha : (a : G) ∈ C := by
        have hh := C.mul_mem hx (C.inv_mem c.property)
        rwa [← he, mul_inv_cancel_right] at hh
      rw [← hinter]
      exact ⟨a.property, ha⟩
  · intro l hl x y hy
    obtain ⟨a, c, he⟩ := factor x
    let a' : A := ⟨l * (a : G) * l⁻¹,
      (mem_normalizer_iff.mp (n.normalized hl) _).mp a.property⟩
    let c' : C := ⟨l * (c : G) * l⁻¹, (inferInstance : C.Normal).conj_mem _ c.property l⟩
    have he' : (a' : G) * (c' : G) = y := by
      change (l * (a : G) * l⁻¹) * (l * (c : G) * l⁻¹) = (y : G)
      rw [hy, ← he]
      group
    change (coordinates y).toAdd = _
    rw [hproduct y a' c' he', hproduct x a c he]
    exact n.action l hl a a' rfl


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The literal inverse image of the globally fixed part of V₀/Z_alpha. -/
noncomputable def fixedLayer (p : FlagCriticalData source geometry i) : Subgroup M :=
  centralizerModulo (spanLayer p) ⊤ (centralLayer (R := R))

instance fixedLayer_normal (p : FlagCriticalData source geometry i) :
    (fixedLayer p).Normal := by
  unfold fixedLayer centralizerModulo
  rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  infer_instance

/-- The seed hypothesis controls the action of the original quotient kernel. -/
theorem spanLayer_kernel_commutator (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) :
    ⁅spanLayer p, source.projection.ker⁆ ≤ naturalLayer (R := R) := by
  apply (map_le_map_iff_of_injective (embedM_injective R)).mp
  rw [map_commutator, map_spanLayer common p, map_naturalLayer,
    source.projection_kernel, ← Q_alpha R source.two_group source.core_le]
  exact span_commutator_le_U common p hseed

/-- The radical of the supplied single section is exactly Z_alpha. -/
theorem radical_eq_centralLayer (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) :
    Escape.radicalPreimage source.projection.ker (spanLayer p)
      (centralLayer (R := R)) = centralLayer (R := R) := by
  exact sup_eq_left.mpr ((spanLayer_kernel_commutator common p hseed).trans
    (comap_mono (U_le_Z _)))

omit [Finite M] in
private theorem fixedLayer_commutator_le (p : FlagCriticalData source geometry i)
    (A : Subgroup M) : ⁅fixedLayer p, A⁆ ≤ centralLayer (R := R) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha x hx
  exact (mem_centralizerModulo_iff.mp hx).2 a (mem_top a)

/-- The source fixed preimage modulo U_alpha equals the fixed part modulo
Z_alpha, for every actual conjugate seed. -/
theorem fixedPreimage_eq_fixedLayer (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) (g : M) :
    fixedPreimage (component source.projection source.flag) (seed p g)
      (naturalLayer (R := R)) = fixedLayer p := by
  let C := fixedPreimage (component source.projection source.flag) (seed p g)
    (naturalLayer (R := R))
  have hCL : ⁅C, component source.projection source.flag⁆ ≤ naturalLayer (R := R) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl c hc
    exact (mem_fixedPreimage _ _ _ c).mp hc |>.2 l hl
  have hCS : C ≤ spanLayer p := by
    intro x hx
    have hh := (mem_fixedPreimage _ _ _ x).mp hx |>.1
    rwa [generated_seed common p g] at hh
  have hCQ : ⁅C, source.projection.ker⁆ ≤ naturalLayer (R := R) :=
    (commutator_mono hCS le_rfl).trans (spanLayer_kernel_commutator common p hseed)
  have hgen : component source.projection source.flag ⊔ source.projection.ker = ⊤ := by
    have hh := component_sup_extensionCore (pairingExtension source)
    simpa only [pairingExtension_projection, pairingExtension_flag, pairing_core] using hh
  have hCA : ⁅C, (⊤ : Subgroup M)⁆ ≤ naturalLayer (R := R) := by
    have ht : (⊤ : Subgroup M) ≤ commutatorPreimage ⊤ C (naturalLayer (R := R)) := by
      apply hgen.ge.trans
      exact sup_le (le_commutatorPreimage le_top (by rwa [commutator_comm]))
        (le_commutatorPreimage le_top (by rwa [commutator_comm]))
    rw [commutator_comm]
    exact (commutator_mono ht le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  apply le_antisymm
  · intro x hx
    exact mem_centralizerModulo_iff.mpr ⟨hCS hx, fun a ha =>
      comap_mono (U_le_Z _) ((commutator_comm C (⊤ : Subgroup M) ▸ hCA)
        (commutator_mem_commutator ha hx))⟩
  · have hc : component source.projection source.flag = pResidual 2 M := by
      rw [component, source.rank_one_generation, source.residual]
    have hp : IsPGroup 2 (fixedLayer p) :=
      (extensionCore_isPGroup source.projection).to_le
        ((centralizerModulo_le _ _ _).trans
          ((comap_mono (span_le_radius p)).trans (radiusLayer_le_core common)))
    have hid := commutator_isPPerfect_idempotent (pResidual 2 M) (fixedLayer p)
      (isPPerfect_pResidual 2) hp le_normalizer_of_normal
    have hZL : ⁅centralLayer (R := R), component source.projection source.flag⁆ ≤
        naturalLayer (R := R) := by
      apply (map_le_map_iff_of_injective (embedM_injective R)).mp
      rw [map_commutator, map_centralLayer, map_component, map_naturalLayer]
      exact le_rfl
    have hbound : ⁅fixedLayer p, component source.projection source.flag⁆ ≤
        naturalLayer (R := R) := by
      rw [← hc] at hid
      rw [← hid]
      exact (commutator_mono (fixedLayer_commutator_le p _) le_rfl).trans hZL
    intro x hx
    apply (mem_fixedPreimage _ _ _ x).mpr
    refine ⟨?_, fun l hl => (commutator_comm (fixedLayer p) (component source.projection source.flag) ▸ hbound)
      (commutator_mem_commutator hl hx)⟩
    rw [generated_seed common p g]
    exact (mem_centralizerModulo_iff.mp hx).1


/-- The midpoint has a nonzero one-dimensional image modulo Z_alpha. -/
theorem middleLayer_index (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i) :
    (centralLayer (R := R)).relIndex (middleLayer p) = 2 := by
  have hle : (centralLayer (R := R)).relIndex (middleLayer p) ≤ 2 := by
    change ((Z R (alpha R)).comap (embedM R)).relIndex (middleLayer p) ≤ 2
    rw [relIndex_comap, map_middleLayer common p]
    have hi := early.edge_Z_index p.middle (beta R) p.middle_color
      (adjacent_symm R p.middle_neighbor)
    exact (relIndex_le_of_le_left
      (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
      (show (Z R (beta R)).relIndex (Z R p.middle) ≠ 0 by rw [hi]; decide)).trans_eq hi
  have hne : (centralLayer (R := R)).relIndex (middleLayer p) ≠ 1 := by
    intro he
    apply middle_commutator_ne_bot common p
    exact commutator_eq_bot_iff_le_centralizer.mpr
      ((relIndex_eq_one.mp he).trans (centralLayer_centralizes_radius common))
  have hpos : (centralLayer (R := R)).relIndex (middleLayer p) ≠ 0 :=
    index_ne_zero_of_finite
  omega


/-- Genuine natural coordinates on V₀ modulo its fixed part, obtained from
the supplied splitting and retaining the original quotient marking. -/
noncomputable def singleSectionCoordinates (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (hs : SingleSection p) : NaturalFactor source.projection ⊤ (spanLayer p) (fixedLayer p) := by
  let s : Escape.SingleNaturalSection source.projection source.projection.ker
      (pResidual 2 M) (spanLayer p) (centralLayer (R := R)) := Classical.choice hs
  have hr := radical_eq_centralLayer common p hseed
  have hn : NaturalFactor source.projection ⊤
      (centralLayer (R := R) ⊔ ⁅spanLayer p, (⊤ : Subgroup M)⁆) (centralLayer (R := R)) := by
    simpa only [Escape.movingPreimage, hr] using s.natural
  have hcover : spanLayer p =
      (centralLayer (R := R) ⊔ ⁅spanLayer p, (⊤ : Subgroup M)⁆) ⊔ fixedLayer p := by
    simpa only [Escape.movingPreimage, hr, fixedLayer] using s.decomposition
  have hinter : (centralLayer (R := R) ⊔ ⁅spanLayer p, (⊤ : Subgroup M)⁆) ⊓
      fixedLayer p = centralLayer (R := R) := by
    simpa only [Escape.movingPreimage, hr, fixedLayer] using s.intersection
  exact extendNaturalAcrossFixed hn hcover hinter le_normalizer_of_normal

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
