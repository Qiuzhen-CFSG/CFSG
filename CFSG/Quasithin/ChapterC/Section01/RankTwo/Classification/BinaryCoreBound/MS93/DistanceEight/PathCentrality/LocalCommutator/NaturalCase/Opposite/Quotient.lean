module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Section
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.ModelProof.Transport

/-!
# The actual fixed quotient in the opposite branch of MS93 (4.4.1)

Write W = localZSpan R a c. Residual commutator idempotence extends the
supplied moving natural coordinates to all of W with kernel exactly W ∩ B_c.
The extension keeps the original marking. A noninner relative marking therefore
supplies contragredient coordinates on this full quotient, not just on a tagged
constituent.

The image `barSpan` of W in G_c/B_c is the source WB_c/B_c. It has order eight.
For a parabolic whose action on U_c has nonzero fixed space, opposite coordinates
prove that the fixed subgroup on this literal image is trivial. The actor's
image condition uses the same projection as the frame; the final version accepts
nonzero fixed space on the actual U_c subgroup.

This proves the fixed-quotient interpretation of the opposite orientation.
It does not choose the source parabolic or any critical continuation, and does
not exclude this orientation by itself. No trapped radius is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), pp.890--891.
The coordinate extension reuses the generic `sectionCoordinates` proof from
FirstPairing/Orientation/QuotientApplication/Verification/NaturalGeneration/Section.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
open RankOnePairing
open Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

namespace Opposite

omit [Finite M] in
private theorem fixed_subgroupOf (c : Vertex R) :
    (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c) =
      letI := geometry.Z_normal c
      centralizerModulo ((V R c).subgroupOf (stabilizer R c))
        (pResidual 2 (stabilizer R c)) ((Z R c).subgroupOf (stabilizer R c)) := by
  let := geometry.Z_normal c
  exact comap_map_eq_self_of_injective (stabilizer R c).subtype_injective _

omit [Finite M] in
/-- The fixed preimage is normal in the finite vertex stabilizer. -/
theorem fixed_normal (c : Vertex R) :
    ((B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)).Normal := by
  let := geometry.Z_normal c
  rw [fixed_subgroupOf (geometry := geometry)]
  change (((V R c).subgroupOf (stabilizer R c)) ⊓
    (centralizer ((pResidual 2 (stabilizer R c)).map
      (QuotientGroup.mk' ((Z R c).subgroupOf (stabilizer R c))) : Set _)).comap
        (QuotientGroup.mk' ((Z R c).subgroupOf (stabilizer R c)))).Normal
  let : ((V R c).subgroupOf (stabilizer R c)).Normal :=
    normal_subgroupOf_of_le_normalizer (V_normalized R c)
  let : ((pResidual 2 (stabilizer R c)).map
      (QuotientGroup.mk' ((Z R c).subgroupOf (stabilizer R c)))).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  infer_instance

omit [Finite M] in
/-- Restricting the actual fixed preimage to W gives its intrinsic fixed part. -/
theorem span_fixed_eq (hd : (cosetGraph R).dist a c = 2) :
    letI := geometry.Z_normal c
    centralizerModulo ((localZSpan R a c).subgroupOf (stabilizer R c))
      (pResidual 2 (stabilizer R c)) ((Z R c).subgroupOf (stabilizer R c)) =
      (localZSpan R a c ⊓ B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c) := by
  let := geometry.Z_normal c
  change _ = (localZSpan R a c).subgroupOf (stabilizer R c) ⊓
    (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)
  rw [fixed_subgroupOf (geometry := geometry)]
  ext x
  simp only [mem_inf, mem_centralizerModulo_iff]
  exact ⟨fun h => ⟨h.1, localZSpan_le_V R hd.le h.1, h.2⟩,
    fun h => ⟨h.1, h.2.2⟩⟩

/-- Coordinates on all of W, with kernel the actual intersection with B_c. -/
noncomputable def spanNatural (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) (f : FrameAt a c) :
    NaturalFactor f.sectionData.projection ⊤
      ((localZSpan R a c).subgroupOf (stabilizer R c))
      ((B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)) := by
  let S := stabilizer R c
  let := finite_stabilizer R c
  have hgen : pResidual 2 S ⊔ (Q R c).subgroupOf S = ⊤ := by
    apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le
      (show Q R c ≤ S from fun _ hx => hx.1)]
    change Ltilde R c ⊔ Q R c = (⊤ : Subgroup S).map S.subtype
    rw [source.local_generation c hc, ← MonoidHom.range_eq_map, range_subtype]
  let n := sectionCoordinates f.sectionData.module_section (isPPerfect_pResidual 2)
    (((source.V_isPGroup geometry hb c hc).to_le (localZSpan_le_V R hd.le)).comap_subtype) hgen
  refine { n with kernel := ?_ }
  rw [n.kernel, span_fixed_eq (geometry := geometry) hd]
  ext x
  exact and_iff_right x.property

@[simp] theorem spanNatural_marking (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) (f : FrameAt a c) :
    (spanNatural source hc hd hb f).marking = f.sectionData.module_section.natural.marking := rfl

/-- Opposite coordinates on W modulo B_c, preserving the reference action on U_c. -/
noncomputable def spanDual (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (h : ¬ f.SameOrientation) :
    DualFactor f.sectionData.projection ⊤
      ((localZSpan R a c).subgroupOf (stabilizer R c))
      ((B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c))
      ((U R c).subgroupOf (stabilizer R c)) f.naturalU :=
  Escape.PairingControl.FirstPairing.Orientation.dualFactorOfNotInner f.naturalU
    (spanNatural source hc hd hb f) h

open RankOnePairing.Incidence
open FixedGeometry.ValueConstruction

private theorem dual_fixed_eq_bot_of_fixed (σ : MulAut SL) (flag : SL) (i : Bool)
    (hf : fixedSpace (markedParabolic σ flag i) ≠ ⊥) :
    fixedSpace (markedParabolic (DualGeometry.dualMark σ) flag i) = ⊥ := by
  obtain ⟨k, ⟨hp, _⟩ | ⟨hp, _⟩⟩ := ModelProof.marked_pair σ flag i
  · rw [DualGeometry.ModelProof.dual_marked, hp,
      DualGeometry.ModelProof.map_graph_conj,
      Matrix.PSL3Two.MarkedAutomorphisms.pointParabolic_map_diagram,
      ModelProof.fixedSpace_conj, ModelProof.line_fixed_bot, Subgroup.map_bot]
  · exact False.elim (hf (by
      rw [hp, ModelProof.fixedSpace_conj, ModelProof.line_fixed_bot, Subgroup.map_bot]))

private theorem fixed_modulo_le_kernel {G : Type*} [Group G]
    {π : G →* SL} {H N P : Subgroup G} [N.Normal]
    (n : NaturalFactor π ⊤ H N) (flag : SL) (i : Bool)
    (hP : P.map π = modelParabolic flag i)
    (hf : fixedSpace (markedParabolic n.marking flag i) = ⊥) :
    centralizerModulo H P N ≤ N := by
  intro x hx
  obtain ⟨hxH, hxfix⟩ := mem_centralizerModulo_iff.mp hx
  let x' : H := ⟨x, hxH⟩
  have hfixed : n.coordinates x' ∈ fixedSpace (markedParabolic n.marking flag i) := by
    rintro g ⟨v, hv, rfl⟩
    obtain ⟨l, hl, he⟩ := hP.symm ▸ hv
    let y : H := ⟨l * x * l⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top _)) _).mp hxH⟩
    have hk : y * x'⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      exact hxfix l hl
    have heq : n.coordinates y = n.coordinates x' := by
      apply mul_inv_eq_one.mp
      simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hk
    have hact := n.action l (mem_top _) x' y rfl
    rw [heq, he] at hact
    exact hact.symm
  have hk : x' ∈ n.coordinates.ker := mem_bot.mp (hf.le hfixed)
  rw [n.kernel] at hk
  exact hk

theorem span_fixed_modulo_le (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (h : ¬ f.SameOrientation)
    (P : Subgroup (stabilizer R c)) (flag : SL) (i : Bool)
    (hP : P.map f.sectionData.projection = modelParabolic flag i)
    (hf : fixedSpace (markedParabolic f.naturalU.marking flag i) ≠ ⊥) :
    letI := fixed_normal (geometry := geometry) c
    centralizerModulo ((localZSpan R a c).subgroupOf (stabilizer R c)) P
      ((B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)) ≤
      (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c) := by
  let := fixed_normal (geometry := geometry) c
  exact fixed_modulo_le_kernel (spanDual source hc hd hb f h).graphNatural flag i hP
    (dual_fixed_eq_bot_of_fixed f.naturalU.marking flag i hf)

noncomputable abbrev FixedQuotient (geometry : Geometry R) (c : Vertex R) :=
  letI := fixed_normal (geometry := geometry) c
  stabilizer R c ⧸ (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)

noncomputable instance fixedQuotient_group (geometry : Geometry R) (c : Vertex R) :
    Group (FixedQuotient geometry c) :=
  letI := fixed_normal (geometry := geometry) c
  inferInstanceAs (Group (stabilizer R c ⧸
    (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)))

noncomputable abbrev fixedQuotientMap (geometry : Geometry R) (c : Vertex R) :
    stabilizer R c →* FixedQuotient geometry c :=
  letI := fixed_normal (geometry := geometry) c
  QuotientGroup.mk' _

/-- The literal source subgroup WB_c/B_c inside G_c/B_c. -/
noncomputable def barSpan (geometry : Geometry R) (a c : Vertex R) :
    Subgroup (FixedQuotient geometry c) :=
  ((localZSpan R a c).subgroupOf (stabilizer R c)).map (fixedQuotientMap geometry c)

/-- The fixed quotient is genuinely isomorphic to the binary three-space. -/
noncomputable def barSpanEquiv (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) (f : FrameAt a c) :
    barSpan geometry a c ≃* Multiplicative (Fin 3 → ZMod 2) := by
  let := fixed_normal (geometry := geometry) c
  let W := (localZSpan R a c).subgroupOf (stabilizer R c)
  let Bc := (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)
  let q := (fixedQuotientMap geometry c).subgroupMap W
  have hker : q.ker = Bc.subgroupOf W := by
    ext x
    change q x = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  let e := QuotientGroup.quotientKerEquivOfSurjective q
    ((fixedQuotientMap geometry c).subgroupMap_surjective W)
  exact e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans
    (spanNatural source hc hd hb f).quotientEquiv)

theorem barSpan_card (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) (f : FrameAt a c) :
    Nat.card (barSpan geometry a c) = 8 := by
  rw [Nat.card_congr (barSpanEquiv source hc hd hb f).toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

omit [Finite M] in
theorem barSpan_eq_product_image :
    barSpan geometry a c =
      (((localZSpan R a c).subgroupOf (stabilizer R c)) ⊔
        (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)).map
          (fixedQuotientMap geometry c) := by
  let := fixed_normal (geometry := geometry) c
  rw [Subgroup.map_sup]
  have hB : ((B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)).map
      (fixedQuotientMap geometry c) = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr hx
  rw [hB, sup_bot_eq]
  rfl

theorem barSpan_fixed_eq_bot (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (h : ¬ f.SameOrientation)
    (P : Subgroup (stabilizer R c)) (flag : SL) (i : Bool)
    (hP : P.map f.sectionData.projection = modelParabolic flag i)
    (hf : fixedSpace (markedParabolic f.naturalU.marking flag i) ≠ ⊥) :
    barSpan geometry a c ⊓ centralizer
      (P.map (fixedQuotientMap geometry c) : Set (FixedQuotient geometry c)) = ⊥ := by
  let := fixed_normal (geometry := geometry) c
  apply le_bot_iff.mp
  rintro y ⟨⟨x, hx, rfl⟩, hfix⟩
  apply (QuotientGroup.eq_one_iff _).mpr
  apply span_fixed_modulo_le source hc hd hb f h P flag i hP hf
  exact ⟨hx, hfix⟩

private theorem model_fixed_of_actual {G : Type*} [Group G]
    {π : G →* SL} {U P : Subgroup G}
    (n : NaturalFactor π ⊤ U ⊥) (flag : SL) (i : Bool)
    (hP : P.map π = modelParabolic flag i)
    (hf : U ⊓ centralizer (P : Set G) ≠ ⊥) :
    fixedSpace (markedParabolic n.marking flag i) ≠ ⊥ := by
  let := (Subgroup.nontrivial_iff_ne_bot _).mpr hf
  obtain ⟨x, hx, hne⟩ := (U ⊓ centralizer (P : Set G)).exists_ne_one_of_nontrivial
  let u : U := ⟨x, hx.1⟩
  have hfixed : n.coordinates u ∈ fixedSpace (markedParabolic n.marking flag i) := by
    rintro g ⟨v, hv, rfl⟩
    obtain ⟨l, hl, he⟩ := hP.symm ▸ hv
    have hconj : (u : G) = l * (u : G) * l⁻¹ := by
      rw [hx.2 l hl, mul_inv_cancel_right]
    have hh := n.action l (mem_top _) u u hconj
    rw [he] at hh
    exact hh.symm
  intro hbot
  have hone : n.coordinates u = 1 := mem_bot.mp (hbot.le hfixed)
  have hu : u = 1 := n.equivOfBot.injective (hone.trans (map_one _).symm)
  exact hne (congrArg Subtype.val hu)

/-- A parabolic fixing U_c has zero fixed space on WB_c/B_c in the opposite orientation. -/
theorem barSpan_fixed_eq_bot_of_actual (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (h : ¬ f.SameOrientation)
    (P : Subgroup (stabilizer R c)) (flag : SL) (i : Bool)
    (hP : P.map f.sectionData.projection = modelParabolic flag i)
    (hf : (U R c).subgroupOf (stabilizer R c) ⊓
      centralizer (P : Set (stabilizer R c)) ≠ ⊥) :
    barSpan geometry a c ⊓ centralizer
      (P.map (fixedQuotientMap geometry c) : Set (FixedQuotient geometry c)) = ⊥ :=
  barSpan_fixed_eq_bot source hc hd hb f h P flag i hP
    (model_fixed_of_actual f.naturalU flag i hP hf)

end Opposite
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
