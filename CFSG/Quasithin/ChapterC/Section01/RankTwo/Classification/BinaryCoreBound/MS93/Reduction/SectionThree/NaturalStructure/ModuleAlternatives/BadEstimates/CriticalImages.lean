module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Basic

public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Critical endpoint images from edge offender rigidity

For each critical pair, the two displacement indices are equal. Indeed, the
marked edge rigidity excludes strict offenders. The order of an elementary
endpoint image is the opposite displacement index, while its fixed codimension
is the binary logarithm of the forward displacement index. Transport to alpha
therefore gives one inequality; critical reversal gives the other.

Consequently every opposite endpoint image is an offender. Uniqueness makes
that image normal in the edge image and identifies all endpoints through the
same edge. Taking preimages under the actual local projection gives the joins
with Q required by `CriticalImageControl`. All actions here are genuine
conjugation actions, and the projection kernel is retained throughout.

The conclusion is conditional on `EdgeOffenderUniqueness`; it does not prove
the bad-case module calculation supplying that premise.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of (2.2)(vi), (2.3)(d), and the initial argument of (3.8),
printed pp.857 and 877.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CriticalImages
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private noncomputable def image (source : LocalSource L R) (E : Subgroup (FreeAmalgam R)) : Subgroup SL :=
  (E.subgroupOf (stabilizer R (alpha R))).map (baseProjection source)

/-- The image order is the relative index with the actual projection kernel. -/
private theorem image_card (source : LocalSource L R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) :
    Nat.card (image source E) = (Q R (alpha R)).relIndex E := by
  rw [image, ← relIndex_ker, baseProjection_kernel, subgroupOf, relIndex_comap,
    map_subgroupOf_eq_of_le hE]

private theorem action_apply (source : LocalSource L R)
    (s : stabilizer R (alpha R)) (x : X R (alpha R)) :
    (xAction source (baseProjection source s) x : FreeAmalgam R) = s * x * (s : FreeAmalgam R)⁻¹ := by
  obtain ⟨m, rfl⟩ := (baseEquiv (R := R)).surjective s
  rw [baseProjection_baseEquiv, xAction, layerAction_apply, baseEquiv_val]

/-- Fixed vectors are exactly the subgroup centralizing the endpoint layer. -/
private theorem image_fixedCodim (source : LocalSource L R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) :
    letI := X_elementary R (alpha R)
    2 ^ fixedCodim (Offenders.linearize (xAction source)) (image source E) =
      Offenders.displacement (X R (alpha R)) E := by
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  let Y := X R (alpha R)
  let ρ := Offenders.linearize (xAction source)
  let C := (centralizer (E : Set (FreeAmalgam R))).subgroupOf Y
  have hfix (v : Additive Y) : v ∈ fixedSpace ρ (image source E) ↔ v.toMul ∈ C := by
    constructor
    · intro hv e he
      have hh := congrArg (fun w : Additive Y => (w.toMul : FreeAmalgam R))
        (hv ⟨baseProjection source ⟨e, hE he⟩, ⟨⟨e, hE he⟩, he, rfl⟩⟩)
      change (xAction source (baseProjection source ⟨e, hE he⟩) v.toMul : FreeAmalgam R) = _ at hh
      rw [action_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hv g
      obtain ⟨s, hs, he⟩ := g.property
      apply Additive.toMul.injective
      apply Subtype.ext
      change (xAction source g.val v.toMul : FreeAmalgam R) = _
      rw [← he, action_apply]
      have hc : (s : FreeAmalgam R) * (v.toMul : FreeAmalgam R) = v.toMul * s := hv s hs
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  let e : fixedSpace ρ (image source E) ≃ C := {
    toFun := fun v => ⟨v.val.toMul, (hfix v.val).mp v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, (hfix _).mpr x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (image source E)) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (image source E))
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hY : Nat.card Y = 2 ^ Module.finrank (ZMod 2) (Additive Y) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Y)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ (image source E)
  have hmul := C.card_mul_index
  rw [hC, hY, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ (image source E))] at hmul
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hmul).symm

private theorem image_elementary (source : LocalSource L R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) (hne : ¬ E ≤ Q R (alpha R))
    [IsElementaryAbelian 2 E] : IsElementaryTwo (image source E) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := IsElementaryAbelian.subgroupOf (p := 2) hE
  refine ⟨?_, IsElementaryAbelian.map (baseProjection source)⟩
  intro h
  have hk := (Subgroup.map_eq_bot_iff _).mp h
  rw [baseProjection_kernel] at hk
  exact hne (fun e he => hk (show (⟨e, hE he⟩ : stabilizer R (alpha R)) ∈ E.subgroupOf _ from he))

/-- Absence of strict offenders gives the reverse cardinal inequality. -/
private theorem index_le_displacement (source : LocalSource L R) (hu : EdgeOffenderUniqueness source)
    (t : Vertex R) (hat : Adjacent R (alpha R) t)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ Q R t) (hne : ¬ E ≤ Q R (alpha R))
    [IsElementaryAbelian 2 E] :
    (Q R (alpha R)).relIndex E ≤ Offenders.displacement (X R (alpha R)) E := by
  let := X_elementary R (alpha R)
  have hES : E ≤ stabilizer R (alpha R) := fun x hx => (hE hx).2 _ (adjacent_symm R hat)
  have helem := image_elementary source E hES hne
  have hle : image source E ≤ edgeActor source t := map_mono (comap_mono hE)
  have h := edgeActor_rank_le_fixedCodim source hu t hat _ hle helem
  rw [← image_card source E hES, helem.card_eq_two_pow_rank, ← image_fixedCodim source E hES]
  exact Nat.pow_le_pow_right (by decide) h


/-- Taking the full preimage restores precisely the join with Q. -/
private theorem image_preimage (source : LocalSource L R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) :
    ((image source E).comap (baseProjection source)).map (stabilizer R (alpha R)).subtype =
      E ⊔ Q R (alpha R) := by
  rw [image, comap_map_eq, Subgroup.map_sup, baseProjection_kernel,
    map_subgroupOf_eq_of_le hE, map_subgroupOf_eq_of_le (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1)]

private theorem image_normalizer_lift (source : LocalSource L R) (E T : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R (alpha R)) (hT : T ≤ stabilizer R (alpha R))
    (hn : image source T ≤ normalizer (image source E : Set SL)) :
    T ≤ normalizer ((E ⊔ Q R (alpha R) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have h : T.subgroupOf (stabilizer R (alpha R)) ≤
      normalizer ((image source E).comap (baseProjection source) : Set (stabilizer R (alpha R))) :=
    ((map_le_iff_le_comap).mp hn).trans (le_normalizer_comap _)
  have hh := (map_mono h).trans (le_normalizer_map (stabilizer R (alpha R)).subtype)
  rwa [map_subgroupOf_eq_of_le hT, image_preimage source E hE] at hh



/-- The edge centralizer identifies the opposite displacement kernel with Q. -/
private theorem critical_edge_data (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false) (b : Vertex R)
    (hc : CriticalPair R a b (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b) :
    X R b ≤ Q R t ∧ ¬ X R b ≤ Q R a ∧
      Offenders.displacement (X R b) (X R a) = (Q R a).relIndex (X R b) := by
  have hbcol := critical_endpoint_color R a ha _ hc
  have htcol : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hNT : Q R a ≤ Q R t := Q_le_adjacent_h R htcol hat
  have hsmall : (cosetGraph R).dist b t < criticalDistance R b (geometry.exists_critical b hbcol) := by
    rw [SimpleGraph.dist_comm, geometry.distance_constant b hbcol, ← geometry.distance_constant a ha]
    have hd := hc.1
    omega
  have hE : X R b ≤ Q R t :=
    X_le_Q_of_dist_lt R geometry (source.edgeCentralizerCondition geometry) b hbcol t hsmall
  have hCY : Q R t ⊓ centralizer (X R a : Set (FreeAmalgam R)) = Q R a := by
    apply le_antisymm
    · calc
        _ ≤ Q R t ⊓ centralizer (Z R a : Set (FreeAmalgam R)) :=
          inf_le_inf_left _ (centralizer_le (geometry.omega_bound a ha (by
            rw [geometry.distance_constant a ha]; exact hb)))
        _ = _ := source.edgeCentralizerCondition geometry a t ha hat
    · exact le_inf hNT (Q_le_centralizer_X R a)
  refine ⟨hE, fun h => (critical_endpoint_choice source geometry hb a ha b hc).2
    ((critical_endpoint_choice source geometry hb a ha b hc).1.trans h), ?_⟩
  have he : X R b ⊓ centralizer (X R a : Set (FreeAmalgam R)) = X R b ⊓ Q R a := by
    rw [← hCY, ← inf_assoc, inf_of_le_left hE]
  unfold Offenders.displacement
  rw [← inf_relIndex_left (X R b), he, inf_relIndex_left]

omit [Finite M] in
private theorem exists_to_alpha (a : Vertex R) (ha : color R a = false) :
    ∃ f : FreeAmalgam R, act R f a = alpha R := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  exact ⟨g⁻¹, by simp only [act_mVertex, mul_inv_cancel]; rfl⟩

private theorem critical_displacement_le (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source)
    (a : Vertex R) (ha : color R a = false) (b : Vertex R)
    (hc : CriticalPair R a b (geometry.exists_critical a ha)) :
    Offenders.displacement (X R b) (X R a) ≤ Offenders.displacement (X R a) (X R b) := by
  obtain ⟨t, hat, ht⟩ := exists_adjacent_dist_sub_one R a b (by
    rw [hc.1, geometry.distance_constant a ha]; exact hb)
  obtain ⟨f, hf⟩ := exists_to_alpha a ha
  have hfcol : color R (act R f a) = false := by rw [hf]; rfl
  have hc' := (criticalPair_act_iff R f a b (geometry.exists_critical a ha)
    (geometry.exists_critical (act R f a) hfcol)).mpr hc
  have hat' := (adjacent_act_iff R f a t).mpr hat
  have ht' : (cosetGraph R).dist (act R f t) (act R f b) + 1 =
      (cosetGraph R).dist (act R f a) (act R f b) := by
    simpa only [dist_act] using ht
  have hcmp : Offenders.displacement (X R (act R f b)) (X R (act R f a)) ≤
      Offenders.displacement (X R (act R f a)) (X R (act R f b)) := by
    simp only [hf] at hc' hat' ht' ⊢
    obtain ⟨hE, hne, hi⟩ := critical_edge_data source geometry hb (alpha R) rfl
      (act R f b) hc' (act R f t) hat' ht'
    rw [hi]
    let := X_elementary R (act R f b)
    exact index_le_displacement source hu _ hat' _ hE hne
  simpa only [X_act, Offenders.displacement_map] using hcmp

/-- The two critical displacement indices coincide under edge offender rigidity. -/
theorem critical_displacement_eq (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source)
    (a : Vertex R) (ha : color R a = false) (b : Vertex R)
    (hc : CriticalPair R a b (geometry.exists_critical a ha)) :
    Offenders.displacement (X R a) (X R b) = Offenders.displacement (X R b) (X R a) := by
  have hbcol := critical_endpoint_color R a ha _ hc
  exact le_antisymm
    (critical_displacement_le source geometry hb hu b hbcol a
      (source.critical_reverse geometry a ha b hbcol hc))
    (critical_displacement_le source geometry hb hu a ha b hc)



/-- After reciprocity, the actual opposite endpoint image is an offender. -/
private theorem critical_image_offender (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source) (b : Vertex R)
    (hc : CriticalPair R (alpha R) b (geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) (hat : Adjacent R (alpha R) t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist (alpha R) b) :
    letI := X_elementary R (alpha R)
    IsOffender (Offenders.linearize (xAction source)) (image source (X R b)) := by
  let := X_elementary R (alpha R)
  let := X_elementary R b
  obtain ⟨hE, hne, hi⟩ := critical_edge_data source geometry hb (alpha R) rfl b hc t hat ht
  have hES : X R b ≤ stabilizer R (alpha R) :=
    fun x hx => (hE hx).2 _ (adjacent_symm R hat)
  have helem := image_elementary source (X R b) hES hne
  refine ⟨helem, ?_⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [image_fixedCodim source _ hES, ← helem.card_eq_two_pow_rank, image_card source _ hES,
    critical_displacement_eq source geometry hb hu (alpha R) rfl b hc, hi]

/-- Conjugacy preserves offenders, so uniqueness forces relative normality. -/
private theorem offender_normalized (source : LocalSource L R) (hu : EdgeOffenderUniqueness source)
    (t : Vertex R) (hat : Adjacent R (alpha R) t) (B : Subgroup SL)
    (hB : B ≤ edgeActor source t) :
    letI := X_elementary R (alpha R)
    IsOffender (Offenders.linearize (xAction source)) B →
      edgeActor source t ≤ normalizer (B : Set SL) := by
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  intro hoff g hg
  obtain ⟨A, _, _, huniq, _⟩ := hu t hat
  rw [mem_normalizer_iff_map_conj_eq]
  change B.map (MulAut.conj g).toMonoidHom = B
  apply (huniq _ ?_ ?_).trans (huniq B hB hoff).symm
  · have h := map_mono (f := (MulAut.conj g).toMonoidHom) hB
    exact h.trans_eq (mem_normalizer_iff_map_conj_eq.mp ((edgeActor source t).le_normalizer hg))
  · exact ⟨hoff.1.map_conj g, by rw [fixedCodim_map_conj, rank_map_conj]; exact hoff.2⟩

private theorem critical_normalized_alpha (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source) (b : Vertex R)
    (hc : CriticalPair R (alpha R) b (geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) (hat : Adjacent R (alpha R) t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist (alpha R) b) :
    Q R t ≤ normalizer ((X R b ⊔ Q R (alpha R) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  let := X_elementary R (alpha R)
  have hE := (critical_edge_data source geometry hb (alpha R) rfl b hc t hat ht).1
  have hT : Q R t ≤ stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
  apply image_normalizer_lift source (X R b) (Q R t) (hE.trans hT) hT
  exact offender_normalized source hu t hat _ (map_mono (comap_mono hE))
    (critical_image_offender source geometry hb hu b hc t hat ht)

private theorem critical_common_alpha (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source) (b : Vertex R)
    (hc : CriticalPair R (alpha R) b (geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) (hat : Adjacent R (alpha R) t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist (alpha R) b)
    (c : Vertex R) (hcc : CriticalPair R (alpha R) c (geometry.exists_critical (alpha R) rfl))
    (htc : (cosetGraph R).dist t c + 1 = (cosetGraph R).dist (alpha R) c) :
    X R b ⊔ Q R (alpha R) = X R c ⊔ Q R (alpha R) := by
  let := X_elementary R (alpha R)
  have hE := (critical_edge_data source geometry hb (alpha R) rfl b hc t hat ht).1
  have hF := (critical_edge_data source geometry hb (alpha R) rfl c hcc t hat htc).1
  have hT : Q R t ≤ stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
  obtain ⟨A, _, _, huniq, _⟩ := hu t hat
  have he : image source (X R b) = image source (X R c) :=
    (huniq _ (map_mono (comap_mono hE))
      (critical_image_offender source geometry hb hu b hc t hat ht)).trans
    (huniq _ (map_mono (comap_mono hF))
      (critical_image_offender source geometry hb hu c hcc t hat htc)).symm
  have hp := congrArg (fun B : Subgroup SL =>
    (B.comap (baseProjection source)).map (stabilizer R (alpha R)).subtype) he
  simpa only [image_preimage source _ (hE.trans hT), image_preimage source _ (hF.trans hT)] using hp



omit [Finite M] in
private theorem critical_to_alpha (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (b : Vertex R) (hc : CriticalPair R a b (geometry.exists_critical a ha))
    (f : FreeAmalgam R) (hf : act R f a = alpha R) :
    CriticalPair R (alpha R) (act R f b) (geometry.exists_critical (alpha R) rfl) := by
  have hfcol : color R (act R f a) = false := by rw [hf]; rfl
  simpa only [hf] using (criticalPair_act_iff R f a b (geometry.exists_critical a ha)
    (geometry.exists_critical (act R f a) hfcol)).mpr hc

private theorem critical_normalized (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source)
    (a : Vertex R) (ha : color R a = false) (b : Vertex R)
    (hc : CriticalPair R a b (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b) :
    Q R t ≤ normalizer ((X R b ⊔ Q R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  obtain ⟨f, hf⟩ := exists_to_alpha a ha
  have hc' := critical_to_alpha geometry a ha b hc f hf
  have hat' : Adjacent R (alpha R) (act R f t) := by
    simpa only [hf] using (adjacent_act_iff R f a t).mpr hat
  have ht' : (cosetGraph R).dist (act R f t) (act R f b) + 1 =
      (cosetGraph R).dist (alpha R) (act R f b) := by
    rw [← hf, dist_act, dist_act]
    exact ht
  have hn : Q R (act R f t) ≤ normalizer
      ((X R (act R f b) ⊔ Q R (act R f a) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    simpa only [hf] using critical_normalized_alpha source geometry hb hu (act R f b) hc'
      (act R f t) hat' ht'
  rw [Q_act, X_act, Q_act, ← Subgroup.map_sup, ← Subgroup.map_equiv_normalizer_eq] at hn
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj f⁻¹).injective).mp hn

private theorem critical_common (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source)
    (a : Vertex R) (ha : color R a = false) (b : Vertex R)
    (hc : CriticalPair R a b (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b)
    (c : Vertex R) (hcc : CriticalPair R a c (geometry.exists_critical a ha))
    (htc : (cosetGraph R).dist t c + 1 = (cosetGraph R).dist a c) :
    X R b ⊔ Q R a = X R c ⊔ Q R a := by
  obtain ⟨f, hf⟩ := exists_to_alpha a ha
  have hc' := critical_to_alpha geometry a ha b hc f hf
  have hcc' := critical_to_alpha geometry a ha c hcc f hf
  have hat' : Adjacent R (alpha R) (act R f t) := by
    simpa only [hf] using (adjacent_act_iff R f a t).mpr hat
  have ht' : (cosetGraph R).dist (act R f t) (act R f b) + 1 =
      (cosetGraph R).dist (alpha R) (act R f b) := by
    rw [← hf, dist_act, dist_act]
    exact ht
  have htc' : (cosetGraph R).dist (act R f t) (act R f c) + 1 =
      (cosetGraph R).dist (alpha R) (act R f c) := by
    rw [← hf, dist_act, dist_act]
    exact htc
  have he : X R (act R f b) ⊔ Q R (act R f a) =
      X R (act R f c) ⊔ Q R (act R f a) := by
    simpa only [hf] using critical_common_alpha source geometry hb hu (act R f b) hc'
      (act R f t) hat' ht' (act R f c) hcc' htc'
  simp only [X_act, Q_act, ← Subgroup.map_sup] at he
  exact Subgroup.map_injective (MulAut.conj f⁻¹).injective he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CriticalImages

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Edge offender rigidity gives both required critical-image properties at every M-vertex. -/
theorem criticalImageControl_of_edgeOffenderUniqueness (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R) (hu : EdgeOffenderUniqueness source) :
    CriticalImageControl R geometry where
  normalized := CriticalImages.critical_normalized source geometry hb hu
  common := CriticalImages.critical_common source geometry hb hu

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
