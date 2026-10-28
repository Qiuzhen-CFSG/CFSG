module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Marked local action and the source relative normalizer

The source projection and the natural-module marking are transported by the
same ambient conjugator, constructing a compatible `LocalModel` at every
M-vertex. In these coordinates the edge kernel has order-four image and fixes
its actual displacement plane pointwise. The single finite-geometry input
`fixerCard` identifies that image with the whole pointwise fixer.

Exact inverse images then identify the relative normalizer inside the local
stabilizer, including its kernel. Quotient generation lifts to the local group.
Every matrix translate of an edge plane comes from an actual adjacent vertex;
the graph's inverse-conjugation convention requires the inverse of the lifted
matrix actor. Coordinate intersections, centralizers and cardinalities are
transported by the same marking.

These results supply local action and realization for the two-choice assembly;
`fixerCard` remains the explicit input from the independent finite-plane proof.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation on printed p.881 and the choices in (4.3.7)(i), p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Transport both the quotient and the natural marking by the same conjugator. -/
theorem localModel_nonempty [Finite M] (source : LocalSource L R)
    {geometry : Geometry R} (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) : Nonempty (LocalModel a) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f :=
    (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have heval (m : M) : (e m : FreeAmalgam R) = g⁻¹ * embedM R m * g := by
    change (MulAut.conj g⁻¹) (embedM R m) = _
    simp [MulAut.conj]
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le
      (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl,
      ← map_map, ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  have hU : (U R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom = U R (mVertex R g) := by
    simpa only [alpha, act_mVertex, one_mul] using (U_act R g (alpha R)).symm
  let eU : U R (alpha R) ≃* U R (mVertex R g) :=
    ((MulAut.conj g⁻¹).subgroupMap (U R (alpha R))).trans (MulEquiv.subgroupCongr hU)
  have heU (u : U R (alpha R)) : (eU u : FreeAmalgam R) = g⁻¹ * (u : FreeAmalgam R) * g := by
    change (MulAut.conj g⁻¹) (u : FreeAmalgam R) = _
    simp [MulAut.conj]
  let π : S →* SL := modules.natural.marking.toMonoidHom.comp
    (source.projection.comp e.symm.toMonoidHom)
  refine ⟨{ projection := π
            surjective := modules.natural.marking.surjective.comp
              (source.projection_surjective.comp e.symm.surjective)
            kernel := ?_
            equiv := eU.symm.trans modules.natural.equiv
            action := ?_ }⟩
  · rw [← hQ]
    ext x
    change modules.natural.marking (source.projection (e.symm x)) = 1 ↔ _
    rw [modules.natural.marking.map_eq_one_iff]
    change e.symm x ∈ source.projection.ker ↔ _
    rw [source.projection_kernel]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  · intro x u v hv
    obtain ⟨m, rfl⟩ := e.surjective x
    obtain ⟨u, rfl⟩ := eU.surjective u
    obtain ⟨v, rfl⟩ := eU.surjective v
    have hv' : (v : FreeAmalgam R) = embedM R m * (u : FreeAmalgam R) * (embedM R m)⁻¹ := by
      rw [heU, heU, heval] at hv
      simpa [mul_assoc] using congrArg (fun z => g * z * g⁻¹) hv
    have h := modules.natural.action m u v hv'
    change modules.natural.equiv (eU.symm (eU v)) =
      modelAction (modules.natural.marking (source.projection (e.symm (e m))))
        (modules.natural.equiv (eU.symm (eU u)))
    simp only [MulEquiv.symm_apply_apply]
    apply Multiplicative.toAdd.injective
    rw [modelAction_apply]
    exact h

namespace LocalModel
variable {a : Vertex R} (model : LocalModel a)

/-- Natural coordinates preserve the order of a subgroup of U_a. -/
theorem coordinates_card (A : Subgroup (FreeAmalgam R)) (hA : A ≤ U R a) :
    Nat.card (model.coordinates A) = Nat.card A := by
  rw [coordinates, ← Nat.card_congr ((A.subgroupOf (U R a)).equivMapOfInjective
    model.equiv.toMonoidHom model.equiv.injective).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]

/-- Coordinates preserve intersections, including the intersection lines. -/
theorem coordinates_inf (A B : Subgroup (FreeAmalgam R)) :
    model.coordinates (A ⊓ B) = model.coordinates A ⊓ model.coordinates B := by
  simp only [coordinates, subgroupOf, comap_inf]
  exact Subgroup.map_inf _ _ model.equiv.toMonoidHom model.equiv.injective

/-- Distinct subgroups of U_a have distinct coordinate subgroups. -/
theorem coordinates_injective {A B : Subgroup (FreeAmalgam R)}
    (hA : A ≤ U R a) (hB : B ≤ U R a)
    (he : model.coordinates A = model.coordinates B) : A = B := by
  have hh := map_injective model.equiv.injective he
  have hm := congrArg (Subgroup.map (U R a).subtype) hh
  simpa only [map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB] using hm

/-- Image order is the actual Q_a-relative index, not an ambient index. -/
theorem actorImage_card (H : Subgroup (FreeAmalgam R)) (hH : H ≤ stabilizer R a) :
    Nat.card (model.actorImage H) = (Q R a).relIndex H := by
  rw [actorImage, ← relIndex_ker, model.kernel, relIndex_subgroupOf hH]

/-- Matrix fixation agrees with ambient commutation under the marking. -/
theorem action_fixed_iff (g : stabilizer R a) (u : U R a) :
    modelAction (model.projection g) (model.equiv u) = model.equiv u ↔
      (g : FreeAmalgam R) * (u : FreeAmalgam R) = u * g := by
  let v : U R a := ⟨g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
    (mem_normalizer_iff.mp (U_normalized a g.property) u).mp u.property⟩
  have hv := model.action g u v rfl
  constructor
  · intro h
    have he := congrArg (fun w : U R a => (w : FreeAmalgam R))
      (model.equiv.injective (hv.trans h))
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro h
    have he : v = u := Subtype.ext (by
      change (g : FreeAmalgam R) * u * (g : FreeAmalgam R)⁻¹ = u
      rw [h, mul_inv_cancel_right])
    exact hv.symm.trans (congrArg model.equiv he)

/-- Common matrix fixed points are precisely the natural-layer centralizer. -/
theorem fixedSpace_actorImage (H : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R a) :
    fixedSpace (model.actorImage H) =
      model.coordinates (U R a ⊓ centralizer (H : Set (FreeAmalgam R))) := by
  ext v
  obtain ⟨u, rfl⟩ := model.equiv.surjective v
  constructor
  · intro hv
    refine ⟨u, ⟨u.property, ?_⟩, rfl⟩
    intro g hg
    exact (model.action_fixed_iff ⟨g, hH hg⟩ u).mp
      (hv _ (mem_map_of_mem model.projection hg))
  · rintro ⟨u', hu', he⟩ g ⟨x, hx, rfl⟩
    have huu : u' = u := model.equiv.injective he
    subst u'
    exact (model.action_fixed_iff x u).mpr (hu'.2 x hx)

/-- Coordinate transport follows the same ambient conjugation as the marking. -/
theorem coordinates_conjugate (g : stabilizer R a)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ U R a) :
    model.coordinates (A.map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) =
      (model.coordinates A).map (modelAction (model.projection g)).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨v, ⟨u, hu, huv⟩, rfl⟩
    refine ⟨model.equiv ⟨u, hA hu⟩, ⟨⟨u, hA hu⟩, hu, rfl⟩, ?_⟩
    exact (model.action g ⟨u, hA hu⟩ v huv.symm).symm
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    let v : U R a := ⟨g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
      (mem_normalizer_iff.mp (U_normalized a g.property) u).mp u.property⟩
    exact ⟨v, ⟨u, hu, rfl⟩, model.action g u v rfl⟩

/-- A subgroup containing the local kernel is recovered exactly from its image. -/
theorem actorImage_comap (H : Subgroup (FreeAmalgam R)) (hQ : Q R a ≤ H) :
    (model.actorImage H).comap model.projection = H.subgroupOf (stabilizer R a) := by
  apply comap_map_eq_self
  rw [model.kernel]
  exact fun _ hx => hQ hx

/-- Generation in the marked quotient lifts once the actual kernel is present. -/
theorem generation_lifts (H K : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R a) (hK : K ≤ stabilizer R a)
    (hQ : Q R a ≤ H ⊔ K)
    (hgen : model.actorImage H ⊔ model.actorImage K = ⊤) :
    H ⊔ K = stabilizer R a := by
  have hm : model.actorImage (H ⊔ K) = ⊤ := by
    rw [actorImage, subgroupOf_sup hH hK, Subgroup.map_sup]
    exact hgen
  have hc := model.actorImage_comap (H ⊔ K) hQ
  rw [hm, comap_top] at hc
  exact le_antisymm (sup_le hH hK) (subgroupOf_eq_top.mp hc.symm)

/-- Every matrix translate is realized by an adjacent vertex. Since the graph
uses inverse conjugation, the realizing vertex is `act g⁻¹ t`. -/
theorem realizes_plane [Finite M] (source : LocalSource L R) {t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (s : SL) :
    ∃ u : Vertex R, Adjacent R a u ∧
      model.coordinates (edgeDisplacement a u) =
        (model.coordinates (edgeDisplacement a t)).map (modelAction s).toMonoidHom := by
  obtain ⟨g, rfl⟩ := model.surjective s
  have hg : act R (g : FreeAmalgam R)⁻¹ a = a := (stabilizer R a).inv_mem g.property
  refine ⟨act R (g : FreeAmalgam R)⁻¹ t, ?_, ?_⟩
  · simpa only [hg] using (adjacent_act_iff R (g : FreeAmalgam R)⁻¹ a t).mpr hat
  · have ht := PairingControl.FirstPairing.edgeDisplacement_act (g : FreeAmalgam R)⁻¹ a t
    rw [hg, inv_inv] at ht
    rw [ht]
    exact model.coordinates_conjugate g _ (Initial.edge_le_natural source a t ha hat)

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

/-- The order-four edge image fixes its actual displacement pointwise. -/
theorem edge_actorImage_eq_planeFixer (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (fixerCard : ∀ A : Subgroup Space, Nat.card A = 4 → Nat.card (planeFixer A) = 4)
    (t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    model.actorImage (Q R t) = planeFixer (model.coordinates (edgeDisplacement a t)) := by
  have hloc : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hU := Initial.edge_le_natural source a t ha hat
  have hcentral : edgeDisplacement a t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    have hz := edge_le_Z p hb control edge a t ha hat
    rw [EdgeTransfer.edge_Z_eq_fixed hb modules a t ha hat] at hz
    exact hz.trans inf_le_right
  have hle : model.actorImage (Q R t) ≤ planeFixer (model.coordinates (edgeDisplacement a t)) := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨u, hu, rfl⟩
    exact (model.action_fixed_iff g u).mpr (hcentral hu g hg)
  apply eq_of_le_of_card_ge hle
  rw [model.actorImage_card _ hloc,
    (edge_indices hb modules p initial control edge a t ha hat).2,
    fixerCard _ (by rw [model.coordinates_card _ hU]; exact edge_card p (by omega) initial a t ha hat)]

/-- The pointwise plane fixer pulls back to the whole edge kernel, inside G_a. -/
theorem edge_planeFixer_comap (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (fixerCard : ∀ A : Subgroup Space, Nat.card A = 4 → Nat.card (planeFixer A) = 4)
    (t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    (planeFixer (model.coordinates (edgeDisplacement a t))).comap model.projection =
      (Q R t).subgroupOf (stabilizer R a) := by
  rw [← model.edge_actorImage_eq_planeFixer hb modules p initial control edge fixerCard t ha hat]
  apply model.actorImage_comap
  apply Q_le_adjacent_h R _ hat
  have hn := adjacent_color_ne R hat
  cases ht : color R t <;> simp_all

/-- The literal relative normalizer is precisely the inverse image of the
matrix normalizer; the normalizers are relative to their respective groups. -/
theorem relativeNormalizer_comap (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (fixerCard : ∀ A : Subgroup Space, Nat.card A = 4 → Nat.card (planeFixer A) = 4)
    (t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    (normalizer (planeFixer (model.coordinates (edgeDisplacement a t)) : Set SL)).comap
        model.projection =
      (stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R))).subgroupOf (stabilizer R a) := by
  rw [comap_normalizer_eq_of_surjective _ model.surjective,
    model.edge_planeFixer_comap hb modules p initial control edge fixerCard t ha hat,
    inf_subgroupOf_left, subgroupOf_normalizer_eq
      (show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat))]

/-- The full relative normalizer has exactly the required matrix image. -/
theorem relativeNormalizer_actorImage (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (fixerCard : ∀ A : Subgroup Space, Nat.card A = 4 → Nat.card (planeFixer A) = 4)
    (t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    model.actorImage (stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) =
      normalizer (planeFixer (model.coordinates (edgeDisplacement a t)) : Set SL) := by
  rw [actorImage, ← model.relativeNormalizer_comap hb modules p initial control edge fixerCard t ha hat]
  exact map_comap_eq_self_of_surjective model.surjective _

/-- The actual vertex kernel lies in the relative normalizer at every edge. -/
theorem kernel_le_relativeNormalizer (t : Vertex R) (ha : color R a = false)
    (hat : Adjacent R a t) :
    Q R a ≤ stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R)) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases ht : color R t <;> simp_all
  exact le_inf (fun _ hx => hx.1) ((Q_le_adjacent_h R ht hat).trans (Q R t).le_normalizer)

/-- Kernel containment in the subgroup of G_a used for quotient lifting. -/
theorem projection_kernel_le_relativeNormalizer (t : Vertex R) (ha : color R a = false)
    (hat : Adjacent R a t) :
    model.projection.ker ≤
      (stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R))).subgroupOf (stabilizer R a) := by
  rw [model.kernel]
  exact subgroupOf_mono _ (kernel_le_relativeNormalizer t ha hat)

end LocalModel
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices
