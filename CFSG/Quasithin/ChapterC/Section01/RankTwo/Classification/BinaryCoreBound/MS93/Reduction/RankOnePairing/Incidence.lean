module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Pencils
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry

/-!
# Local incidence propagation in MS93 (1.7)

The fixed pencil gives two neighboring decompositions with disjoint value
lines. Irreducibility first kills the local fixed kernel; centralizer
normality then propagates to the ambient normal closure. The three-subgroup
lemma gives [W,L,U] = 1 and kills [C,W]. Evaluation on the binary seed proves
that every noncentral w generates W modulo C_W(U).

The dual pencil covers U by genuine neighboring closures. The resulting
commutator bounds and a second pair of decompositions kill C_W(X_beta).
A relative normal-closure argument and the three-subgroup lemma make each
remaining evaluation L_alpha-equivariant. Local irreducibility gives its
image C_Z(Q_alpha).

`fixed_case` constructs the fixed pencil from the nonzero residual fixed
space and proves all four incidence and binary generation conclusions.
`dual_case` constructs the dual pencil from the zero residual fixed space
and compatible dual coordinates. `dual_case_of_natural` obtains those
coordinates from the source's natural quotient hypothesis.

These results retain only `SourceData`, the independently supplied
`LocalFacts`, and the stated branch hypotheses. The parent assembly must
still supply `LocalFacts` and assemble the full module conclusions of (1.7).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.7), pp.847--848.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
open Subgroup
open scoped commutatorElement
universe u
variable {M : Type u} [Group M] [Finite M]
variable {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M} [Z.Normal] [W.Normal]

/-- The incidence and binary evaluation-kernel conclusions from the fixed pencil. -/
theorem fixed_case_of_pencil (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (p : FixedPencil e i Z W X) :
    ⁅fixedPreimage (component e.projection e.flag) X Z, W⁆ = ⊥ ∧
    ⁅⁅W, component e.projection e.flag⁆, generated X⁆ = ⊥ ∧
    W ⊓ centralizer (X : Set M) = W ⊓ centralizer (generated X : Set M) ∧
    ∀ w : W, (w : M) ∉ centralizer (generated X : Set M) →
      W ≤ zpowers (w : M) ⊔ centralizer (generated X : Set M) := by
  let U := generated X
  let C := fixedPreimage (component e.projection e.flag) X Z
  let L := component e.projection e.flag
  let P := localParabolic e i
  let R := localParabolic e (!i)
  let Y := localGenerated R X
  let A := localResidual P
  have hXU : X ≤ U := le_normalClosure
  have hYU : Y ≤ U := localGenerated_le_generated R X
  have hCU : C ≤ U := inf_le_left
  have hXY : X ≤ Y := le_localGenerated R X (d.x_le.trans (f.core_le (!i)))
  have hCY : C ⊓ Y ≤ centralizer (W : Set M) :=
    fixed_local_centralizes U W Z C L Y d.generated_commutator (f.z_central_W d) hCU
      (fixedPreimage_commutator L X Z) f.z_irreducible
      (fun h => p.local_proper (h.trans p.local_bound))
  obtain ⟨a, b, _ha, _hb, hspanA, hspanB, hdis⟩ := p.neighbors
  have hstep : W ⊓ centralizer (X : Set M) ≤ centralizer (Y : Set M) :=
    centralizes_of_two_decompositions U W Z X Y (conjugate a X) (conjugate b X)
      (C ⊓ Y) (conjugate a (localFixed e Z i)) (conjugate b (localFixed e Z i))
      d.generated_commutator (f.z_central_generated d) hXU
      (conjugate_le_normal X U hXU a) (conjugate_le_normal X U hXU b)
      (inf_le_left.trans hCU) hspanA hspanB
      (commutator_conjugate_left X W _ p.seed_bound a)
      (commutator_conjugate_left X W _ p.seed_bound b) hCY hdis
  have hcent : W ⊓ centralizer (X : Set M) = W ⊓ centralizer (U : Set M) :=
    centralizer_propagation P R X W f.local_generation (f.seed_normalized d)
      (d.x_le.trans (f.core_le (!i))) hstep
  have hprop : W ⊓ centralizer (X : Set M) ≤ centralizer (U : Set M) :=
    hcent.le.trans inf_le_right
  have hAX : A ≤ normalizer (X : Set M) :=
    (map_subtype_le _).trans (f.seed_normalized d)
  have hXA : ⁅X, A⁆ ≤ C ⊓ Y := le_inf d.seed_fixed
    ((le_normalizer_iff_commutator_le_left.mp hAX).trans hXY)
  have htriple : ⁅⁅W, L⁆, U⁆ = ⊥ :=
    triple_of_seed U W X A L (C ⊓ Y) hprop (p.seed_bound.trans p.seed_fixed)
      hXA hCY p.residual_generation
  have hCW : ⁅C, W⁆ = ⊥ := fixed_centralizes_of_triple U W Z C L hCU
    d.generated_commutator (fixedPreimage_commutator L X Z) (f.z_central_W d) htriple
    (natural_fixed_eq_bot d.natural f.component_image)
  refine ⟨hCW, htriple, hcent, ?_⟩
  intro w hw
  obtain ⟨x, hx⟩ := p.seed_generator
  exact binary_seed_generation U W Z X C (localFixed e Z i) (f.z_central_W d)
    inf_le_left hXU p.seed_bound p.seed_card
    (commutator_eq_bot_iff_le_centralizer.mp hCW) hprop x hx w hw

/-- The fixed-space branch of the incidence argument, including the binary
evaluation-kernel input. The seed generator and neighboring decompositions
are constructed from the source's local natural two-space. -/
theorem fixed_case (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥) :
    ⁅fixedPreimage (component e.projection e.flag) X Z, W⁆ = ⊥ ∧
    ⁅⁅W, component e.projection e.flag⁆, generated X⁆ = ⊥ ∧
    W ⊓ centralizer (X : Set M) = W ⊓ centralizer (generated X : Set M) ∧
    ∀ w : W, (w : M) ∉ centralizer (generated X : Set M) →
      W ≤ zpowers (w : M) ⊔ centralizer (generated X : Set M) :=
  fixed_case_of_pencil d f (FixedGeometry.of_fixed d f h)

/-- The two other seed planes restrict pairing with C_W(X_alpha) to the
core-fixed line of each neighboring closure. -/
theorem dual_neighbor_bound (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (p : DualPencil e i Z W X) (a : localParabolic e i) :
    ⁅conjugate (a : M) (localGenerated (localParabolic e (!i)) X),
      W ⊓ centralizer (X : Set M)⁆ ≤ conjugate (a : M) (localFixed e Z (!i)) ∧
    conjugate (a : M) (localFixed e Z (!i)) ≤ localFixed e Z i := by
  let U := generated X
  let Y := localGenerated (localParabolic e (!i)) X
  let T := W ⊓ centralizer (X : Set M)
  let K := pairingKernel X W
  have hXU : X ≤ U := le_normalClosure
  have hKU : K ≤ U := inf_le_left
  have hKT : ⁅K, T⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le inf_le_left))
  have hXT : ⁅X, T⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hUT : ⁅U, T⁆ ≤ Z := (commutator_mono le_rfl inf_le_left).trans d.generated_commutator
  obtain ⟨r, s, hr, hs, hinter, hle⟩ := p.star_neighbors a
  have hb (b : localParabolic e (!i))
      (hspan : conjugate (a : M) Y ≤ (X ⊔ conjugate ((a : M) * (b : M)) X) ⊔ K) :
      ⁅conjugate (a : M) Y, T⁆ ≤ conjugate ((a : M) * (b : M)) (localFixed e Z i) := by
    apply (commutator_mono hspan le_rfl).trans
    apply pairing_sup_bound U T Z _ K _ hUT (f.z_central_generated d)
      (sup_le hXU (conjugate_le_normal X U hXU _)) hKU
    · exact pairing_sup_bound U T Z X _ _ hUT (f.z_central_generated d)
        hXU (conjugate_le_normal X U hXU _) (hXT.le.trans bot_le)
        ((commutator_mono le_rfl inf_le_left).trans
          (commutator_conjugate_left X W _ p.seed_bound _))
    · exact hKT.le.trans bot_le
  exact ⟨(le_inf (hb r hr) (hb s hs)).trans hinter, hle⟩

/-- The local line bound uses the restricted second argument C_W(X_alpha). -/
theorem dual_local_bound (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (p : DualPencil e i Z W X) :
    ⁅localGenerated (localParabolic e (!i)) X, W ⊓ centralizer (X : Set M)⁆ ≤
      localFixed e Z (!i) := by
  have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by
    ext x
    simp
  simpa only [OneMemClass.coe_one, conjugate, he, map_id] using
    (dual_neighbor_bound d f p 1).1

/-- The neighboring closures bound the full pairing with C_W(X_alpha). -/
theorem dual_star_bound (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (p : DualPencil e i Z W X) :
    ⁅generated X, W ⊓ centralizer (X : Set M)⁆ ≤ localFixed e Z i := by
  let U := generated X
  let Y := localGenerated (localParabolic e (!i)) X
  let T := W ⊓ centralizer (X : Set M)
  let K := pairingKernel X W
  let Yp := fun a : localParabolic e i => conjugate (a : M) Y
  have hYU : Y ≤ U := localGenerated_le_generated _ X
  have hYpU (a : localParabolic e i) : Yp a ≤ U := conjugate_le_normal Y U hYU a
  have hKU : K ≤ U := inf_le_left
  have hKT : ⁅K, T⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le inf_le_left))
  have hUT : ⁅U, T⁆ ≤ Z := (commutator_mono le_rfl inf_le_left).trans d.generated_commutator
  have hYp (a : localParabolic e i) : ⁅Yp a, T⁆ ≤ localFixed e Z i :=
    (dual_neighbor_bound d f p a).1.trans (dual_neighbor_bound d f p a).2
  exact (commutator_mono p.star_cover le_rfl).trans
    (pairing_sup_bound U T Z (⨆ a, Yp a) K _ hUT (f.z_central_generated d)
      (iSup_le hYpU) hKU
      (pairing_iSup_bound U T Z _ Yp hUT (f.z_central_generated d) hYpU hYp)
      (hKT.le.trans bot_le))

/-- Two opposite neighboring closures propagate centralization from X_beta to U. -/
theorem dual_opposite_centralizer (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (p : DualPencil e i Z W X) :
    W ⊓ centralizer (localGenerated (localParabolic e (!i)) X : Set M) ≤
      centralizer (generated X : Set M) := by
  let U := generated X
  let Y := localGenerated (localParabolic e (!i)) X
  let T := W ⊓ centralizer (Y : Set M)
  let K := pairingKernel X W
  have hYU : Y ≤ U := localGenerated_le_generated _ X
  have hUT : ⁅U, T⁆ ≤ Z := (commutator_mono le_rfl inf_le_left).trans d.generated_commutator
  have hYT : ⁅Y, T⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hKT : ⁅K, T⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le inf_le_left))
  obtain ⟨a, b, hXa, hXb, ha, hb, hdis⟩ := p.opposite_cover
  have hbound (g : M) (hXg : conjugate g X ≤ Y)
      (hcover : U ≤ (Y ⊔ conjugate g Y) ⊔ K) :
      ⁅U, T⁆ ≤ conjugate g (localFixed e Z (!i)) := by
    apply (commutator_mono hcover le_rfl).trans
    apply pairing_sup_bound U T Z _ K _ hUT (f.z_central_generated d)
      (sup_le hYU (conjugate_le_normal Y U hYU g)) inf_le_left
    · exact pairing_sup_bound U T Z Y _ _ hUT (f.z_central_generated d)
        hYU (conjugate_le_normal Y U hYU g) (hYT.le.trans bot_le)
        ((commutator_mono le_rfl (inf_le_inf_left W (centralizer_le hXg))).trans
          (commutator_conjugate_restricted Y W X _ (dual_local_bound d f p) g))
    · exact hKT.le.trans bot_le
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  exact bot_unique (hdis ▸ le_inf (hbound a hXa ha) (hbound b hXb hb))

/-- The literal elementwise commutator identity, conditional on the dual pencil. -/
theorem dual_case_of_pencil (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (p : DualPencil e i Z W X)
    (w : ↥(W ⊓ centralizer (X : Set M)))
    (hw : (w : M) ∉ centralizer (generated X : Set M)) :
    ⁅generated X, zpowers (w : M)⁆ = localFixed e Z i := by
  let U := generated X
  let Y := localGenerated (localParabolic e (!i)) X
  let T := W ⊓ centralizer (X : Set M)
  let P := localParabolic e i
  let Q := localCore (localParabolic e (!i))
  let A := localResidual P
  have hYTU : ⁅⁅Y, T⁆, Q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((dual_local_bound d f p).trans inf_le_right)
  have hQYT : ⁅⁅Q, Y⁆, T⁆ = ⊥ := by
    rw [commutator_comm Q Y]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (p.core_fixed.trans (centralizer_le inf_le_left))
  have hTQY : ⁅⁅T, Q⁆, Y⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hQYT hYTU
  have hTQ : ⁅T, Q⁆ ≤ centralizer (U : Set M) :=
    (le_inf ((commutator_mono inf_le_left le_rfl).trans (commutator_le_left W Q))
      (commutator_eq_bot_iff_le_centralizer.mp hTQY)).trans
        (dual_opposite_centralizer d f p)
  have hPT : P ≤ normalizer (T : Set M) :=
    (le_inf le_normalizer_of_normal
      (normalizes_centralizer P X (f.seed_normalized d))).trans
        inf_normalizer_le_normalizer_inf
  have hAT : ⁅A, T⁆ ≤ centralizer (U : Set M) :=
    (commutator_mono p.residual_generation le_rfl).trans
      (localGenerated_commutator_bound P Q T (centralizer (U : Set M)) hPT
        (by rwa [commutator_comm]))
  have htriple : ⁅⁅T, A⁆, U⁆ = ⊥ := by
    rw [commutator_comm T A]
    exact commutator_eq_bot_iff_le_centralizer.mpr hAT
  have hDU : localFixed e Z i ≤ centralizer (U : Set M) :=
    inf_le_left.trans (f.z_central_generated d)
  exact commutator_eq_of_evaluation_surjective U T (localFixed e Z i)
    (dual_star_bound d f p) hDU w
    (evaluation_surjective U T (localFixed e Z i) (dual_star_bound d f p) hDU
      A htriple p.local_irreducible w hw)

/-- The dual-space branch of the incidence argument with its geometric
premises discharged. The right side is the fixed space of the actual local
two-core, and the element lies in the restricted centralizer C_W(X). -/
theorem dual_case (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (dual : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥)
    (w : ↥(W ⊓ centralizer (X : Set M)))
    (hw : (w : M) ∉ centralizer (generated X : Set M)) :
    ⁅generated X, zpowers (w : M)⁆ = Z ⊓ centralizer (localCore (localParabolic e i) : Set M) :=
  dual_case_of_pencil d f (DualGeometry.of_dual d f dual h) w hw

/-- The second incidence conclusion directly from the source's natural
quotient hypothesis. Compatible contragredient coordinates and every
neighboring-pencil premise are proved upstream. -/
theorem dual_case_of_natural (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M)))
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥)
    (w : ↥(W ⊓ centralizer (X : Set M)))
    (hw : (w : M) ∉ centralizer (generated X : Set M)) :
    ⁅generated X, zpowers (w : M)⁆ = Z ⊓ centralizer (localCore (localParabolic e i) : Set M) :=
  dual_case_of_pencil d f (DualGeometry.of_natural d f n h) w hw

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
