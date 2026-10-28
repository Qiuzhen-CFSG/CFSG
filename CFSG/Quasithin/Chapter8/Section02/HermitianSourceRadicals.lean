module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianRadicals
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceParameters

/-!
# The Hermitian offender's plane marking and relative fixed subgroup

Rank saturation gives actor rank 4n and fixed rank 4n on the actual
ambient subgroup. Transport through the same automizer embedding now
identifies that actor with the marked plane root group. Its uniqueness
inside a two-subgroup proves normalization by the image of the original
Sylow subgroup whenever the canonical offender lies there. The fixed
subgroup is consequently normal in that Sylow subgroup and is centralized
by the literal two-conjugate join.

These results discharge the plane-marking and image-normalization inputs
of 8.2.5. The earlier w = n, r >= 4n, canonical kernel and H.4.4(3)
premises remain explicit. Their construction, exclusion of n > 1 and the
field-four centralizer argument remain with
qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith 8.2.4–5, printed pp.716–717, using the proof of
H.4.4, printed p.381 (refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Chapter7.NormalizedSource.NonMathieuHermitian
variable {G : Type*} [Group G] [Finite G]

/-- A generator attaining the weak-closure minimum equals its offender
normalizer, so it already lies in the original Sylow subgroup. -/
theorem exists_offender_le_sylow {V : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T) {n : ℕ} (hw : globalW V T = n) :
    ∃ g : G, IsWOffenderAt V T g ∧ offenderNormalizer V g ≤ T := by
  obtain ⟨A, ⟨⟨g,hAW,hi⟩,hAT⟩,hAC⟩ := globalW_generator hw
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hAB : A ≤ offenderNormalizer V g := le_inf hAW (hAT.trans hT.normalizes)
  have hBC : ¬ offenderNormalizer V g ≤ centralizer (V : Set G) :=
    fun h => hAC (hAB.trans h)
  have hcorA : subgroupCorank W A = n := by
    change Nat.log 2 (A.relIndex W) = n
    rw [hi,Nat.log_pow (by decide)]
  have hsum := offender_corank_add (W := W) hAB
    (show offenderNormalizer V g ≤ W from inf_le_left)
  have hl := globalW_le_corank_of_noncentralizing_normalizes hT g le_rfl hBC
  rw [hw] at hl
  have hl' : n ≤ subgroupCorank W (offenderNormalizer V g) := ENat.natCast_le_natCast.mp hl
  have he : subgroupCorank W (offenderNormalizer V g) = n := by omega
  have hz : subgroupCorank (offenderNormalizer V g) A = 0 := by omega
  let : IsElementaryAbelian 2 (offenderNormalizer V g) :=
    offender_elementary_of_le (show offenderNormalizer V g ≤ W from inf_le_left)
  have heq : A = offenderNormalizer V g := subgroup_eq_of_corank_zero hAB hz
  refine ⟨g,⟨?_,hw.trans (congrArg (fun x : ℕ => (x : ℕ∞)) he.symm)⟩,heq ▸ hAT⟩
  intro hc
  exact hAC (hAW.trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)))

variable (V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G)
  (n : ℕ) [NeZero n]
  (e : Additive V ≃ₗ[ZMod 2] Space n)
  (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
  (he : ∀ a v, e (automizerRepresentation V a v) =
    overgroupAction n (binaryNormalizer n) (j a) (e v))
  (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
    3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
  (g : G) (hT : HypothesisE322 V T) (hOff : IsWOffenderAt V T g)
  (hw : globalW V T = n) (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
  (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
    V ⊓ V.map (MulAut.conj g).toMonoidHom)

include e hj he hgeometry hT hOff hw hr hkernel in
private theorem offender_model_ranks :
    let f := (binaryNormalizer n).subtype.comp j
    let A := (inducedAutomizer V (offenderNormalizer V g)).map f
    rank A = 4*n ∧ Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) A) = 4*n := by
  obtain ⟨ha, _, hfix, _⟩ := offender_parameters_of_coordinates V T n e j hj he
    hgeometry g hT hOff hw hr hkernel
  let f := (binaryNormalizer n).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  refine ⟨(rank_map_injective f hf _).trans ha, ?_⟩
  have hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = n := ENat.natCast_inj.mp (hOff.2.symm.trans hw)
  have hc := Offenders.intersection_corank V g hkernel
  rw [← hfix,hcor,ha,← fixedCodim_inducedAutomizer V (offenderNormalizer V g) inf_le_right] at hc
  have hc' := fixedCodim_map_equivariant (automizerRepresentation V)
    (UnipotentRadicals.ambientAction n) f e he
    (inducedAutomizer V (offenderNormalizer V g))
  have hsum := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n)
    ((inducedAutomizer V (offenderNormalizer V g)).map f)
  rw [← hc',hc,finrank_binary] at hsum
  dsimp only [f] at hsum
  omega

include e hj he hgeometry hT hOff hw hr hkernel in
/-- The actual ambient offender maps to the marked plane root group under
the same coordinate embedding used for saturation. -/
theorem offender_plane_of_coordinates :
    ∃ c : Cover n,
      ((inducedAutomizer V (offenderNormalizer V g)).map
        ((binaryNormalizer n).subtype.comp j)).map
          (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  obtain ⟨ha,hfix⟩ := offender_model_ranks V T n e j hj he hgeometry g hT hOff hw hr hkernel
  let f := (binaryNormalizer n).subtype.comp j
  let : IsElementaryAbelian 2 (inducedAutomizer V (offenderNormalizer V g)) :=
    offender_inducedAutomizer_elementary V g
  let : IsElementaryAbelian 2 ((inducedAutomizer V (offenderNormalizer V g)).map f) :=
    IsElementaryAbelian.map f
  have hAN : (inducedAutomizer V (offenderNormalizer V g)).map f ≤ binaryNormalizer n :=
    fun _ ⟨a,_,ha⟩ => ha ▸ (j a).property
  exact saturated_actor_plane n _ hAN ha hfix

include e hj he hgeometry hT hOff hw hr hkernel in
/-- The same marking expressed using canonical conjugation of the literal
representation operators, independently of the normalizer codomain. -/
theorem offender_plane_coordinates :
    ∃ c : Cover n,
      ((inducedAutomizer V (offenderNormalizer V g)).map
        (ChapterK.Linear.Recognition.coordinateHom (automizerRepresentation V) n e)).map
          (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  have hm := offender_plane_of_coordinates V T n e j hj he hgeometry g hT hOff hw hr hkernel
  have hf : (binaryNormalizer n).subtype.comp j = ChapterK.Linear.Recognition.coordinateHom (automizerRepresentation V) n e := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [ChapterK.Linear.Recognition.coordinateHom_apply]
    exact (congrArg (fun w => overgroupAction n (binaryNormalizer n) (j a) w)
      (e.apply_symm_apply v)).symm.trans (he a (e.symm v)).symm
  rwa [hf] at hm

include e hj he hgeometry hT hOff hw hr hkernel in
/-- If the canonical offender is placed in the original Sylow subgroup,
the marked actor calculation discharges the image-normalizer premise of
8.2.5. -/
theorem offender_image_normalized_of_coordinates (hAT : offenderNormalizer V g ≤ T) :
    inducedAutomizer V T ≤
      normalizer (inducedAutomizer V (offenderNormalizer V g) : Set (Automizer V)) := by
  obtain ⟨ha,hfix⟩ := offender_model_ranks V T n e j hj he hgeometry g hT hOff hw hr hkernel
  let f := (binaryNormalizer n).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  let A := inducedAutomizer V (offenderNormalizer V g)
  let P := inducedAutomizer V T
  let : IsElementaryAbelian 2 A := offender_inducedAutomizer_elementary V g
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hp : IsPGroup 2 P := T.2.comap_subtype.map _
  have hAP : A ≤ P := map_mono (comap_mono hAT)
  have hPN : P.map f ≤ binaryNormalizer n := fun _ ⟨a,_,ha⟩ => ha ▸ (j a).property
  have hn := saturated_actor_normalized n (P.map f) (hp.map f) hPN (A.map f)
    (map_mono hAP) ha hfix
  intro a haP
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.map_injective hf
  change (A.map (MulAut.conj a).toMonoidHom).map f = A.map f
  rw [map_map]
  have heq : f.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (f a)).toMonoidHom.comp f := by
    ext b
    simp [MulAut.conj_apply]
  rw [heq,← map_map]
  exact mem_normalizer_iff_map_conj_eq.mp (hn (mem_map_of_mem f haP))

include e hj he hgeometry hT hOff hw hr hkernel in
/-- The Hermitian actor calculation gives relative normality and the
centralization conclusions for the literal two-conjugate subgroup. -/
theorem offender_fixed_normal_of_coordinates (hAT : offenderNormalizer V g ≤ T) :
    let U := V ⊓ centralizer (offenderNormalizer V g : Set G)
    U = offenderNormalizer V g ⊓ centralizer (V : Set G) ∧
      U = V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
  have hi := offender_image_normalized_of_coordinates V T n e j hj he
    hgeometry g hT hOff hw hr hkernel hAT
  have heq := (offender_parameters_of_coordinates V T n e j hj he
    hgeometry g hT hOff hw hr hkernel).2.2.1
  exact ⟨heq.trans hkernel.symm,heq,
    Offenders.fixed_normal_in_sylow V _ T hT.le_sylow inf_le_right hT.normalizes hi,
    Offenders.fixed_normalized_of_image_normalized V _ T inf_le_right hT.normalizes hi,
    Offenders.generated_pair_centralizes_fixed V g heq⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
