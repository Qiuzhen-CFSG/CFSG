module

public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.Contracts
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.MaxElementaryOffender
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.FieldTheory.Finiteness

/-!
# Maximum elementary subgroups on the doubled natural module

For a maximum-order elementary subgroup E of R, the comparison with
U C_E(U) gives |U : C_U(E)| ≤ |ρK(E)|. The specified coordinates identify
C_U(E) with the actual fixed vectors of ρK(E) on two natural summands.
A nontrivial subgroup fixes at most sixteen doubled vectors, so a nontrivial
maximum-elementary image has order at least four.

Sylow conjugacy and the Borel-overgroup classification place the image of
P in one of the two standard parabolics, using only inner conjugation.
Their radicals have order four. The point radical fixes at most four
doubled vectors, contradicting the comparison, so the image is the full
plane radical. Graph duality is used only to calculate the *standard point
radical*; the quotient marking and its natural action are never twisted.

If every maximum elementary subgroup lies in Q, then J(B) = J(R) = J(Q).
The intrinsic J(B) is characteristic, its ambient image is normal in K,
and |U| = 64 ensures it is nontrivial. This gives the literal characteristic
obstruction in the first branch of the source argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, C.1.37, printed pp.141–143, especially the doubled
natural paragraph on p.142. The cardinal comparison is the proved
`Stellmacher.maxElementary_card_le_fixed_mul_image`.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
open Subgroup Theory.GroupTheory Stellmacher
universe u
variable {K : Type u} [Group K] [Finite K]
  {κ : GroupClass.{u}} {L P U : Subgroup K} [L.Normal] [U.Normal]
  {T : Sylow 2 K} (d : SourceData κ L P U T)

private theorem maxJ_intermediate (S D : Subgroup K)
    (hJS : elementaryAbelianMaxJ S ≤ D) (hDS : D ≤ S) :
    elementaryAbelianMaxJ D = elementaryAbelianMaxJ S := by
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq D S hDS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S D hJS
  have he := le_antisymm hsmall.1 hlarge.1
  exact le_antisymm (hsmall.2 he) (hlarge.2 he.symm)

namespace SourceData
include d

omit [Finite K] [L.Normal] [U.Normal] d in
/-- The elementary Thompson subgroup centralizes its own omega-center. -/
theorem maxJ_le_baumann : elementaryAbelianMaxJ (R P) ≤ B P := by
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj
  apply mem_centralizer_iff.mpr
  intro z hz
  obtain ⟨zJ, hzJ, rfl⟩ := hz
  obtain ⟨zC, _, rfl⟩ := hzJ
  exact congrArg Subtype.val ((mem_center_iff.mp zC.property) ⟨j, hj⟩).symm

/-- When J(R) lies in Q, intrinsic J(B) is a nontrivial characteristic subgroup
whose subtype image is the normal subgroup J(Q). -/
theorem obstruction_of_maxJ_le_core
    (hJ : elementaryAbelianMaxJ (R P) ≤ Q (K := K)) :
    CharacteristicObstruction P := by
  have hJQ : elementaryAbelianMaxJ (Q (K := K)) = elementaryAbelianMaxJ (R P) :=
    maxJ_intermediate (R P) Q hJ d.core_le_radical
  have hJB : elementaryAbelianMaxJ (B P) = elementaryAbelianMaxJ (R P) :=
    maxJ_intermediate (R P) (B P) (maxJ_le_baumann (P := P)) inf_le_left
  let C := elementaryAbelianMaxJ (⊤ : Subgroup (B P))
  have hC : C.map (B P).subtype = elementaryAbelianMaxJ (R P) := by
    rw [← elementaryAbelianMaxJ_map_injective _ (B P).subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype, hJB]
  refine ⟨C, elementaryAbelianMaxJ_top_characteristic, ?_, ?_⟩
  · intro hbot
    have hJbot : elementaryAbelianMaxJ (R P) = ⊥ := by rw [← hC, hbot, Subgroup.map_bot]
    obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (R P)
    have hAbot : A = ⊥ := le_bot_iff.mp (hJbot ▸ le_sSup hA)
    have hc := hA.2.2 U d.source_module_le_radical d.elementary
    rw [d.source_module_card, hAbot, Subgroup.card_bot] at hc
    omega
  · rw [hC, ← hJQ, normal_iff_map_conj_eq]
    intro g
    change (elementaryAbelianMaxJ Q).map (MulAut.conj g).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv]
    congr 1
    exact Subgroup.Normal.map_conj_eq Q g

/-- The all-in-core branch of the maximum-elementary comparison. -/
theorem obstruction_of_maxima_le_core
    (h : ∀ E ∈ elementaryAbelianMaxSubgroups (R P), E ≤ Q (K := K)) :
    CharacteristicObstruction P :=
  d.obstruction_of_maxJ_le_core (sSup_le h)

/-- The maximum-elementary replacement bound, with |U| = 64 and the actual
quotient projection as its action image. -/
theorem maxElementary_card_bound (E : Subgroup K)
    (hE : E ∈ elementaryAbelianMaxSubgroups (R P)) :
    64 ≤ Nat.card ↥(U ⊓ centralizer (E : Set K)) * Nat.card (E.map d.ρK) := by
  let := d.elementary
  have h := maxElementary_card_le_fixed_mul_image (R P) U E d.source_module_le_radical hE
    d.ρK (d.ambient_projection_kernel.trans d.centralizer_eq_core.symm)
  rwa [d.source_module_card] at h

end SourceData

/-- The fixed vectors of an actual subgroup of SL₃(2) on two copies of its
specified natural module. -/
def DoubleFixed (A : Subgroup SL) :=
  {v : DoubleSpace // ∀ a ∈ A, ∀ i, Matrix.mulVec a.val (v i) = v i}

namespace SourceData
include d

omit [Finite K] in
/-- The specified action identifies centralizing elements with actual fixed
vectors in both natural summands. -/
theorem centralizer_iff_doubleFixed (E : Subgroup K) (u : U) :
    (u : K) ∈ centralizer (E : Set K) ↔
      ∀ a ∈ E.map d.ρK, ∀ i,
        Matrix.mulVec a.val (Multiplicative.toAdd (d.eU u) i) =
          Multiplicative.toAdd (d.eU u) i := by
  constructor
  · intro hu a ha i
    obtain ⟨e, he, rfl⟩ := ha
    have hc : MulAut.conjNormal e u = u := by
      apply Subtype.ext
      change e * (u : K) * e⁻¹ = (u : K)
      rw [mem_centralizer_iff.mp hu e he, mul_inv_cancel_right]
    have h := congrFun (d.action e u) i
    rw [hc] at h
    exact h.symm
  · intro hu
    apply mem_centralizer_iff.mpr
    intro e he
    have hc : MulAut.conjNormal e u = u := by
      apply d.eU.injective
      apply Multiplicative.toAdd.injective
      rw [d.action]
      funext i
      exact hu (d.ρK e) (mem_map_of_mem _ he) i
    have h := congrArg Subtype.val hc
    change e * (u : K) * e⁻¹ = (u : K) at h
    exact mul_inv_eq_iff_eq_mul.mp h

/-- The module marking restricts to an equivalence of the actual centralizer
and the doubled fixed-vector space. -/
noncomputable def centralizerEquivDoubleFixed (E : Subgroup K) :
    ↥(U ⊓ centralizer (E : Set K)) ≃ DoubleFixed (E.map d.ρK) where
  toFun u := ⟨Multiplicative.toAdd (d.eU ⟨u, u.property.1⟩),
    (d.centralizer_iff_doubleFixed E _).mp u.property.2⟩
  invFun v := ⟨d.eU.symm (Multiplicative.ofAdd v.val),
    (d.eU.symm (Multiplicative.ofAdd v.val)).property,
    (d.centralizer_iff_doubleFixed E _).mpr (by simpa using v.property)⟩
  left_inv u := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

omit [Finite K] in
/-- Cardinality transport through the prescribed module marking. -/
theorem centralizer_card_eq_doubleFixed (E : Subgroup K) :
    Nat.card ↥(U ⊓ centralizer (E : Set K)) = Nat.card (DoubleFixed (E.map d.ρK)) :=
  Nat.card_congr (d.centralizerEquivDoubleFixed E)

/-- The offender inequality in the original matrix coordinates. -/
theorem maxElementary_doubleFixed_bound (E : Subgroup K)
    (hE : E ∈ elementaryAbelianMaxSubgroups (R P)) :
    64 ≤ Nat.card (DoubleFixed (E.map d.ρK)) * Nat.card (E.map d.ρK) := by
  rw [← d.centralizer_card_eq_doubleFixed]
  exact d.maxElementary_card_bound E hE

end SourceData

namespace SourceData
include d

omit [Finite K] in
/-- Surjectivity already holds on the component. -/
theorem ambient_projection_surjective : Function.Surjective d.ρK := by
  intro g
  obtain ⟨l, hl⟩ := d.component_surjective g
  exact ⟨l, hl⟩

omit [Finite K] in
/-- The parabolic remains maximal after quotienting by the ambient two-core. -/
theorem parabolic_image_maximal : IsCoatom (P.map d.ρK) := by
  have hpre : (P.map d.ρK).comap d.ρK = P :=
    comap_map_eq_self (d.ambient_projection_kernel ▸ d.core_le_parabolic)
  refine ⟨?_, ?_⟩
  · intro h
    exact d.maximal.1 (by rw [← hpre, h, comap_top])
  · intro H hH
    have hlt : P < H.comap d.ρK := by
      calc
        P = (P.map d.ρK).comap d.ρK := hpre.symm
        _ < H.comap d.ρK :=
          (comap_lt_comap_of_surjective d.ambient_projection_surjective).mpr hH
    apply comap_injective d.ambient_projection_surjective
    simpa only [comap_top] using d.maximal.2 _ hlt

/-- The image of the intrinsic radical is the radical of the actual image. -/
theorem radical_image_eq_core : (R P).map d.ρK = (P.map d.ρK).pCoreIn 2 := by
  apply map_pCoreIn_of_ker_isPGroup
  rw [d.ambient_projection_kernel]
  exact pCore_isPGroup

open Matrix.PSL3Two
open scoped Pointwise

/-- An inner conjugation places the parabolic image at one of the two
standard stabilizers above the upper triangular Sylow subgroup. -/
theorem parabolic_image_marking : ∃ g : SL,
    (P.map d.ρK).map (MulAut.conj g).toMonoidHom = pointParabolicSL ∨
    (P.map d.ρK).map (MulAut.conj g).toMonoidHom = lineParabolicSL := by
  let S := T.mapSurjective d.ambient_projection_surjective
  let S₀ : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL S S₀
  have hS : ((T : Subgroup K).map d.ρK).map (MulAut.conj g).toMonoidHom = borelSL := by
    change ((g • S : Sylow 2 SL) : Subgroup SL) = borelSL
    rw [hg]
    rfl
  refine ⟨g, (coatoms_over_borelSL _).mp ⟨?_, ?_⟩⟩
  · exact ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr d.parabolic_image_maximal
  · rw [← hS]
    exact map_mono (map_mono d.sylow_le)

/-- The same inner marking identifies the two possible radical images. -/
theorem radical_image_marking : ∃ g : SL,
    ((R P).map d.ρK).map (MulAut.conj g).toMonoidHom = pointParabolicSL.pCoreIn 2 ∨
    ((R P).map d.ρK).map (MulAut.conj g).toMonoidHom = BinaryLinearThree.R := by
  obtain ⟨g, hp | hp⟩ := d.parabolic_image_marking
  · refine ⟨g, Or.inl ?_⟩
    rw [d.radical_image_eq_core, map_pCoreIn_of_injective, hp]
    exact (MulAut.conj g).injective
  · refine ⟨g, Or.inr ?_⟩
    rw [d.radical_image_eq_core, map_pCoreIn_of_injective, hp,
      lineParabolicSL_pCoreIn_two_eq_R]
    exact (MulAut.conj g).injective

end SourceData

namespace SourceData
include d

/-- The source offender inequality |U : C_U(E)| ≤ |ρK(E)|. -/
theorem maxElementary_offender_index (E : Subgroup K)
    (hE : E ∈ elementaryAbelianMaxSubgroups (R P)) :
    (centralizer (E : Set K)).relIndex U ≤ Nat.card (E.map d.ρK) := by
  have hcard : Nat.card ↥(U ⊓ centralizer (E : Set K)) *
      (centralizer (E : Set K)).relIndex U = Nat.card U := by
    simpa only [relIndex_bot_left, inf_relIndex_right, inf_relIndex_left, inf_comm] using
      relIndex_mul_relIndex (⊥ : Subgroup K) (centralizer (E : Set K) ⊓ U) U
        bot_le inf_le_right
  have hb := d.maxElementary_card_bound E hE
  rw [d.source_module_card] at hcard
  have hp : 0 < Nat.card ↥(U ⊓ centralizer (E : Set K)) := Nat.card_pos
  nlinarith

/-- Failure of the literal obstruction supplies a maximum elementary
subgroup whose image under the specified projection is nontrivial. -/
theorem exists_maximum_nontrivial_image (hno : ¬ CharacteristicObstruction P) :
    ∃ E ∈ elementaryAbelianMaxSubgroups (R P), E.map d.ρK ≠ ⊥ := by
  classical
  by_contra! h
  apply hno
  apply d.obstruction_of_maxima_le_core
  intro E hE
  rw [← d.ambient_projection_kernel]
  exact (Subgroup.map_eq_bot_iff _).mp (h E hE)

omit [Finite K] in
/-- A surjective maximum elementary image forces the full Thompson image. -/
theorem thompson_image_of_maximum_image (E : Subgroup K)
    (hE : E ∈ elementaryAbelianMaxSubgroups (R P))
    (himage : E.map d.ρK = (R P).map d.ρK) :
    (elementaryAbelianMaxJ (R P)).map d.ρK = (R P).map d.ρK := by
  apply le_antisymm (map_mono (sSup_le fun _ hA => hA.1))
  rw [← himage]
  exact map_mono (le_sSup hE)

end SourceData

namespace OffenderGeometry
open Representation.BinaryOffender Matrix.PSL3Two

/-- The doubled fixed space is precisely two copies of the natural fixed space. -/
noncomputable def doubleFixedEquivPi (A : Subgroup SL) :
    DoubleFixed A ≃ (Fin 2 → fixedSpace BinaryLinearThree.W A) where
  toFun v i := ⟨v.val i, fun a => v.property a a.property i⟩
  invFun v := ⟨fun i => (v i).val, fun a ha i => (v i).property ⟨a, ha⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fixed-space orders multiply across the two natural summands. -/
theorem doubleFixed_card (A : Subgroup SL) :
    Nat.card (DoubleFixed A) = Nat.card (fixedSpace BinaryLinearThree.W A) ^ 2 := by
  rw [Nat.card_congr (doubleFixedEquivPi A), Nat.card_fun, Nat.card_fin]

/-- Inner conjugation preserves the doubled fixed-space order. -/
theorem doubleFixed_card_conj (A : Subgroup SL) (g : SL) :
    Nat.card (DoubleFixed (A.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (DoubleFixed A) := by
  rw [doubleFixed_card, doubleFixed_card,
    ← Nat.card_congr (fixedSpaceConjEquiv BinaryLinearThree.W A g).toEquiv]

/-- A nontrivial matrix subgroup fixes a proper natural subspace, hence at
most sixteen vectors on two natural summands. -/
theorem doubleFixed_card_le_sixteen (A : Subgroup SL) (hne : A ≠ ⊥) :
    Nat.card (DoubleFixed A) ≤ 16 := by
  have hproper : fixedSpace BinaryLinearThree.W A ≠ ⊤ := by
    intro htop
    apply hne
    apply le_bot_iff.mp
    intro g hg
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    have hv : v ∈ fixedSpace BinaryLinearThree.W A := by rw [htop]; trivial
    exact (hv ⟨g, hg⟩).trans (Matrix.one_mulVec v).symm
  have hdim := Submodule.finrank_lt hproper
  have hthree : Module.finrank (ZMod 2) BinaryLinearThree.Vector = 3 := by
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]
  rw [hthree] at hdim
  have hc : Nat.card (fixedSpace BinaryLinearThree.W A) ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    have htwo : Nat.card (ZMod 2) = 2 := by simp
    rw [htwo]
    exact Nat.pow_le_pow_right (by decide) (by omega :
      Module.finrank (ZMod 2) (fixedSpace BinaryLinearThree.W A) ≤ 2)
  rw [doubleFixed_card]
  nlinarith

private theorem point_core_eq_dual_plane :
    pointParabolicSL.pCoreIn 2 = BinaryLinearThree.R.map flagDuality.toMonoidHom := by
  rw [← lineParabolicSL_pCoreIn_two_eq_R,
    map_pCoreIn_of_injective 2 lineParabolicSL _ flagDuality.injective,
    flagDuality_map_line]

/-- The point-parabolic radical has order four. -/
theorem card_point_core : Nat.card (pointParabolicSL.pCoreIn 2) = 4 := by
  rw [point_core_eq_dual_plane, card_map_of_injective flagDuality.injective,
    BinaryLinearThree.card_R]

private theorem point_core_fixed_coordinates (v : Fin 3 → ZMod 2)
    (hv : ∀ a ∈ pointParabolicSL.pCoreIn 2, Matrix.mulVec a.val v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  let a : SL := ⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩
  let b : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
  have ha : a ∈ pointParabolicSL.pCoreIn 2 := by
    rw [point_core_eq_dual_plane]
    refine ⟨BinaryLinearThree.shear (Multiplicative.ofAdd (1,0)),
      ⟨Multiplicative.ofAdd (1,0), rfl⟩, ?_⟩
    apply Subtype.ext
    decide +kernel
  have hb : b ∈ pointParabolicSL.pCoreIn 2 := by
    rw [point_core_eq_dual_plane]
    refine ⟨BinaryLinearThree.shear (Multiplicative.ofAdd (0,1)),
      ⟨Multiplicative.ofAdd (0,1), rfl⟩, ?_⟩
    apply Subtype.ext
    decide +kernel
  have hcoords : ∀ w : Fin 3 → ZMod 2,
      Matrix.mulVec a.val w = w → Matrix.mulVec b.val w = w →
        w 1 = 0 ∧ w 2 = 0 := by decide +kernel
  exact hcoords v (hv a ha) (hv b hb)

/-- Two independent point shears force both natural vectors onto the fixed
axis; at most four doubled vectors remain. -/
theorem doubleFixed_point_core_le_four :
    Nat.card (DoubleFixed (pointParabolicSL.pCoreIn 2)) ≤ 4 := by
  let f : DoubleFixed (pointParabolicSL.pCoreIn 2) → (Fin 2 → ZMod 2) :=
    fun v i => v.val i 0
  have hinj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    funext i j
    have hv := point_core_fixed_coordinates (v.val i) (fun a ha => v.property a ha i)
    have hw := point_core_fixed_coordinates (w.val i) (fun a ha => w.property a ha i)
    fin_cases j
    · exact congrFun h i
    · exact hv.1.trans hw.1.symm
    · exact hv.2.trans hw.2.symm
  have h := Nat.card_le_card_of_injective f hinj
  simpa using h

/-- A nontrivial subgroup of a marked parabolic radical satisfying the
doubled-natural offender bound is the full plane radical. -/
theorem radical_calculation (D A : Subgroup SL)
    (hmark : ∃ g : SL, D.map (MulAut.conj g).toMonoidHom =
      pointParabolicSL.pCoreIn 2 ∨
      D.map (MulAut.conj g).toMonoidHom = BinaryLinearThree.R)
    (hAD : A ≤ D) (hne : A ≠ ⊥)
    (hb : 64 ≤ Nat.card (DoubleFixed A) * Nat.card A) :
    A = D ∧ ∃ g : SL, D = BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hmark⟩ := hmark
  have hDcard : Nat.card D = 4 := by
    rw [← card_map_of_injective (K := D) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    rcases hmark with h | h
    · rw [h, card_point_core]
    · rw [h, BinaryLinearThree.card_R]
  have hfixed := doubleFixed_card_le_sixteen A hne
  have hAc : 4 ≤ Nat.card A := by
    nlinarith [Nat.mul_le_mul_right (Nat.card A) hfixed]
  have hAD' : A = D := eq_of_le_of_card_ge hAD (by omega)
  refine ⟨hAD', ?_⟩
  rcases hmark with hp | hl
  · have hDfixed : Nat.card (DoubleFixed D) ≤ 4 := by
      rw [← doubleFixed_card_conj D g, hp]
      exact doubleFixed_point_core_le_four
    rw [hAD', hDcard] at hb
    omega
  · refine ⟨g⁻¹, ?_⟩
    have he := congrArg (fun H : Subgroup SL => H.map (MulAut.conj g⁻¹).toMonoidHom) hl
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id SL := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    simpa only [map_map, hid, Subgroup.map_id] using he

end OffenderGeometry

namespace SourceData

/-- The maximum-elementary comparison in the doubled-natural case of C.1.37:
either intrinsic J(B) witnesses the characteristic obstruction, or the full
Thompson image is the plane radical in the supplied natural coordinates. -/
theorem offender_reduction : CharacteristicObstruction P ∨ OffenderData d := by
  classical
  by_cases hno : CharacteristicObstruction P
  · exact Or.inl hno
  · obtain ⟨E, hE, hne⟩ := d.exists_maximum_nontrivial_image hno
    obtain ⟨himage, hplane⟩ := OffenderGeometry.radical_calculation
      ((R P).map d.ρK) (E.map d.ρK) d.radical_image_marking
      (map_mono hE.1) hne (d.maxElementary_doubleFixed_bound E hE)
    exact Or.inr ⟨d.thompson_image_of_maximum_image E hE himage, hplane⟩

end SourceData

end CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
