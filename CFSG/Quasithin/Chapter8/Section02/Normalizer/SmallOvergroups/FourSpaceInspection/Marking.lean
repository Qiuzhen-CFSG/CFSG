module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.QuasisimpleAction
public import Theory.Representation.BinaryAlternatingFiveNormalizer
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.QuasithinBasic

/-!+# The marked alternating action in the four-space branch

The module on U in the first two rows of 8.2.5 is the binary deleted
permutation module for A₅. Transport its literal action image using an
isomorphism of U, not an abstract isomorphism of its acting group. The
normalizer theorem then puts the action of T L_U inside the same S₅ image.
A perfect subgroup inside this S₅ image lies in its alternating image:
the sign homomorphism vanishes on a perfect group.

The universal cubic overgroup inspection is stated as an explicit pending
contract. It is stronger than the normalizer theorem and is not proved here.
The final consumer below uses this contract and the cubic-rank bound to
obtain containment on the original U, then lifts through the actual source
Sylow and quasisimple two-core quotient.

Source: Aschbacher–Smith, proof of 8.2.8(1), printed p.719/PDF p.736.
The marking is 8.2.6(2), using H.4.6(2) and H.16.3(2). In particular the
different L₂(4)-module on B/U is not used as a replacement for U.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection

/-- The multiplicative additive group of the actual deleted-permutation module. -/
abbrev FiveModule := Multiplicative (BinaryPermutation.natural (Fin 5))

/-- The marked alternating operators on the four-space. -/
@[expose] noncomputable def alternatingImage : Subgroup (MulAut FiveModule) :=
  (alternatingGroup (Fin 5)).map (BinaryPermutation.naturalMulAction (Fin 5))

/-- The marked symmetric operators on that same four-space. -/
@[expose] noncomputable def symmetricImage : Subgroup (MulAut FiveModule) :=
  (BinaryPermutation.naturalMulAction (Fin 5)).range

/-- Pending finite matrix theorem: adjoining an operator outside the marked
S₅ to A₅ forces cubic rank at least two. This is a proof obligation, not an
instance or an asserted overgroup classification. -/
@[expose] def CubicOvergroupInspection : Prop :=
  ∀ D : Subgroup (MulAut FiveModule), alternatingImage ≤ D →
    primeRank 3 D ≤ 1 → D ≤ symmetricImage

private theorem perfect_le_alternating (D : Subgroup (MulAut FiveModule))
    [Group.IsPerfect D] (hD : D ≤ symmetricImage) : D ≤ alternatingImage := by
  let j := BinaryPermutation.naturalMulAction (Fin 5)
  let e : Equiv.Perm (Fin 5) ≃* symmetricImage :=
    MonoidHom.ofInjective (BinaryPermutation.naturalMulAction_injective_of_odd
      (Fin 5) (by decide))
  let f := Equiv.Perm.sign.comp (e.symm.toMonoidHom.comp (inclusion hD))
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf (d : D) : f d = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f d, ⟨d, rfl⟩⟩ : f.range) 1)
  intro d hd
  let σ := e.symm (inclusion hD ⟨d, hd⟩)
  refine ⟨σ, ?_, ?_⟩
  · exact Equiv.Perm.mem_alternatingGroup.mpr (hf ⟨d, hd⟩)
  · exact congrArg Subtype.val (e.apply_symm_apply (inclusion hD ⟨d, hd⟩))

variable {G : Type*} [Group G]

/-- When H normalizes U, its relative-normalizer image is the range of its
actual conjugation homomorphism. -/
theorem actionImage_eq_range (H U : Subgroup G)
    (hHU : H ≤ normalizer (U : Set G)) :
    actionImage H U = (U.normalizerMonoidHom.comp (inclusion hHU)).range := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨inclusion hHU x, x.property, rfl⟩

/-- Relative normalization survives the literal action map on U. -/
theorem actionImage_normalizes (H R U : Subgroup G)
    (hRU : R ≤ normalizer (U : Set G))
    (hHR : H ≤ normalizer (R : Set G)) :
    actionImage H U ≤ normalizer (actionImage R U : Set (MulAut U)) := by
  apply le_trans (map_mono (f := U.normalizerMonoidHom) ?_)
    (le_normalizer_map U.normalizerMonoidHom)
  rw [← subgroupOf_normalizer_eq hRU]
  exact subgroupOf_mono _ hHR

/-- A marking of 8.2.6(2) identifies Aut_(T L_U)(U) inside the concrete
S₅ normalizer of the deleted-permutation action. -/
theorem marked_sylow_residual_action_le (L U T : Subgroup G)
    (e : U ≃* FiveModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G)) :
    (actionImage (T ⊔ localResidual L U) U).map (MulAut.congr e).toMonoidHom ≤
      symmetricImage := by
  have h := map_mono (f := (MulAut.congr e).toMonoidHom)
    (actionImage_normalizes (T ⊔ localResidual L U) (localResidual L U) U
      ((localResidual_le L U).trans inf_le_right)
      (sup_le (normalizes_localResidual L U T hTL hTU) (localResidual L U).le_normalizer))
  rw [map_equiv_normalizer_eq, hmark] at h
  exact h.trans BinaryPermutation.normalizer_alternatingFive_naturalMulAction_le_range

/-- The cubic bound passes to the original action image because an odd-prime
rank-one group has cyclic Sylow subgroups. No arbitrary quotient-rank
monotonicity is used. -/
theorem actionImage_threeRank_le_one [Finite G] (K U : Subgroup G)
    (hKU : K ≤ normalizer (U : Set G)) (hrank : primeRank 3 K ≤ 1) :
    primeRank 3 (actionImage K U) ≤ 1 := by
  rw [actionImage_eq_range K U hKU]
  let f := U.normalizerMonoidHom.comp (inclusion hKU)
  let S : Sylow 3 K := Classical.choice inferInstance
  exact S.primeRank_le_one_of_surjective
    (S.isCyclic_of_odd_of_primeRank_le_one (by decide) hrank)
    f.rangeRestrict f.rangeRestrict_surjective

/-- Once the finite inspection and the commuting-section cubic bound are
proved, perfectness removes the possible odd-permutation operators. The
conclusion is the requested containment on the original U. -/
theorem actionImage_le_of_inspection [Finite G] (L K U : Subgroup G)
    [Group.IsPerfect K] (inspection : CubicOvergroupInspection)
    (e : U ≃* FiveModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hRK : localResidual L U ≤ K) (hKU : K ≤ normalizer (U : Set G))
    (hrank : primeRank 3 K ≤ 1) :
    actionImage K U ≤ actionImage (localResidual L U) U := by
  let D := (actionImage K U).map (MulAut.congr e).toMonoidHom
  have hA : alternatingImage ≤ D := by
    rw [← hmark]
    exact map_mono (map_mono (subgroupOf_mono _ hRK))
  have hr : primeRank 3 D ≤ 1 := by
    rw [← Theory.GroupTheory.primeRank_equiv 3
      ((actionImage K U).equivMapOfInjective (MulAut.congr e).toMonoidHom
        (MulAut.congr e).injective)]
    exact actionImage_threeRank_le_one K U hKU hrank
  let : Group.IsPerfect (actionImage K U) := by
    rw [actionImage_eq_range K U hKU]
    exact Group.IsPerfect.range _
  let : Group.IsPerfect D := Group.IsPerfect.map _
  have hle := perfect_le_alternating D (inspection D hA hr)
  rw [← hmark] at hle
  exact (map_le_map_iff_of_injective (MulAut.congr e).injective).mp hle

/-- Application through the source Sylow of N_G(U) and 8.2.7's literal
quasisimple quotient. The only later inputs are the named finite inspection
and cubic bound, both still to be discharged by the FourSpaceInspection owner. -/
theorem localResidual_eq_of_inspection [Finite G] (L K U : Subgroup G)
    (S : Sylow 2 (normalizer (U : Set G)))
    [Group.IsPerfect K] [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (inspection : CubicOvergroupInspection) (e : U ≃* FiveModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hRK : localResidual L U ≤ K) (hKU : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hSL : (S : Subgroup (normalizer (U : Set G))).map
      (normalizer (U : Set G)).subtype ≤ normalizer (L : Set G))
    (hnontriv : ¬ localResidual L U ≤ centralizer (U : Set G))
    (hrank : primeRank 3 K ≤ 1) : localResidual L U = K := by
  exact localResidual_eq_of_quasisimple_actionImage L K U _ hRK hKU
    ((pCoreIn_mono_of_normalizes hKU hNK).trans (pCoreIn_le_sylow _ S))
    hSL (map_subtype_le _) hnontriv
    (actionImage_le_of_inspection L K U inspection e hmark hRK hKU hrank)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection
