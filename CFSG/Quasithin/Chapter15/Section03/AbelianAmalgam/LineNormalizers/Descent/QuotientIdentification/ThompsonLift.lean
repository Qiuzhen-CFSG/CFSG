module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Original

/-!
# Lifting the original Thompson commutator

Assume the original quotient map sends `X_E` to the alternating subgroup
in the second `S₃` factor. The maximum-elementary Thompson argument supplies
an involution in `J(R)` outside `Q_E`. Since `J(R)` centralizes `E`, this
involution has a nonidentity image in the second factor. A finite permutation
calculation shows that every element of that `A₃` is a commutator with it.

The two-residual `X_E = O²(C_G(E))` is itself two-residual-perfect. We transfer
this fact to its copy inside `G_E`, lift the quotient generation through the
normal two-core of `G_E`, and map back to the ambient group. The reverse
containment uses the relative normality of `X_E` in `G_E`.

This is a conditional helper for Lemma 15.3.67(4): its assembly owner must
supply the residual-image equality. No ambient normality of `Q_E` is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section

open Subgroup Stellmacher
open BenderSuzuki.External
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification.ThompsonLift

private theorem alternating_commutator_involution :
    ∀ t : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 →
      ∀ a : Equiv.Perm (Fin 3), a ∈ alternatingGroup (Fin 3) →
        ∃ b : Equiv.Perm (Fin 3), b ∈ alternatingGroup (Fin 3) ∧ ⁅b, t⁆ = a := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem second_factor_le_commutator
    (K : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (t : Equiv.Perm (Fin 3)) (ht : t ^ 2 = 1) (hnt : t ≠ 1)
    (htK : (1, t) ∈ K) :
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) ≤
      ⁅(⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)), K⁆ := by
  rintro ⟨x, a⟩ ⟨hx, ha⟩
  have hx1 : x = 1 := hx
  subst x
  obtain ⟨b, hb, hba⟩ := alternating_commutator_involution t ht hnt a ha
  have hc := commutator_mem_commutator
    (show (1, b) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod
      (alternatingGroup (Fin 3)) from ⟨one_mem _, hb⟩) htK
  have he : ⁅((1 : Equiv.Perm (Fin 3)), b), ((1 : Equiv.Perm (Fin 3)), t)⁆ = (1, a) := by
    apply Prod.ext
    · simp [commutatorElement_def]
    · exact hba
  rwa [he] at hc

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem thompson_le_centralizer {M Y T V E : Subgroup G}
    (s : Inputs M Y T V E) :
    elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G)) ≤ centralizer (E : Set G) :=
  (sSup_le fun _ hA => hA.1).trans (inf_le_right.trans (centralizer_le s.line_le))

private theorem relative_lineX_residual_perfect (E : Subgroup G) :
    hktPResidual 2 ((lineX E).subgroupOf (lineNormalizer E)) = ⊤ := by
  let e := subgroupOfEquivOfLe
    ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [hktPResidual_map_of_surjective' e.toMonoidHom e.surjective]
  rw [show hktPResidual 2 (lineX E) = ⊤ from
    twoResidualAmbient_has_top_twoResidual (centralizer (E : Set G))]
  exact (map_top_of_surjective e.toMonoidHom e.surjective).symm

variable {M Y T V E : Subgroup G} [IsMulCommutative V]

private theorem image_le_commutator (s : Inputs M Y T V E)
    (himage : ((lineX E).subgroupOf (lineNormalizer E)).map (originalProductMap s) =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3))) :
    ((lineX E).subgroupOf (lineNormalizer E)).map (originalProductMap s) ≤
      (⁅(lineX E).subgroupOf (lineNormalizer E),
        (elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))).subgroupOf
          (lineNormalizer E)⁆).map (originalProductMap s) := by
  let H := lineNormalizer E
  let J := elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))
  obtain ⟨j, hj, hj2, hjQ⟩ := exists_thompson_involution s
  have hjC : j ∈ centralizer (E : Set G) := thompson_le_centralizer s hj
  let jH : H := ⟨j, centralizer_le_normalizer (E : Set G) hjC⟩
  let t := (originalProductMap s jH).2
  have hjimage : originalProductMap s jH = (1, t) := by
    have hc := originalProductMap_centralizer s ⟨j, hjC⟩
    have hc1 := congrArg Prod.fst hc
    exact Prod.ext hc1 rfl
  have ht : t ^ 2 = 1 := by
    have hjH2 : jH ^ 2 = 1 := Subtype.ext hj2
    have hm := congrArg (fun x : H => (originalProductMap s x).2) hjH2
    simpa only [map_pow, Prod.pow_snd, map_one, Prod.snd_one] using hm
  have hnt : t ≠ 1 := by
    intro ht1
    have hk : jH ∈ (originalProductMap s).ker := by
      change originalProductMap s jH = 1
      rw [hjimage, ht1]
      rfl
    apply hjQ
    rw [originalProductMap_ker] at hk
    exact mem_map_of_mem H.subtype hk
  rw [map_commutator, himage]
  apply second_factor_le_commutator _ t ht hnt
  rw [← hjimage]
  exact mem_map_of_mem _ (show jH ∈ J.subgroupOf H from hj)

/-- Under the separately supplied residual-image equality, the original residual
is generated by its commutators with the original Thompson subgroup. -/
theorem lineX_eq_commutator_thompson_of_image (s : Inputs M Y T V E)
    (himage : ((lineX E).subgroupOf (lineNormalizer E)).map (originalProductMap s) =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3))) :
    lineX E = ⁅lineX E, elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))⁆ := by
  let H := lineNormalizer E
  let F := (lineX E).subgroupOf H
  let J := elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))
  let K := J.subgroupOf H
  have hXH : lineX E ≤ H :=
    (lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))
  have hJH : J ≤ H :=
    (thompson_le_centralizer s).trans (centralizer_le_normalizer (E : Set G))
  have hmapF : F.map H.subtype = lineX E := map_subgroupOf_eq_of_le hXH
  have hmapK : K.map H.subtype = J := map_subgroupOf_eq_of_le hJH
  have hquot : F.map (QuotientGroup.mk' (pCore 2 H)) ≤
      (⁅F, K⁆).map (QuotientGroup.mk' (pCore 2 H)) := by
    apply (map_le_map_iff_of_injective
      (f := (originalProductEquiv s).toMonoidHom) (originalProductEquiv s).injective).mp
    simpa only [map_map, originalProductMap, quotientMap] using image_le_commutator s himage
  have hFK : F ≤ ⁅F, K⁆ := residualPerfect_le_commutator_of_quotient
    (pCore 2 H) F K pCore_normal pCore_isPGroup (relative_lineX_residual_perfect E) hquot
  apply le_antisymm
  · have hm := map_mono (f := H.subtype) hFK
    rwa [map_commutator, hmapF, hmapK] at hm
  · exact le_normalizer_iff_commutator_le_left.mp
      (hJH.trans (lineNormalizer_le_normalizer_lineX E))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification.ThompsonLift
