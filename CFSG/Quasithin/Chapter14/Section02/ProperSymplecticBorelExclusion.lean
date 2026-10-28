module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleSource
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableSupplement
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The proper-completion symplectic Borel exclusion

The selected local C-component B is proper in the normal containing
C-component L. If Y lies in L, normalization by the original Sylow and
the solvable quotient show that B and Y generate L. Restricting that
Sylow to L gives two overgroups: the proper join with B, and the solvable
join with Y. The actual symplectic quotient sends them to overgroups of
the same full Sylow, contradicting the parabolic supplement theorem.

The final theorem applies this to the literal K₁, source residual Y and
canonical solvable residual L of the original 14.2.15 completion. It
derives full Sylow, properness, normalization and solvability internally.
The earlier containing-family selection and A.3.18 placement Y≤L remain
explicit; characteristic two of the completion is not assumed.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The source Borel contradiction with a proper local component, retaining
its original Sylow and actual containing-component quotient. -/
theorem proper_symplectic_solvable_supplement_false
    (T : Sylow 2 G) (B L Y : Subgroup G)
    (hB : B ∈ ChapterA.Section03.localCComponents T)
    (hL : L.IsCComponent) (hBL : B ≤ L) (hne : B ≠ L) (hYL : Y ≤ L)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hgen : B ⊔ Y ⊔ (T : Subgroup G) = ⊤)
    (hsol : Group.IsSolvable (Y ⊔ (T : Subgroup G) : Subgroup G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.symplecticGroup (Fin 2) F) : False := by
  let N := B ⊔ Y
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf hTB hTY).trans (normalizer_inf_normalizer_le_normalizer_sup B Y)
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique
    (hgen ▸ sup_le N.le_normalizer hTN))
  let : Group.IsNilpotent (G ⧸ N) :=
    (isPGroup_quotient_of_sup_eq_top N T T.isPGroup' hgen).isNilpotent
  let := hL.perfect
  have hNL : N = L := le_antisymm (sup_le hBL hYL)
    ((le_solvableResidual_of_isPerfect L).trans (solvableResidual_le_of_solvable_quotient N))
  obtain ⟨Q,hQ⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  let U := (Q : Subgroup L).map L.subtype
  have hUL : U ≤ L := map_subtype_le _
  have hUT : U ≤ (T : Subgroup G) := by
    rw [show U = (Q : Subgroup L).map L.subtype from rfl,hQ,subgroupOf_map_subtype]
    exact inf_le_left
  let D := B ⊔ U
  have hDL : D ≤ L := sup_le hBL hUL
  have hBD : (B.subgroupOf D).IsCComponent :=
    hB.subgroupOf_of_le le_sup_left (sup_le le_sup_left (hUT.trans le_sup_right))
  have hD : D.subgroupOf L ≠ ⊤ := by
    intro ht
    have he : D = L := le_antisymm hDL (subgroupOf_eq_top.mp ht)
    rw [he] at hBD
    exact hne (le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hBD)))
  let A := Y ⊔ U
  have hAL : A ≤ L := sup_le hYL hUL
  let _ := hsol
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (sup_le_sup_left hUT Y))
  have hAS : Group.IsSolvable (A.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hAL).toMonoidHom) (subgroupOfEquivOfLe hAL).injective
  have hjoin : D.subgroupOf L ⊔ A.subgroupOf L = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hDL,map_subgroupOf_eq_of_le hAL,
      ←MonoidHom.range_eq_map,range_subtype]
    apply le_antisymm (sup_le hDL hAL)
    rw [←hNL]
    exact sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  exact Theory.SpecificGroups.SymplecticFour.proper_sylow_overgroup_sup_solvable_ne_top_of_twoGroup_kernel
    hF hn f hf (hk.symm ▸ pCore_isPGroup) Q (D.subgroupOf L) (A.subgroupOf L)
    (fun x hx => mem_sup_right (mem_map_of_mem L.subtype hx)) hD
    (fun x hx => mem_sup_right (mem_map_of_mem L.subtype hx)) hAS hjoin


open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original 14.2.15 source application of the symplectic Borel contradiction.
The earlier A.3.18 placement and the selected quotient remain explicit. -/
theorem source_proper_completion_symplectic_borel_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    sourceResidual M Mc ≤ L →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.symplecticGroup (Fin 2) F) → False := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  let Y := sourceResidual M Mc
  change Y ≤ L → Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.symplecticGroup (Fin 2) F) → False
  rintro hYL ⟨eL⟩
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  have hKC : K ≤ centralizer (centralInvolutions T : Set G) :=
    (le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hne : K ≠ L := fun he =>
    source_proper_completion_component_noncentral hG T hempty hM hu hmany hcard e
      H hH K S hST hgen hK hSN hcorea hs (he.ge.trans hKC)
  have hKX : K ≤ X := le_sup_left.trans le_sup_left
  have hYX : Y ≤ X := le_sup_right.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hKP : K.subgroupOf X ∈ Chapter1.L X P := by
    rw [hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSX hKX).mp ⟨hKX,hK⟩
  have hSY : S ≤ normalizer (Y : Set G) := hST.trans (hM.1.2.trans
    ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp (residualY_normal M Mc)))
  have hPK : (P : Subgroup X) ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [hPS,←subgroupOf_normalizer_eq hKX]
    exact comap_mono hSN
  have hPY : (P : Subgroup X) ≤ normalizer (Y.subgroupOf X : Set X) := by
    rw [hPS,←subgroupOf_normalizer_eq hYX]
    exact comap_mono hSY
  have hgenX : K.subgroupOf X ⊔ Y.subgroupOf X ⊔ (P : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hKX,
      map_subgroupOf_eq_of_le hYX,hP,←MonoidHom.range_eq_map,range_subtype]
  let : Group.IsSolvable (Y ⊔ (T : Subgroup G) : Subgroup G) :=
    source_residualSylow_solvable hG T hempty hM hu hmany hcard e
  let : Group.IsSolvable (Y ⊔ S : Subgroup G) := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (sup_le_sup_left hST Y))
  have hsol : Group.IsSolvable (Y.subgroupOf X ⊔ (P : Subgroup X) : Subgroup X) := by
    rw [hPS,←subgroupOf_sup hYX hSX]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (sup_le hYX hSX)).toMonoidHom)
      (subgroupOfEquivOfLe (sup_le hYX hSX)).injective
  have hneX : K.subgroupOf X ≠ L.subgroupOf X := by
    intro he
    apply hne
    have hm := congrArg (Subgroup.map X.subtype) he
    rwa [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hL.1] at hm
  let d := subgroupOfEquivOfLe hL.1
  let eX := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eL
  exact proper_symplectic_solvable_supplement_false P (K.subgroupOf X)
    (L.subgroupOf X) (Y.subgroupOf X) hKP.1 hL.2 (comap_mono hKL) hneX
    (comap_mono hYL) hPK hPY hgenX hsol hF hn eX

end CFSG.Quasithin.Chapter14.Section02
