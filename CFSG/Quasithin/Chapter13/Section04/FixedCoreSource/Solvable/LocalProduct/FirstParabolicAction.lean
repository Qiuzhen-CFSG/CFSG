module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstParabolicCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction

/-!
# The literal action-core preimage on the first residual parabolic

Use the actual conjugation action of P=L₁T on the five-dimensional V,
its range, and the restriction from the original T. The subgroup defined
here is exactly the preimage in T of O₂ of that range. In the ordinary
row C_L(V)=O₂(L); the two-group quotient LT/L then makes C_LT(V) a
two-group. Core lifting therefore identifies this literal preimage with
O₂(P), rather than with the core of an arbitrarily chosen action model.

The final theorem uses this equality in the combined short-block product
and uniqueness theorem. The source normalizer description
M₁=N_LT(V₁)=L₁T and the earlier V≤J(R₁) input still require their original
source assembly. The covered row is not identified with O₂(L₁T):
Notation 13.2.1 allows the actual preimage to be larger there.
The non-block branch, C₃ chamber and ambient fusion remain with
qt-d-1341-solvable-source; earlier-source discharge remains with
qt-d-1341-fixed-core-source and its existing producers.
Source: Aschbacher–Smith Notation 13.2.1 and 13.4.8, pp.877,904–905.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The ordinary component quotient makes the actual LT-module kernel a two-group. -/
theorem local_module_centralizer_isTwo_of_ordinary
    (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    IsPGroup 2 ((L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) : Subgroup G) := by
  let X := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : N ⊔ (T : Subgroup G).subgroupOf X = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ X from le_sup_left)
      (show (T : Subgroup G) ≤ X from le_sup_right)]
    exact subgroupOf_self X
  have hquot : IsPGroup 2 (X ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf X)
      T.isPGroup'.comap_subtype hgen
  let C := X ⊓ centralizer (V : Set G)
  let f : C →* (X ⧸ N) := (QuotientGroup.mk' N).comp (inclusion inf_le_left)
  let j : f.ker →* (centralizer (V : Set G)).subgroupOf L :=
    { toFun := fun a => ⟨⟨a.val.val, (QuotientGroup.eq_one_iff (N := N) (inclusion inf_le_left a.val)).mp a.property⟩,
        a.val.property.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hh
    exact Subtype.ext (Subtype.ext (congrArg (fun x => x.val.val) hh))
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcent : IsPGroup 2 ((centralizer (V : Set G)).subgroupOf L) := by
    rw [D.centralizer_eq_core_of_simple e.isSimpleGroup]
    exact pCore_isPGroup
  have hker : IsPGroup 2 f.ker := hcent.of_injective j hj
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup f hker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

/-- Conjugation by the actual residual parabolic on the original chosen V. -/
def firstParabolicAction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) :
    (firstCentralizerResidual L z ⊔ (T : Subgroup G) : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion
    ((sup_le ((firstCentralizerResidual_le L z).trans inf_le_left |>.trans L.le_normalizer)
      D.sylow_normalizes_component).trans (normalizer_component_le_module h structural D m)))

/-- The literal preimage in T of the two-core of the first-parabolic action image. -/
def firstActionCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) : Subgroup G :=
  ((pCore 2 (firstParabolicAction h structural D m z).range).comap
    ((firstParabolicAction h structural D m z).rangeRestrict.comp
      (inclusion (show (T : Subgroup G) ≤ firstCentralizerResidual L z ⊔ (T : Subgroup G)
        from le_sup_right)))).map (T : Subgroup G).subtype

/-- Core lifting identifies the literal action preimage in the ordinary row. -/
theorem firstActionCore_eq_firstParabolicCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    firstActionCore h structural D m z = firstParabolicCore T L z := by
  let P := firstCentralizerResidual L z ⊔ (T : Subgroup G)
  let X := L ⊔ (T : Subgroup G)
  let f := firstParabolicAction h structural D m z
  have hPX : P ≤ X := sup_le_sup_right ((firstCentralizerResidual_le L z).trans inf_le_left) _
  have hk : f.ker = (centralizer (V : Set G)).subgroupOf P := by
    ext a
    change (inclusion _ a) ∈ V.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    apply ((local_module_centralizer_isTwo_of_ordinary D e).comap_subtype).to_le
    intro a ha
    exact ⟨hPX a.property,ha⟩
  have hpr : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hp
  have he := f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hpr
  have hRT := (firstParabolicCore_local_data (L := L) hz).1
  change ((pCore 2 f.range).comap (f.rangeRestrict.comp (inclusion
    (show (T : Subgroup G) ≤ P from le_sup_right)))).map (T : Subgroup G).subtype = P.pCoreIn 2
  apply le_antisymm
  · rintro x ⟨t,ht,rfl⟩
    exact ⟨inclusion le_sup_right t,he.le ht,rfl⟩
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨⟨a,hRT (mem_map_of_mem P.subtype ha)⟩,?_,rfl⟩
    exact he.ge ha

/-- Apply the short-block product theorem to the literal action-core preimage. -/
theorem centralizer_pair_quotient_of_short_block_firstActionCore
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstActionCore h structural D m z.val))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstActionCore h structural D m z.val)) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  obtain ⟨e⟩ := ordinary_of_short_core_marking D m hb
  have hR := firstActionCore_eq_firstParabolicCore h structural D m e hz
  generalize hRa : firstActionCore h structural D m z.val = R at hVJ ⊢
  have hRc : R = firstParabolicCore T L z.val := hRa.symm.trans hR
  clear hRa hR
  subst R
  exact centralizer_pair_quotient_of_short_block_firstParabolicCore
    h₀ h structural D m hb z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
