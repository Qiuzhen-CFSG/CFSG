module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizerBound
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Kernel
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreFixedPoints
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The exceptional centralizer has Sylow index at most two

The image of the original U_H fixes exactly two letters in the natural
six-letter action. Since T normalizes U_H, the T-orbit of the letter fixed
by the selected A₅ pair has at most two elements. Its stabilizer normalizes
that pair: the actual permutation kernel is a normalizing two-group and
the pair is two-perfect. It therefore normalizes C_T(K), and when this
group has order two it centralizes it. Orbit--stabilizer gives
[T:C_T(C_T(K))] ≤ 2 on the original subgroups.

Source: Aschbacher--Smith, 13.5.15(7), printed p.920.
-/

public noncomputable section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalIndex
open Section08.SourceCompletion Section07.NaturalAction
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks

variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

private theorem permutation_subgroup_image (A : Subgroup G) (hAL : A ≤ D.L) :
    (A.subgroupOf D.LT).map (permutation d) = (A.subgroupOf D.L).map (localMap d) := by
  ext s
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x,hAL hx⟩,hx,?_⟩
    exact (permutation_L d ⟨x,hAL hx⟩).symm
  · rintro ⟨x,hx,rfl⟩
    exact ⟨inclusion le_sup_left x,hx,permutation_L d x⟩

private theorem permutation_kernel_two
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    IsPGroup 2 (permutation d).ker := by
  apply kernel_isTwoGroup_of_supplement D.L D.T d.normalizes_L
  have he : (permutation d).comp (inclusion (show D.L ≤ D.LT from le_sup_left)) =
      localMap d := by
    apply MonoidHom.ext
    intro l
    exact permutation_L d l
  rw [he]
  exact SourceStar.local_kernel_two d e

private theorem five_image_eq_stabilizer (a : alternatingGroup (Fin 6)) :
    FivePair.five.map (MulAut.conj a.val).toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 6)) (a.val 5) ⊓ alternatingGroup (Fin 6) := by
  rw [FivePair.five,map_inf _ _ _ (MulAut.conj a.val).injective,
    conjugate_alternating,←MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

/-- Fixing the original selected letter normalizes the actual two-perfect pair,
not just its permutation image. -/
theorem point_stabilizer_normalizes_pair
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (t : D.T) (ht : permutation d (inclusion le_sup_right t) (a.val 5) = a.val 5) :
    (t : G) ∈ normalizer (NormalBranch.K D g.val : Set G) := by
  let K := NormalBranch.K D g.val
  let P := K.subgroupOf D.LT
  let f : D.LT →* Equiv.Perm (Fin 6) := permutation d
  have hTP : (D.T : Subgroup G) ≤ D.LT := le_sup_right
  change f (inclusion hTP t) (a.val 5) = a.val 5 at ht
  have hKP : K ≤ D.LT := hK.trans le_sup_left
  have hP : IsPPerfect 2 P := hp.of_surjective
    (subgroupOfEquivOfLe hKP).symm.toMonoidHom (subgroupOfEquivOfLe hKP).symm.surjective
  have hker : IsPGroup 2 f.ker := permutation_kernel_two d e
  have hnorm : f.ker ≤ normalizer (P : Set D.LT) := by
    have hle : f.ker ≤ pCore 2 D.LT := le_sSup ⟨inferInstance,hker⟩
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (SourcePairResidual.twoCore_normalizes_pair h g
      (mem_map_of_mem D.LT.subtype (hle hx))) y.val
  have him : P.map f =
      MulAction.stabilizer (Equiv.Perm (Fin 6)) (a.val 5) ⊓ alternatingGroup (Fin 6) :=
    (permutation_subgroup_image d K hK).trans (hi.trans (five_image_eq_stabilizer a))
  have hnative : f (inclusion hTP t) ∈ normalizer (P.map f : Set _) := by
    rw [him]
    exact inf_normalizer_le_normalizer_inf
      ⟨(MulAction.stabilizer (Equiv.Perm (Fin 6)) (a.val 5)).le_normalizer ht,
        le_normalizer_of_normal (mem_top _)⟩
  have htP : inclusion hTP t ∈
      normalizer (P : Set D.LT) := by
    rw [←comap_normalizer_map_of_pPerfect f P hP hker hnorm]
    exact hnative
  rw [←subgroupOf_normalizer_eq hKP] at htP
  exact htP

/-- In the exceptional order-two case, the literal C_T(C_T(K)) has index
at most two in the original Sylow subgroup. -/
theorem exceptional_sylow_centralizer_index
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH)
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hc : Nat.card ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    ((D.T : Subgroup G) ⊓ centralizer
      (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) :
        Subgroup G) : Set G)).relIndex (D.T : Subgroup G) ≤ 2 := by
  classical
  let K := NormalBranch.K D g.val
  let C := (D.T : Subgroup G) ⊓ centralizer (K : Set G)
  let f : D.LT →* Equiv.Perm (Fin 6) := permutation d
  have hTP : (D.T : Subgroup G) ≤ D.LT := le_sup_right
  let fT := f.comp (inclusion hTP)
  let : MulAction D.T (Fin 6) := MulAction.compHom (Fin 6) fT
  let B := MulAction.stabilizer D.T (a.val 5)
  have hB : B ≤ ((D.T : Subgroup G) ⊓ centralizer (C : Set G)).subgroupOf D.T := by
    have hBN : B.map (D.T : Subgroup G).subtype ≤ normalizer (C : Set G) := by
      rintro _ ⟨t,ht,rfl⟩
      have htK := point_stabilizer_normalizes_pair d h e g hK hp a hi t ht
      exact inf_normalizer_le_normalizer_inf
        ⟨(D.T : Subgroup G).le_normalizer t.property,
          normalizer_le_normalizer_centralizer K htK⟩
    have hBC := centralizes_of_normalizes_card_two hc hBN
    intro t ht
    exact ⟨t.property,hBC (mem_map_of_mem _ ht)⟩
  have hidx : ((D.T : Subgroup G) ⊓ centralizer (C : Set G)).relIndex D.T ≤ B.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) (index_dvd_of_le hB)
  apply hidx.trans
  rw [MulAction.index_stabilizer]
  obtain ⟨b,hb,_⟩ := QuadraticSource.source_even_flag d
  let A := (D.UH.subgroupOf D.LT).map f
  have hUL : D.UH ≤ D.L := (closure_reduction h hseed hn).2.2
  have hA : A = pointCoreEven.map (MulAut.conj b.val).toMonoidHom :=
    (permutation_subgroup_image d D.UH hUL).trans
      (SourcePointCore.closure_image_eq_point_core d h e hseed hn hU b hb)
  have him : (K.subgroupOf D.LT).map f =
      MulAction.stabilizer (Equiv.Perm (Fin 6)) (a.val 5) ⊓ alternatingGroup (Fin 6) :=
    (permutation_subgroup_image d K hK).trans (hi.trans (five_image_eq_stabilizer a))
  have hfix : ∀ p ∈ A, p (a.val 5) = a.val 5 := by
    intro p hpA
    have hpK : p ∈ (K.subgroupOf D.LT).map f :=
      map_mono (subgroupOf_mono D.LT (show D.UH ≤ K from le_sup_left)) hpA
    exact (him ▸ hpK).1
  have hTN : (D.T : Subgroup G) ≤ normalizer (D.UH : Set G) :=
    h.T_le_H.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have horbit : MulAction.orbit D.T (a.val 5) ⊆ ({b.val 4,b.val 5} : Set (Fin 6)) := by
    rintro y ⟨t,rfl⟩
    have htU : inclusion hTP t ∈
        normalizer (D.UH.subgroupOf D.LT : Set D.LT) := by
      have hULT : D.UH ≤ D.LT := hUL.trans le_sup_left
      rw [←subgroupOf_normalizer_eq hULT]
      exact hTN t.property
    have htA : fT t ∈ normalizer (A : Set _) :=
      (D.UH.subgroupOf D.LT).le_normalizer_map f (mem_map_of_mem f htU)
    have hy : ∀ p ∈ A, p (fT t (a.val 5)) = fT t (a.val 5) := by
      intro p hpA
      have hpin : (fT t)⁻¹ * p * fT t ∈ A := by
        have hinv : (fT t)⁻¹ ∈ normalizer (A : Set (Equiv.Perm (Fin 6))) :=
          (normalizer (A : Set (Equiv.Perm (Fin 6)))).inv_mem htA
        simpa only [inv_inv] using (mem_normalizer_iff.mp hinv p).mp hpA
      have he := hfix _ hpin
      change (fT t).symm (p (fT t (a.val 5))) = a.val 5 at he
      exact (Equiv.symm_apply_eq _).mp he
    rw [hA] at hy
    exact (conjugate_pointCoreEven_fixed_iff b.val _).mp hy
  calc
    (MulAction.orbit D.T (a.val 5)).ncard ≤ ({b.val 4,b.val 5} : Set (Fin 6)).ncard :=
      Set.ncard_le_ncard horbit
    _ = 2 := Set.ncard_pair (b.val.injective.ne (by decide))

/-- Extend the original centralizer in T to a Sylow subgroup of C_G(C),
retaining its exact relative index, as used by the local-family argument. -/
theorem exists_exceptional_centralizer_sylow
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH)
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hc : Nat.card ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    let J := centralizer (C : Set G)
    let T₀ := (D.T : Subgroup G) ⊓ J
    ∃ S : Sylow 2 J, T₀.subgroupOf J ≤ S ∧
      (T₀.subgroupOf J).relIndex (S : Subgroup J) ≤ 2 := by
  dsimp only
  let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
  let J := centralizer (C : Set G)
  let T₀ := (D.T : Subgroup G) ⊓ J
  obtain ⟨S,hS⟩ := ((D.T.isPGroup'.to_le (show T₀ ≤ (D.T : Subgroup G) from inf_le_left)).comap_subtype
    (K := J)).exists_le_sylow
  let B := (S : Subgroup J).map J.subtype
  have hTB : T₀ ≤ B := by
    intro x hx
    exact mem_map_of_mem J.subtype (hS (show (⟨x,hx.2⟩ : J) ∈ T₀.subgroupOf J from hx))
  obtain ⟨R,hBR⟩ := (S.isPGroup'.map J.subtype).exists_le_sylow
  have hBT : Nat.card B ≤ Nat.card D.T :=
    (card_le_of_le hBR).trans_eq (Nat.card_congr (R.equiv D.T).toEquiv)
  have hidx : T₀.relIndex B ≤ T₀.relIndex (D.T : Subgroup G) := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.card T₀) _ Nat.card_pos
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) T₀ B bot_le hTB
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) T₀ (D.T : Subgroup G) bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at h1 h2
    rw [h1,h2]
    exact hBT
  have hbound : T₀.relIndex B ≤ 2 := hidx.trans
    (exceptional_sylow_centralizer_index d h e hseed hn hU g hK hp a hi hc)
  refine ⟨S,hS,?_⟩
  have he := relIndex_map_map_of_injective (T₀.subgroupOf J) (S : Subgroup J) J.subtype_injective
  rw [map_subgroupOf_eq_of_le (show T₀ ≤ J from inf_le_right)] at he
  exact he ▸ hbound

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalIndex
