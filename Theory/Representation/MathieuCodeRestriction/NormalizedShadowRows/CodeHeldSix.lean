module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeHeldCubic
public import Theory.GroupTheory.PerfectSmallNormalizerAction
public import Mathlib.GroupTheory.GroupAction.Period
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# The Held local obstruction to a full alternating-six section

In each literal max3/max4 quotient, two commuting even six-point
permutations have lifts with a commutator surviving the two-core. A perfect
subgroup with full two-core quotient A₆ would embed in the six-point action:
its solvable kernel is simultaneously a two-group and a three-group. Its
image is the entire A₆, and it centralizes the small action kernel. Changing
lifts by that central kernel contradicts the native commutator calculation.

The full-Sylow maximal two-local catalogue then excludes a perfect subgroup
with A₆ two-core quotient and nontrivial two-core in Held. The original
Chapter12 residual application is supplied by `M22CodeHeldExcluded`.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, using A.3.12;
GLS3 Table 5.3p and the unchanged ATLAS HeG1 degree-2058/max3/max4 words.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace MathieuCode.NormalizedShadowRows.HeldSix
open Held.LocalPairs.PairCoverage Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound

@[expose] def firstLift (i : Bool) : localOvergroup i := adjacent i 0 * adjacent i 1
@[expose] def secondLift (i : Bool) : localOvergroup i := adjacent i 3 * adjacent i 4
@[expose] def defect (i : Bool) : localOvergroup i :=
  firstLift i * secondLift i * (firstLift i)⁻¹ * (secondLift i)⁻¹

private theorem defect_rep (i : Bool) : Held.representation (defect i).val =
    (adjacentPerm i 0 * adjacentPerm i 1) * (adjacentPerm i 3 * adjacentPerm i 4) *
      (adjacentPerm i 0 * adjacentPerm i 1)⁻¹ * (adjacentPerm i 3 * adjacentPerm i 4)⁻¹ := by
  simp only [defect,firstLift,secondLift,Subgroup.coe_mul,Subgroup.coe_inv,
    map_mul,map_inv,representation_adjacent_table]

private theorem defect_not_core (i : Bool) : defect i ∉ pCore 2 (localOvergroup i) := by
  let p := Held.representation (defect i).val
  have h3 : p ^ 3 • (0 : Fin 2058) = 0 := by
    change (p ^ 3) 0 = 0
    dsimp only [p]
    rw [defect_rep]
    cases i <;> decide +kernel
  have h1 : ¬ p • (0 : Fin 2058) = 0 := by
    change ¬ p 0 = 0
    dsimp only [p]
    rw [defect_rep]
    cases i <;> decide +kernel
  have hd : MulAction.period p (0 : Fin 2058) ∣ 3 :=
    MulAction.pow_smul_eq_iff_period_dvd.mp h3
  have hn : MulAction.period p (0 : Fin 2058) ≠ 1 := by
    intro he
    apply h1
    simpa using (MulAction.pow_smul_eq_iff_period_dvd.mpr
      (show MulAction.period p (0 : Fin 2058) ∣ 1 by rw [he]))
  have hp : MulAction.period p (0 : Fin 2058) = 3 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left hn
  intro hc
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := localOvergroup i)) ⟨defect i,hc⟩
  have hpow : p ^ (2 ^ n) = 1 := by
    have hh := congrArg (fun g : pCore 2 (localOvergroup i) => Held.representation g.val.val) hn
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using hh
  have hdiv : 3 ∣ 2 ^ n := by
    rw [←hp,←MulAction.pow_smul_eq_iff_period_dvd,hpow,one_smul]
  exact (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hdiv)

private theorem action_adjacent (i : Bool) (k : Fin 5) :
    SixPoint.action i (adjacent i k) =
      (if i then SixPoint.first i * SixPoint.second i else SixPoint.second i) ^ k.val *
        SixPoint.first i *
        ((if i then SixPoint.first i * SixPoint.second i else SixPoint.second i) ^ k.val)⁻¹ := by
  have hg0 : SixPoint.action i (generator i 0) = SixPoint.first i := by
    cases i <;> exact SixPoint.action_first _
  have hg1 : SixPoint.action i (generator i 1) = SixPoint.second i := by
    cases i <;> exact SixPoint.action_second _
  have hc : SixPoint.action i (cycle i) =
      if i then SixPoint.first i * SixPoint.second i else SixPoint.second i := by
    cases i <;> simp only [cycle,Bool.false_eq_true,↓reduceIte,map_mul,hg0,hg1]
  simp only [adjacent,map_mul,map_pow,map_inv,hg0,hc]

theorem native_lifts (i : Bool) :
    SixPoint.action i (firstLift i) ∈ alternatingGroup (Fin 6) ∧
    SixPoint.action i (secondLift i) ∈ alternatingGroup (Fin 6) ∧
    Commute (SixPoint.action i (firstLift i)) (SixPoint.action i (secondLift i)) ∧
    defect i ∉ pCore 2 (localOvergroup i) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [firstLift,map_mul,action_adjacent]
    rw [Equiv.Perm.mem_alternatingGroup]
    cases i <;> decide +kernel
  · simp only [secondLift,map_mul,action_adjacent]
    rw [Equiv.Perm.mem_alternatingGroup]
    cases i <;> decide +kernel
  · simp only [firstLift,secondLift,map_mul,action_adjacent]
    change _ * _ = _ * _
    cases i <;> decide +kernel
  · exact defect_not_core i

open scoped commutatorElement

private theorem small_kernel (i : Bool) :
    IsPGroup 3 (SixPoint.quotientAction i).ker :=
  isPGroup_iff_card_dvd_pow.mpr ⟨1, by simpa using
    Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i⟩

theorem not_six_section_quotient (i : Bool) (B : Subgroup (LocalQuotient i))
    [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let f := SixPoint.quotientAction i
  let r := f.comp B.subtype
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hk3 : IsPGroup 3 r.ker := by
    change IsPGroup 3 (f.ker.comap B.subtype)
    exact (small_kernel i).comap_subtype
  let : Group.IsNilpotent r.ker := hk3.isNilpotent
  have hk2 := PerfectCoreTwoExtension.ker_isTwoGroup r
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ hk2 hk3)
  have hBA : B.map f ≤ alternatingGroup (Fin 6) := by
    rw [← B.commutator_eq_self, map_commutator]
    exact (commutator_mono le_top le_top).trans (by
      rw [← commutator_def, alternatingGroup.commutator_perm_eq (by norm_num)])
  have hmap : B.map f = alternatingGroup (Fin 6) := by
    apply eq_of_le_of_card_ge hBA
    have hd : Nat.card (alternatingGroup (Fin 6)) ≤ Nat.card B := by
      rw [← Nat.card_congr e.toEquiv]
      exact Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)
    have hc := Nat.card_congr (MonoidHom.ofInjective hr).toEquiv
    rw [show r.range = B.map f from by rw [MonoidHom.range_comp,range_subtype]] at hc
    rwa [←hc]
  have hBker : B ≤ centralizer (f.ker : Set (LocalQuotient i)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_perfect_normalizer_card_le_four
    · rw [normalizer_eq_top]; exact le_top
    · exact (Nat.le_of_dvd (by decide : 0 < 3)
        (Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i)).trans (by decide)
  let P := (alternatingGroup (Fin 6)).comap f
  have hP : P = B ⊔ f.ker := by dsimp only [P]; rw [←hmap,comap_map_eq]
  let : IsMulCommutative f.ker := by
    let : IsCyclic f.ker := isCyclic_of_card_dvd_prime
      (Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i)
    infer_instance
  have hPC : P ≤ centralizer (f.ker : Set (LocalQuotient i)) := by
    rw [hP]
    exact sup_le hBker (commutator_eq_bot_iff_le_centralizer.mp
      (commutator_self_eq_bot_iff.mpr inferInstance))
  let g := f.comp P.subtype
  have hgc : g.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hPC y.property) x.val hx).symm
  obtain ⟨hx,hy,hxy,hdef⟩ := native_lifts i
  let x : P := ⟨localQuotientMap i (firstLift i),hx⟩
  let y : P := ⟨localQuotientMap i (secondLift i),hy⟩
  obtain ⟨a,ha,hax⟩ := show f x.val ∈ B.map f by rw [hmap]; exact hx
  obtain ⟨b,hb,hby⟩ := show f y.val ∈ B.map f by rw [hmap]; exact hy
  have hab : Commute (⟨a,ha⟩ : B) (⟨b,hb⟩ : B) := by
    apply hr
    change f (a*b) = f (b*a)
    rw [map_mul,map_mul,hax,hby]
    exact hxy.eq
  let aP : P := ⟨a,by rw [hP]; exact (show B ≤ B ⊔ f.ker from le_sup_left) ha⟩
  let bP : P := ⟨b,by rw [hP]; exact (show B ≤ B ⊔ f.ker from le_sup_left) hb⟩
  have habP : Commute aP bP := Subtype.ext (congrArg (fun t : B => t.val) hab.eq)
  have hc : ⁅x,y⁆ = 1 :=
    (CentralExtension.commutator_eq_of_image_eq g hgc hax.symm hby.symm).trans habP.commutator_eq
  apply hdef
  apply (QuotientGroup.eq_one_iff _).mp
  exact congrArg (fun t : P => t.val) hc

theorem not_six_section_local (i : Bool) (B : Subgroup (localOvergroup i))
    [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let q := localQuotientMap i
  let A := B.map q
  let : Group.IsPerfect A := Group.IsPerfect.map q
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 (localOvergroup i))).ker.subgroupOf B)
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk
  exact not_six_section_quotient i A (a.symm.trans e)

private theorem candidate_not_six_section (i : Fin 3)
    (B : Subgroup (Held.TwoLocalCandidates.subgroup i)) [hperf : Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 from by omega) with rfl | rfl | rfl
  · exact @not_six_section_local false B hperf e
  · exact @not_six_section_local true B hperf e
  · have hd : 5 ∣ Nat.card B := by
      have hh := card_quotient_dvd_card (pCore 2 B)
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hh
      exact (by decide : 5 ∣ Nat.factorial 6 / 2).trans hh
    have hh := hd.trans B.card_subgroup_dvd_card
    change 5 ∣ Nat.card Held.TwoLocalCandidates.max5 at hh
    rw [Held.InvolutionFixedData.TwoB.max5_card] at hh
    norm_num at hh

theorem held_not_six_section_of_core_ne_bot
    (S : Sylow 2 Held.He) (B : Subgroup Held.He) [Group.IsPerfect B]
    (hn : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (hc : pCore 2 B ≠ ⊥)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Held.He S T
  let a := MulAut.conj g
  let A := B.map a.toMonoidHom
  let b : B ≃* A := a.subgroupMap B
  let : Group.IsPerfect A := Group.IsPerfect.map a.toMonoidHom
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hnA : (T : Subgroup Held.He) ≤ normalizer (A : Set Held.He) := by
    have hh := (map_mono (f := a.toMonoidHom) hn).trans (B.le_normalizer_map a.toMonoidHom)
    change ((g • S : Sylow 2 Held.He) : Subgroup Held.He) ≤ _ at hh
    rwa [hg] at hh
  have hcA : pCore 2 A ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := b.toMonoidHom) _ b.injective).mp
    rw [pCore_map_iso,hz]
  let U := (pCore 2 A).map A.subtype
  have hU : U ≠ ⊥ := fun he => hcA ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp he)
  have hloc : IsTwoLocal (normalizer (U : Set Held.He)) :=
    ⟨U,hU,pCore_isPGroup.map A.subtype,rfl⟩
  have hnorm := normalizer_le_normalizer_characteristic_image A (pCore 2 A)
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal hloc
  have hTN := hnA.trans (hnorm.trans hNN)
  have hAN := A.le_normalizer.trans (hnorm.trans hNN)
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN hTN
  obtain ⟨i,k,hk⟩ := hcatalogue R hR hRn hRe (hNR ▸ hN)
  let d : N ≃* Held.TwoLocalCandidates.subgroup i :=
    (MulEquiv.subgroupCongr (hNR.trans hk)).trans ((MulAut.conj k).subgroupMap _).symm
  let C := (A.subgroupOf N).map d.toMonoidHom
  let c : C ≃* A :=
    (d.subgroupMap (A.subgroupOf N)).symm.trans (subgroupOfEquivOfLe hAN)
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  exact candidate_not_six_section i C (cq.trans (bq.symm.trans e))

end MathieuCode.NormalizedShadowRows.HeldSix
