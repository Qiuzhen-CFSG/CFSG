module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCoreSize
public import Theory.SpecificGroups.PSL3Two.WreathCubicCentralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.FullRows

/-!
# Comparing the two original kernels in the collapsed enlargement

Write J=L₀T, X=O²(H), E=<N_G(T₁),H>, and K=<Xᴱ>. The original
binary-three wreath action has kernel exactly O₂(J). A cubic plane in
that actor has a three-group centralizer, so C_T(P) lies in O₂(J).
The literal factorization T=O₂(X)N_T(P) then gives
O₂(H)=O₂(X)O₂(J).

Under the remaining collapse O₂(X)≤O₂(K), this becomes
O₂(H)=O₂(K)O₂(J). In particular O₂(K) induces the full parabolic-core
action on the original module. Intersecting with K and applying the same
K/O₂(K) map identifies the image of O₂(J) with the previously computed
parabolic-core image, of order four. All relative normality, subgroup
intersections and conjugation maps retain their original carriers.

The final consumer constructs the natural action from the original source
guards and applies these identities to the actual remaining configuration.
Its exclusion and assembly of StabilizerNormalizerAt and HalfSylowUniqueAt
remain with qt-d-10-nona5-half-sylow-unique. Only ModuleChoiceAt is external,
finally discharged by qt-d-10-nona5-point-control. No exclusion is asserted
from these kernel identities alone.

Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The wreath lift has precisely the kernel of the original conjugation action. -/
theorem LiftData.kernel_eq_action_kernel {s : NaturalData D}
    {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz) : f.hom.ker = (joinAction D).ker := by
  ext g
  constructor
  · intro hg
    apply MulEquiv.ext
    intro v
    apply (fullCoordinates s hz).injective
    rw [f.equivariant,show f.hom g = 1 from hg,map_one]
    rfl
  · intro hg
    apply SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.action_injective
    rw [map_one]
    apply MulEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective w
    rw [←f.equivariant,show joinAction D g = 1 from hg]
    rfl

/-- The literal original two-core is the whole kernel of the selected wreath action. -/
theorem LiftData.kernel_eq_join_core {s : NaturalData D}
    {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz) : f.hom.ker = pCore 2 (localJoin T L) := by
  have hle : f.hom.ker ≤ pCore 2 (localJoin T L) := le_sSup ⟨inferInstance,f.kernel_two⟩
  apply le_antisymm hle
  rw [f.kernel_eq_action_kernel,joinAction_ker]
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  intro x hx
  have hm : (x : G) ∈ (localJoin T L).pCoreIn 2 := mem_map_of_mem _ hx
  rw [←D.sylow_centralizer_module hu,←s.full_eq_local] at hm
  exact hm.2

/-- The original Sylow centralizer of the cubic complement lies in the original join core. -/
theorem LiftData.cubic_centralizer_le_join_core {s : NaturalData D}
    {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz) {P : Subgroup G}
    (hPJ : P ≤ localJoin T L) (hP : IsPGroup 3 P) (hc : Nat.card P = 9) :
    (T : Subgroup G) ⊓ centralizer (P : Set G) ≤ (localJoin T L).pCoreIn 2 := by
  let J := localJoin T L
  let A := P.subgroupOf J
  let B := ((T : Subgroup G) ⊓ centralizer (P : Set G)).subgroupOf J
  have ha : IsPGroup 3 A := hP.of_equiv (subgroupOfEquivOfLe hPJ).symm
  have hd := ha.disjoint_of_coprime f.kernel_two (by decide : Nat.Coprime 3 2)
  have hi : Function.Injective (f.hom.subgroupMap A) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    change f.hom.subgroupMap A x = 1 at hx
    exact Subtype.ext (hd.le_bot ⟨x.property,congrArg Subtype.val hx⟩)
  have hcard : Nat.card (A.map f.hom) = 9 := by
    rw [←Nat.card_congr (MulEquiv.ofBijective (f.hom.subgroupMap A)
      ⟨hi,f.hom.subgroupMap_surjective A⟩).toEquiv]
    exact (Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv).trans hc
  have hcent : B.map f.hom ≤ centralizer (A.map f.hom : Set _) := by
    rintro _ ⟨b,hb,rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a,ha,rfl⟩
    have he : a * b = b * a := Subtype.ext (mem_centralizer_iff.mp hb.2 a ha)
    exact (map_mul f.hom a b).symm.trans ((congrArg f.hom he).trans (map_mul f.hom b a))
  have hzero := Matrix.PSL3Two.WreathPair.two_subgroup_centralizing_cubic_plane_eq_bot
    (A.map f.hom) (B.map f.hom) hcard
    (((T.isPGroup'.to_le inf_le_left).comap_subtype).map f.hom) hcent
  have hk : B ≤ f.hom.ker := (Subgroup.map_eq_bot_iff _).mp hzero
  have hcore : f.hom.ker ≤ pCore 2 J := le_sSup ⟨inferInstance,f.kernel_two⟩
  intro x hx
  let y : J := ⟨x,(show (T : Subgroup G) ≤ J from le_sup_right) hx.1⟩
  exact mem_map_of_mem J.subtype (hcore (hk (show y ∈ B from hx)))

namespace Parabolics
variable {H P : Subgroup G}

/-- The parabolic core is generated by the residual core and its cubic centralizer. -/
theorem Data.parabolic_core_le_residual_core_join_centralizer (h : Data D H)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H)) :
    H.pCoreIn 2 ≤ (residual H).pCoreIn 2 ⊔
      ((T : Subgroup G) ⊓ centralizer (P : Set G)) := by
  let C := (residual H).pCoreIn 2
  let Q := H.pCoreIn 2
  let N := (T : Subgroup G) ⊓ normalizer (P : Set G)
  have hCQ : C ≤ Q := pCoreIn_mono_of_normalizes (map_subtype_le _)
    (le_normalizer_embedded_pResidual 2 H)
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le] using
      pCoreIn_le_sylow H (T.subtype h.sylow_le)
  have hNC : N ≤ normalizer (C : Set G) :=
    inf_le_left.trans (hi.invariant.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hdis : Disjoint Q P := (isPGroup_pCoreIn 2 H).disjoint_of_coprime
    hi.odd_complement.isPGroup (by decide)
  have hcent : Q ⊓ normalizer (P : Set G) ≤ centralizer (P : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply le_trans _ hdis.le_bot
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp
          ((hi.complement_le.trans (map_subtype_le _)).trans
            (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))))
    · exact le_normalizer_iff_commutator_le_right.mp inf_le_right
  intro x hx
  have hx' : x ∈ (C : Set G) * (N : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left C N hNC]
    exact hi.normalizer_factor ▸ hQT hx
  obtain ⟨c,hc,n,hn,he⟩ := hx'
  have hnQ : n ∈ Q := by
    have hh := Q.mul_mem (Q.inv_mem (hCQ hc)) hx
    rwa [←he,inv_mul_cancel_left] at hh
  rw [←he]
  exact mul_mem_sup hc ⟨hn.1,hcent ⟨hnQ,hn.2⟩⟩

/-- In the original natural action the two parabolic cores differ only by the join kernel. -/
theorem Data.parabolic_core_eq_residual_core_join_core (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    H.pCoreIn 2 = (residual H).pCoreIn 2 ⊔ (localJoin T L).pCoreIn 2 := by
  apply le_antisymm
  · exact h.parabolic_core_le_residual_core_join_centralizer hi |>.trans
      (sup_le_sup_left (f.cubic_centralizer_le_join_core
        (hi.complement_le.trans ((map_subtype_le _).trans h.le_join))
        hi.odd_complement.isPGroup hP) _)
  · apply sup_le
    · exact pCoreIn_mono_of_normalizes (map_subtype_le _)
        (le_normalizer_embedded_pResidual 2 H)
    · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
        ((join_core_le_stabilizer D).trans (inf_le_left.trans h.sylow_le))
        (h.le_join.trans ((localJoin T L).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))

/-- Under collapse the containing core and the original join core generate the parabolic core. -/
theorem Data.collapsed_parabolic_core_eq_join (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    H.pCoreIn 2 = (enlargedResidual T L H).pCoreIn 2 ⊔ (localJoin T L).pCoreIn 2 := by
  have he := h.parabolic_core_eq_residual_core_join_core f hi hP
  apply le_antisymm (he.le.trans (sup_le_sup_right hc _))
  apply sup_le
  · exact (pCoreIn_mono_of_normalizes h.enlargedResidual_le_enlargement
      (le_normalizer_conjugateSpanBy _ _)).trans h.enlargement_core_le_parabolic_core
  · exact le_sup_right.trans he.ge

/-- Collapse makes the containing core induce the whole parabolic-core
action on the original full module, through the literal conjugation map. -/
theorem Data.collapsed_core_action_image (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D) =
      ((H.pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D) := by
  have he := h.collapsed_parabolic_core_eq_join f hi hP hc
  have hQJ : (enlargedResidual T L H).pCoreIn 2 ≤ localJoin T L :=
    (le_sup_left.trans he.ge).trans ((pCoreIn_le 2 H).trans h.le_join)
  have hzQ : (((localJoin T L).pCoreIn 2).subgroupOf (localJoin T L)).map
      (joinAction D) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [←f.kernel_eq_action_kernel,f.kernel_eq_join_core]
    intro x hx
    obtain ⟨y,hy,he⟩ := hx
    exact (Subtype.ext he : y=x) ▸ hy
  rw [he,subgroupOf_sup hQJ (pCoreIn_le 2 _),Subgroup.map_sup,hzQ,sup_bot_eq]

/-- The parabolic intersection core is the intersection with the core of H. -/
theorem Data.parabolic_intersection_core_eq_inf (h : Data D H) :
    (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2 =
      H.pCoreIn 2 ⊓ enlargedResidual T L H := by
  rw [h.parabolic_intersection]
  have hn : H ≤ normalizer (H ⊓ enlargedResidual T L H : Set G) :=
    (le_inf H.le_normalizer (le_sup_right.trans (le_normalizer_conjugateSpanBy _ _))).trans
      inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · exact le_inf (pCoreIn_mono_of_normalizes inf_le_left hn)
      ((pCoreIn_le 2 _).trans inf_le_right)
  · exact (le_inf (le_inf (inf_le_left.trans (pCoreIn_le 2 H)) inf_le_right) inf_le_left).trans
      (inf_pCoreIn_le_of_le 2 (show H ⊓ enlargedResidual T L H ≤ H from inf_le_left))

/-- The original action kernel has exactly the parabolic-core image in the containing quotient. -/
theorem Data.collapsed_join_core_image (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    quotientImage (enlargedResidual T L H) ((localJoin T L).pCoreIn 2) =
      quotientImage (enlargedResidual T L H)
        ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2) := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  let R := (localJoin T L).pCoreIn 2
  have hRK : (Q ⊔ R) ⊓ K = Q ⊔ (R ⊓ K) := by
    have hRQ : R ≤ normalizer (Q : Set G) :=
      ((join_core_le_stabilizer D).trans inf_le_left).trans
        (h.sylow_normalizes_enlargedResidual.trans
          (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    apply le_antisymm
    · rintro x ⟨hx,hxK⟩
      have hx' : x ∈ (Q : Set G) * (R : Set G) := by
        rwa [←coe_mul_of_right_le_normalizer_left Q R hRQ]
      obtain ⟨q,hq,r,hr,he⟩ := hx'
      have hrK : r ∈ K := by
        have hh := K.mul_mem (K.inv_mem (pCoreIn_le 2 K hq)) hxK
        rwa [←he,inv_mul_cancel_left] at hh
      rw [←he]
      exact mul_mem_sup hq ⟨hr,hrK⟩
    · exact sup_le (le_inf le_sup_left (pCoreIn_le 2 K))
        (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  have he := h.parabolic_intersection_core_eq_inf
  rw [h.collapsed_parabolic_core_eq_join f hi hP hc,hRK] at he
  rw [he]
  unfold quotientImage
  rw [subgroupOf_sup (pCoreIn_le 2 K) inf_le_right,Subgroup.map_sup]
  have hzQ : (Q.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    intro x hx
    obtain ⟨y,hy,he⟩ := hx
    exact (Subtype.ext he : y=x) ▸ hy
  rw [hzQ,bot_sup_eq,inf_subgroupOf_right]

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Every remaining source configuration has a four-element image of the
original module-action kernel in its containing quotient. -/
theorem SourceCubicNormalizerEnlargement.exists_action_kernel_image
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
        (residual H) P (enlargement T L H) I ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
      (p % 24 = 11 ∨ p % 24 = 13) ∧
      (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      H.pCoreIn 2 = (residual H).pCoreIn 2 ⊔ (localJoin T L).pCoreIn 2 ∧
      H.pCoreIn 2 = (enlargedResidual T L H).pCoreIn 2 ⊔ (localJoin T L).pCoreIn 2 ∧
      (((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D) =
        ((H.pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D) ∧
      Nat.card (quotientImage (enlargedResidual T L H) ((localJoin T L).pCoreIn 2)) = 4 := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  refine ⟨H,P,I,p,h,hs,hK,hp,ho,hm,h24,hcollapse,
    h.parabolic_core_eq_residual_core_join_core f hs.toLocalInput hP,
    h.collapsed_parabolic_core_eq_join f hs.toLocalInput hP hcollapse,
    h.collapsed_core_action_image f hs.toLocalInput hP hcollapse,?_⟩
  rw [h.collapsed_join_core_image f hs.toLocalInput hP hcollapse]
  exact h.collapsed_quotient_core_card hn hs hK hp ho hm hmod hcollapse

/-- The actual two source contracts reduce to a configuration in which the
original action kernel has the forced four-element image. -/
theorem sourceContracts_or_cubicActionKernelImage (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, Data D H ∧
          H.pCoreIn 2 = (enlargedResidual T L H).pCoreIn 2 ⊔ (localJoin T L).pCoreIn 2 ∧
          Nat.card (quotientImage (enlargedResidual T L H) ((localJoin T L).pCoreIn 2)) = 4 := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,_,_,_,h,_,_,_,_,_,_,_,_,he,_,hfour⟩ := hc.exists_action_kernel_image
    exact Or.inr ⟨L,D,hc,H,h,he,hfour⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
