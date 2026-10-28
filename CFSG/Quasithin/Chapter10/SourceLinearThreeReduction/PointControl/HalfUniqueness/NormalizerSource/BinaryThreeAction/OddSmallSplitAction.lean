module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallInnerAction
public import Theory.SpecificGroups.PSL3Two.WreathCubicSplitting

/-!
# Splitting the original module action on the containing Frattini section

Retain Q=O₂(K), K=<O²(H)^E>, and the original natural-module factors
V₁=[V,L] and V₂=V₁ᵗ. The original cubic plane normalizes the action of Q
in the base of SL₃(2) wr C₂. Its coordinate projections occur independently.
Lifting those projections gives Q=C_Q(V₁)C_Q(V₂).

Consequently the images of V₁ and V₂ on Q/Φ(Q) intersect trivially: an
automorphism belonging to both images fixes both centralizer factors and
hence all of Q/Φ(Q). The original exchanger identifies their orders. Thus
the full V-action has square order. In the collapsed case its earlier
order-dividing-four bound now leaves only the trivial image or a four-group.
Every nontrivial image therefore has fixed index at most its squared order;
the previously unresolved order-two case is excluded.

The final applications retain both original source contracts and the same
module, exchanger and containing-core action. Nontriviality of this image,
its placement relative to the containing quotient, and exclusion of the
remaining configuration are not asserted. They and final assembly remain
with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the sole external
premise, with its final discharge retained by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

private theorem LiftData.centralizes_first (f : LiftData s hz)
    (q : localJoin T L) (hr : (f.hom q).right = 1) (hl : (f.hom q).left 1 = 1) :
    (q:G) ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  let a' : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨a,ha⟩
  let v := factorProduct s hz (a',1)
  have he : action (f.hom q) (fullCoordinates s hz v) = fullCoordinates s hz v := by
    funext i
    rw [action_apply]
    simp only [hr,inv_one,one_mul]
    rw [coordinates_factorProduct]
    by_cases hi : i=1
    · subst i; simp [hl]
    · simp only [hi,if_false]
      rw [show partnerCoordinates s hz 1 = 1 from map_one _]
      simp
  rw [←f.equivariant] at he
  have hh := congrArg Subtype.val ((fullCoordinates s hz).injective he)
  rw [joinAction_apply,factorProduct_apply] at hh
  simp only [OneMemClass.coe_one,mul_one] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem LiftData.centralizes_second (f : LiftData s hz)
    (q : localJoin T L) (hr : (f.hom q).right = 1)
    (hl : (f.hom q).left other = 1) :
    (q:G) ∈ centralizer
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom : Set G) := by
  rw [mem_centralizer_iff]
  intro b hb
  let b' : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) := ⟨b,hb⟩
  let v := factorProduct s hz (1,b')
  have he : action (f.hom q) (fullCoordinates s hz v) = fullCoordinates s hz v := by
    funext i
    rw [action_apply]
    simp only [hr,inv_one,one_mul]
    rw [coordinates_factorProduct]
    rcases bit_cases i with rfl | rfl
    · simp
    · simp [hl]
  rw [←f.equivariant] at he
  have hh := congrArg Subtype.val ((fullCoordinates s hz).injective he)
  rw [joinAction_apply,factorProduct_apply] at hh
  simp only [OneMemClass.coe_one,one_mul] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

namespace Parabolics
variable {H P : Subgroup G}

private theorem Data.core_coordinatePart_lift (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (q : localJoin T L) (hq : (q:G) ∈ (enlargedResidual T L H).pCoreIn 2)
    (i : Bit) :
    ∃ q' : localJoin T L, (q':G) ∈ (enlargedResidual T L H).pCoreIn 2 ∧
      f.hom q' = Matrix.PSL3Two.WreathPair.CubicSplitting.coordinatePart (f.hom q) i := by
  let J := localJoin T L
  let Q := (enlargedResidual T L H).pCoreIn 2
  let A := P.subgroupOf J
  let U := (Q.subgroupOf J).map f.hom
  have hPJ : P ≤ J := hi.complement_le.trans ((map_subtype_le _).trans h.le_join)
  have ha : IsPGroup 3 A := hi.odd_complement.isPGroup.of_equiv
    (subgroupOfEquivOfLe hPJ).symm
  have hd := ha.disjoint_of_coprime f.kernel_two (by decide : Nat.Coprime 3 2)
  have hinj : Function.Injective (f.hom.subgroupMap A) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    change f.hom.subgroupMap A x = 1 at hx
    exact Subtype.ext (hd.le_bot ⟨x.property,congrArg Subtype.val hx⟩)
  have hcard : Nat.card (A.map f.hom) = 9 := by
    rw [←Nat.card_congr (MulEquiv.ofBijective (f.hom.subgroupMap A)
      ⟨hinj,f.hom.subgroupMap_surjective A⟩).toEquiv]
    exact (Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv).trans hP
  have hPQ : P ≤ normalizer (Q : Set G) :=
    (hi.complement_le.trans h.residual_le_enlargedResidual).trans
      ((enlargedResidual T L H).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQJ : Q ≤ J := h.enlargedResidual_core_le_intersection.trans
    (inf_le_left.trans (inf_le_left.trans le_sup_right))
  have hn : A ≤ normalizer (Q.subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq hQJ]
    exact subgroupOf_mono J hPQ
  have hr : ∀ u ∈ U, u.right = 1 := by
    rintro _ ⟨q,hq,rfl⟩
    exact f.right_eq_one_of_normalizes q (h.enlargedResidual_core_le_intersection hq).1.2
  exact Matrix.PSL3Two.WreathPair.CubicSplitting.coordinatePart_mem
    (A.map f.hom) U hcard ((isPGroup_pCoreIn 2 _).comap_subtype.map f.hom) hr
    ((map_mono hn).trans (le_normalizer_map f.hom)) (f.hom q) (mem_map_of_mem f.hom hq) i

/-- The containing core is generated by the centralizers of the two original
natural-module factors. No new factor or exchanger is chosen. -/
theorem Data.core_eq_sup_factor_centralizers (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    (enlargedResidual T L H).pCoreIn 2 =
      ((enlargedResidual T L H).pCoreIn 2 ⊓ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊔
      ((enlargedResidual T L H).pCoreIn 2 ⊓ centralizer
        ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom : Set G)) := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  have hQJ : Q ≤ localJoin T L := h.enlargedResidual_core_le_intersection.trans
    (inf_le_left.trans (inf_le_left.trans le_sup_right))
  apply le_antisymm
  · intro q hq
    let q' : localJoin T L := ⟨q,hQJ hq⟩
    obtain ⟨a,ha,hea⟩ := h.core_coordinatePart_lift f hi hP q' hq 1
    let b := a⁻¹*q'
    have hb : (b:G) ∈ Q := Q.mul_mem (Q.inv_mem ha) hq
    have hra : (f.hom a).right = 1 := by
      rw [hea]; rfl
    have hrb : (f.hom b).right = 1 := by
      exact f.right_eq_one_of_normalizes b (h.enlargedResidual_core_le_intersection hb).1.2
    have hla : (f.hom a).left other = 1 := by
      rw [hea]; simp [Matrix.PSL3Two.WreathPair.CubicSplitting.coordinatePart]
    have hlb : (f.hom b).left 1 = 1 := by
      simp [b,map_mul,map_inv,hea,Matrix.PSL3Two.WreathPair.CubicSplitting.coordinatePart]
    have hab : (a:G)*(b:G) = q := by change (a:G)*((a:G)⁻¹*q)=q; group
    rw [←hab]
    exact mul_mem (mem_sup_right ⟨ha,f.centralizes_second a hra hla⟩)
      (mem_sup_left ⟨hb,f.centralizes_first b hrb hlb⟩)
  · exact sup_le inf_le_left inf_le_left

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Subgroup Theory.GroupTheory
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

omit [Finite G] in
private theorem coreFrattiniAction_fixes_of_commute
    (a : enlargement T L H) (q : (enlargedResidual T L H).pCoreIn 2)
    (hc : (a:G)*(q:G)=(q:G)*(a:G)) :
    coreFrattiniAction T L H a (QuotientGroup.mk' _ q) = QuotientGroup.mk' _ q := by
  rw [coreFrattiniAction_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  change (a:G)*(q:G)*(a:G)⁻¹=(q:G)
  rw [hc,mul_inv_cancel_right]

/-- The two original module factors have disjoint images on the containing
Frattini section. This is stronger than their original disjointness. -/
theorem Data.factorFrattiniImages_disjoint (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    Disjoint (((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf (enlargement T L H)).map
      (coreFrattiniAction T L H))
      ((((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).subgroupOf
        (enlargement T L H)).map (coreFrattiniAction T L H)) := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let A : Subgroup G := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let π := QuotientGroup.mk' (frattini Q)
  apply disjoint_iff.mpr
  apply bot_unique
  rintro u ⟨⟨a,ha,rfl⟩,⟨b,hb,he⟩⟩
  apply mem_bot.mpr
  apply MulEquiv.ext
  intro w
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) w
  let F := ((coreFrattiniAction T L H a).toMonoidHom.comp π).eqLocus π
  have hA : (Q ⊓ centralizer (A : Set G)).subgroupOf Q ≤ F := by
    intro x hx
    exact coreFrattiniAction_fixes_of_commute a x ((mem_centralizer_iff.mp hx.2) a ha)
  have hB : (Q ⊓ centralizer (B : Set G)).subgroupOf Q ≤ F := by
    intro x hx
    change coreFrattiniAction T L H a (π x) = π x
    rw [←he]
    exact coreFrattiniAction_fixes_of_commute b x ((mem_centralizer_iff.mp hx.2) b hb)
  have htop : (⊤ : Subgroup Q) ≤ F := by
    have hh := sup_le hA hB
    rw [←subgroupOf_sup inf_le_left inf_le_left,
      ←h.core_eq_sup_factor_centralizers f hi hP,subgroupOf_self] at hh
    exact hh
  exact htop (mem_top q)

/-- The original exchanger identifies the two actual action images. -/
theorem Data.factorFrattiniImages_card_eq (h : Data D H) (s : NaturalData D) :
    Nat.card ((((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).subgroupOf
      (enlargement T L H)).map (coreFrattiniAction T L H)) =
    Nat.card (((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf (enlargement T L H)).map
      (coreFrattiniAction T L H)) := by
  let E := enlargement T L H
  let a := coreFrattiniAction T L H
  let A : Subgroup G := ⁅D.fullModule,L⁆
  let t : E := ⟨s.exchange,h.sylow_le.trans le_sup_right s.exchange_mem⟩
  have hAE : A ≤ E := (selected_moved_le s).trans (h.fullModule_le_enlargement s.full_eq_local)
  have he : ((A.map (MulAut.conj s.exchange).toMonoidHom).subgroupOf E).map a =
      ((A.subgroupOf E).map a).map (MulAut.conj (a t)).toMonoidHom := by
    ext u
    constructor
    · rintro ⟨b,hb,rfl⟩
      obtain ⟨x,hx,hxb⟩ := hb
      let x' : E := ⟨x,hAE hx⟩
      refine ⟨a x',mem_map_of_mem a hx,?_⟩
      have hb' : t*x'*t⁻¹=b := Subtype.ext hxb
      change a t * a x' * (a t)⁻¹ = a b
      rw [←map_inv,←map_mul,←map_mul,hb']
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨t*x*t⁻¹,?_,?_⟩
      · exact mem_map_of_mem (MulAut.conj s.exchange).toMonoidHom hx
      · change a (t*x*t⁻¹) = a t * a x * (a t)⁻¹
        rw [map_mul,map_mul,map_inv]
  change Nat.card (((A.map (MulAut.conj s.exchange).toMonoidHom).subgroupOf E).map a) = _
  rw [he,card_map_of_injective (MulAut.conj (a t)).injective]

/-- The whole original module image is the product of its two exchanged,
disjoint factor images, hence has square order. -/
theorem Data.moduleFrattiniImage_card_square (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    Nat.card (moduleFrattiniImage D H) =
      Nat.card (((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf (enlargement T L H)).map
        (coreFrattiniAction T L H)) ^ 2 := by
  let E := enlargement T L H
  let a := coreFrattiniAction T L H
  let A := ((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf E).map a
  let B := (((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).subgroupOf E).map a
  have hVE := h.fullModule_le_enlargement s.full_eq_local
  have hgen : A ⊔ B = moduleFrattiniImage D H := by
    rw [←Subgroup.map_sup,←subgroupOf_sup ((selected_moved_le s).trans hVE)
      ((selected_partner_le s).trans hVE),←s.generated]
    rfl
  have hAB : A ≤ centralizer (B : Set _) := by
    rintro u ⟨x,hx,rfl⟩ v ⟨y,hy,rfl⟩
    let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
    have heG : (y:G)*(x:G)=(x:G)*(y:G) :=
      congrArg (fun z : D.fullModule => (z:G))
        (mul_comm (⟨y,selected_partner_le s hy⟩ : D.fullModule) ⟨x,selected_moved_le s hx⟩)
    have he : y*x=x*y := Subtype.ext heG
    change a y * a x = a x * a y
    rw [←map_mul,←map_mul,he]
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B
    (h.factorFrattiniImages_disjoint f hi hP) hAB
  rw [←hgen,←Nat.card_congr e.toEquiv,Nat.card_prod]
  have hcard : Nat.card B = Nat.card A := h.factorFrattiniImages_card_eq s
  rw [hcard,pow_two]

/-- Collapse leaves only the trivial or order-four module action; in particular
no surviving action of order two is possible. -/
theorem Data.collapsed_moduleFrattiniImage_bot_or_four (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    moduleFrattiniImage D H = ⊥ ∨ Nat.card (moduleFrattiniImage D H) = 4 := by
  have hsq := h.moduleFrattiniImage_card_square f hi hP
  have hd := h.collapsed_moduleFrattiniImage_card_dvd f hn hi hP hc
  have hpos := Nat.card_pos (α := moduleFrattiniImage D H)
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  let n := Nat.card (((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf (enlargement T L H)).map
    (coreFrattiniAction T L H))
  have hn : n = 1 ∨ n = 2 := by
    have hnpos : 0 < n := Nat.card_pos
    have hntwo : n ≤ 2 := by change Nat.card (moduleFrattiniImage D H) = n ^ 2 at hsq; nlinarith
    omega
  rcases hn with hn | hn
  · left
    apply eq_bot_of_card_eq
    change Nat.card (moduleFrattiniImage D H) = n ^ 2 at hsq
    simpa [hn] using hsq
  · right
    change Nat.card (moduleFrattiniImage D H) = n ^ 2 at hsq
    simpa [hn] using hsq

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Every nontrivial original module image is now a genuine four-group with
the fixed-index bound by its squared order. -/
theorem Data.collapsed_nontrivial_moduleFrattiniImage (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    Nat.card (moduleFrattiniImage D H) = 4 ∧
      (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ≤
        Nat.card (moduleFrattiniImage D H) ^ 2 := by
  have hfour := (h.collapsed_moduleFrattiniImage_bot_or_four f hn hi hP hc).resolve_left hne
  exact ⟨hfour,h.collapsed_moduleFrattiniImage_four_bound f hi hP hc hfour⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Subgroup Theory.GroupTheory
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The source configuration has either trivial original module action or a
quadratic four-group with the required index-square bound, on the same
containing-core Frattini section. No nontriviality or inner placement is assumed. -/
theorem SourceCubicNormalizerEnlargement.exists_split_module_action
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      Function.Injective (h.coreQuotientFrattiniAction hn) ∧
      IsElementaryAbelian 2 (moduleFrattiniImage D H) ∧
      commutatorAction₂ (moduleFrattiniImage D H) (CoreFrattiniSection T L H) = ⊥ ∧
      (moduleFrattiniImage D H = ⊥ ∨
        Nat.card (moduleFrattiniImage D H) = 4 ∧
        (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ≤
          Nat.card (moduleFrattiniImage D H) ^ 2) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  refine ⟨H,P,h,hn,hs.toLocalInput,h.coreQuotientFrattiniAction_injective hn,
    h.moduleFrattiniImage_elementary hfull,h.moduleFrattiniImage_quadratic hfull,?_⟩
  rcases h.collapsed_moduleFrattiniImage_bot_or_four f hn hs.toLocalInput hP hcollapse with hh | hh
  · exact Or.inl hh
  · exact Or.inr ⟨hh,h.collapsed_moduleFrattiniImage_four_bound f hs.toLocalInput hP hcollapse hh⟩

/-- Both original contracts retain the original source configuration, with the
order-two module-action case now excluded by the two actual natural factors. -/
theorem sourceContracts_or_splitModuleAction (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, Data D H ∧
          IsElementaryAbelian 2 (moduleFrattiniImage D H) ∧
          commutatorAction₂ (moduleFrattiniImage D H) (CoreFrattiniSection T L H) = ⊥ ∧
          (moduleFrattiniImage D H = ⊥ ∨
            Nat.card (moduleFrattiniImage D H) = 4 ∧
            (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ≤
              Nat.card (moduleFrattiniImage D H) ^ 2) := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,_,h,_,_,_,hel,hq,hcases⟩ := hc.exists_split_module_action
    exact Or.inr ⟨L,D,hc,H,h,hel,hq,hcases⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
