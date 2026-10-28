module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.CoreSections
public import Theory.GroupAction.HomomorphismFixedKernel

/-!
# Faithfulness of the original radical quotient action

The point-core centralizer C_Q(Z) is normal and self-centralizing in Q.
An action fixing such a normal p-subgroup fixes both it and its quotient,
so it has p-group image. Applied inside C_G(z), whose generalized Fitting
subgroup is Q, this proves that C_S(R) is a two-group. The same kernel and
quotient argument on R/Z then makes the S-action kernel a normal two-group;
R=O₂(S) identifies this kernel exactly.

Consequently both S/R and the full N_G(Z)/R act faithfully on the literal
radical quotient, and C_{N_G(Z)}(R)=Z. All action and quotient maps are those
constructed from the original source three-space.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), the tensor argument in (4.4), pp.597–598,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

/-- An action fixing a normal self-centralizing subgroup of a finite p-group
is itself a p-group, provided its action kernel is a p-group. -/
theorem isPGroup_of_fixes_normal_selfCentralizing {P A : Type*} [Group P] [Finite P]
    [Group A] {p : ℕ} (U : Subgroup P) [U.Normal]
    (hU : IsPGroup p U) (hc : Subgroup.centralizer (U : Set P) ≤ U)
    (ρ : A →* MulAut P) (hk : IsPGroup p ρ.ker)
    (hf : ∀ a : A, ∀ u : U, ρ a u = u) : IsPGroup p A := by
  apply (QuotientGroup.mk' U).isPGroup_of_fixes_kernel_and_quotient
    (by rw [QuotientGroup.ker_mk']; exact hU) ρ hk
  · intro a x
    have hmem : x⁻¹ * ρ a x ∈ U := by
      apply hc
      intro u hu
      have he := hf a ⟨x*u*x⁻¹,(inferInstance : U.Normal).conj_mem u hu x⟩
      change ρ a (x*u*x⁻¹) = x*u*x⁻¹ at he
      rw [map_mul,map_mul,map_inv,hf a ⟨u,hu⟩] at he
      have he' : (x⁻¹ * ρ a x)*u*(x⁻¹ * ρ a x)⁻¹=u := by
        calc
          _ = x⁻¹*(ρ a x*u*(ρ a x)⁻¹)*x := by group
          _ = x⁻¹*(x*u*x⁻¹)*x := by rw [he]
          _ = u := by group
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    have he : QuotientGroup.mk' U (x⁻¹ * ρ a x) = 1 :=
      (QuotientGroup.eq_one_iff (N := U) (x⁻¹ * ρ a x)).mpr hmem
    rw [map_mul,map_inv,inv_mul_eq_one] at he
    exact he.symm
  · intro a x
    apply hf a ⟨x.val,?_⟩
    simpa only [QuotientGroup.ker_mk'] using x.property

namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

/-- The original point core acts on the same source three-space. -/
def pointCoreSpaceAction {t : G} (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    ambientCore t →* MulAut d.space :=
  d.normalizerAction.comp (inclusion (d.cores_normalize t ht ht1))

theorem pointCoreSpaceAction_ker {t : G} (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    (d.pointCoreSpaceAction ht ht1).ker = d.S.subgroupOf (ambientCore t) := by
  rw [pointCoreSpaceAction,←MonoidHom.comap_ker,normalizerAction,normalizerMonoidHom_ker]
  rfl

/-- The point-core centralizer of Z is normal and self-centralizing in that core. -/
theorem pointCoreCentralizer_selfCentralizing (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    Subgroup.centralizer (d.S.subgroupOf (ambientCore t) : Set (ambientCore t)) ≤
      d.S.subgroupOf (ambientCore t) := by
  intro q hq u hu
  let uQ : ambientCore t := ⟨u,d.contained_in_cores t ht ht1 hu⟩
  have huS : uQ ∈ d.S.subgroupOf (ambientCore t) :=
    (d.space_le_R h hu).2
  exact congrArg Subtype.val (hq uQ huS)

/-- The centralizer of the source radical in S is a two-group. -/
theorem S_radicalCentralizer_isTwoGroup (h : IsTypeJ4 z) :
    IsPGroup 2 (d.S ⊓ Subgroup.centralizer (d.R : Set G) : Subgroup G) := by
  have hz : z ∈ d.space := by
    rw [space,d.generated]
    exact subset_closure (by simp)
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  let Q := ambientCore z
  let C := d.S ⊓ Subgroup.centralizer (d.R : Set G)
  let U := d.S.subgroupOf Q
  have hQN : d.S ≤ normalizer (Q : Set G) := by
    rw [LocalGeometry.normalizer_ambientCore h]
    exact d.S_le_point_centralizer hz
  let ρ : C →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion (inf_le_left.trans hQN))
  have hfix : ∀ c : C, ∀ u : U, ρ c u = u := by
    intro c u
    apply Subtype.ext
    change (c : G)*(u.val : G)*(c : G)⁻¹=(u.val : G)
    have huR : (u.val : G) ∈ d.R := d.coreCentralizer_le_R hz hz1 ⟨u.val.property,u.property⟩
    rw [←c.property.2 _ huR,mul_inv_cancel_right]
  have hk : IsPGroup 2 ρ.ker := by
    have hmem (c : ρ.ker) : (c.val : G) ∈ Q := by
      have hc : (c.val : G) ∈ centralizer z := d.S_le_point_centralizer hz c.val.property.1
      have hcQ : (⟨(c.val : G),hc⟩ : centralizer z) ∈ core z := by
        apply centralizer_generalizedFitting_le (centralizer z)
        intro u hu
        let uQ : Q := ⟨u.val,mem_map_of_mem (centralizer z).subtype hu⟩
        have he := congrArg (fun a : MulAut Q => (a uQ : G)) c.property
        change (c.val : G)*u.val*(c.val : G)⁻¹=u.val at he
        exact Subtype.ext ((mul_inv_eq_iff_eq_mul.mp he).symm)
      exact mem_map_of_mem (centralizer z).subtype hcQ
    let j : ρ.ker →* Q := (C.subtype.comp ρ.ker.subtype).codRestrict Q hmem
    have hj : Function.Injective j := by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : Q => (x : G)) he
    let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient z) h.extraspecial
    exact (IsExtraspecial.isPGroup 2 Q).of_injective j hj
  let : U.Normal := by
    change (d.S.subgroupOf (ambientCore z)).Normal
    rw [←d.pointCoreSpaceAction_ker hz hz1]
    infer_instance
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient z) h.extraspecial
  exact isPGroup_of_fixes_normal_selfCentralizing U
    ((IsExtraspecial.isPGroup 2 Q).to_subgroup U)
    (d.pointCoreCentralizer_selfCentralizing h hz hz1) ρ hk hfix

attribute [local instance] R_normal_in_S_intrinsic R_normal_in_normalizer

/-- The kernel of the literal S-action on R/Z is a two-group. -/
theorem S_radicalAction_kernel_isTwoGroup (h : IsTypeJ4 z) :
    IsPGroup 2 ((d.SRadicalAction h).comp (QuotientGroup.mk' (d.R.subgroupOf d.S))).ker := by
  let β := (d.SRadicalAction h).comp (QuotientGroup.mk' (d.R.subgroupOf d.S))
  let α : d.S →* MulAut d.R := d.R.normalizerMonoidHom.comp
    (inclusion ((Subgroup.centralizer_le_normalizer _).trans d.R_normalized))
  let ρ := α.comp β.ker.subtype
  let C := d.S ⊓ Subgroup.centralizer (d.R : Set G)
  have hk : IsPGroup 2 ρ.ker := by
    have hc (a : ρ.ker) : (a.val.val : G) ∈ C := by
      refine ⟨a.val.val.property,?_⟩
      intro r hr
      have he := congrArg (fun f : MulAut d.R => (f ⟨r,hr⟩ : G)) a.property
      change (a.val.val : G)*r*(a.val.val : G)⁻¹=r at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    let j : ρ.ker →* C :=
      ((d.S.subtype.comp β.ker.subtype).comp ρ.ker.subtype).codRestrict C hc
    have hj : Function.Injective j := by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : C => (x : G)) he
    exact (d.S_radicalCentralizer_isTwoGroup h).of_injective j hj
  have hR : IsPGroup 2 d.R := by
    rw [d.R_eq_S_twoCore h]
    exact isPGroup_pCoreIn 2 d.S
  apply (QuotientGroup.mk' (center d.R)).isPGroup_of_fixes_kernel_and_quotient
    (by rw [QuotientGroup.ker_mk']; exact hR.to_subgroup _) ρ hk
  · intro a r
    have he := congrArg (fun f : MulAut (d.R ⧸ center d.R) =>
      f (QuotientGroup.mk' (center d.R) r)) a.property
    change d.radicalAction (inclusion (Subgroup.centralizer_le_normalizer _) a.val)
      (QuotientGroup.mk' (center d.R) r) = QuotientGroup.mk' (center d.R) r at he
    rw [d.radicalAction_mk] at he
    exact he
  · intro a r
    have hr : r.val ∈ center d.R := by
      simpa only [QuotientGroup.ker_mk'] using r.property
    have hz : (r.val : G) ∈ d.space := by
      rw [←d.R_center_eq_space h]
      exact mem_map_of_mem _ hr
    apply Subtype.ext
    change (a.val : G)*(r.val : G)*(a.val : G)⁻¹=(r.val : G)
    rw [←a.val.property _ hz,mul_inv_cancel_right]

/-- The S/R conjugation action has no kernel. -/
theorem SRadicalAction_injective (h : IsTypeJ4 z) : Function.Injective (d.SRadicalAction h) := by
  let β := (d.SRadicalAction h).comp (QuotientGroup.mk' (d.R.subgroupOf d.S))
  have hk : β.ker ≤ pCore 2 d.S := le_sSup ⟨inferInstance,d.S_radicalAction_kernel_isTwoGroup h⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.S) a
  have hs : s ∈ β.ker := ha
  have hsR : (s : G) ∈ d.R := by
    rw [d.R_eq_S_twoCore h]
    exact mem_map_of_mem d.S.subtype (hk hs)
  exact mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hsR)

/-- The entire original normalizer quotient acts faithfully on the radical quotient. -/
theorem radicalQuotientAction_injective (h : IsTypeJ4 z) :
    Function.Injective (d.radicalQuotientAction h) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨n,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf (normalizer (d.space : Set G))) a
  have hn : n ∈ d.radicalAction.ker := ha
  have hs : (n : G) ∈ d.S := d.radicalAction_ker_le_S h hn
  let s : d.S := ⟨n.val,hs⟩
  have he : d.SRadicalAction h (QuotientGroup.mk' _ s) = 1 := ha
  have hsR : s ∈ d.R.subgroupOf d.S := (QuotientGroup.eq_one_iff s).mp
    ((d.SRadicalAction_injective h) (he.trans (map_one _).symm))
  exact mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hsR)

/-- The kernel before taking the normalizer quotient is exactly the original R. -/
theorem radicalAction_ker (h : IsTypeJ4 z) :
    d.radicalAction.ker = d.R.subgroupOf (normalizer (d.space : Set G)) := by
  apply le_antisymm ?_ (d.R_le_radicalAction_ker h)
  intro n hn
  apply (QuotientGroup.eq_one_iff n).mp
  apply d.radicalQuotientAction_injective h
  exact (show d.radicalQuotientAction h (QuotientGroup.mk' _ n) = 1 from hn).trans
    (map_one _).symm

/-- The radical has only its own center as centralizer in the original normalizer. -/
theorem normalizer_radical_centralizer (h : IsTypeJ4 z) :
    normalizer (d.space : Set G) ⊓ Subgroup.centralizer (d.R : Set G) = d.space := by
  apply le_antisymm
  · intro n hn
    have hnker : (⟨n,hn.1⟩ : normalizer (d.space : Set G)) ∈ d.radicalAction.ker := by
      apply MulEquiv.ext
      intro v
      obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (center d.R) v
      rw [d.radicalAction_mk]
      apply congrArg (QuotientGroup.mk' (center d.R))
      apply Subtype.ext
      change n*(r : G)*n⁻¹=(r : G)
      rw [←hn.2 r r.property,mul_inv_cancel_right]
    have hnR : n ∈ d.R := (d.radicalAction_ker h).le hnker
    rw [←d.R_center_eq_space h]
    refine ⟨⟨n,hnR⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro r
    exact Subtype.ext (hn.2 r r.property)
  · intro n hn
    refine ⟨d.space.le_normalizer hn,?_⟩
    rw [←d.R_center_eq_space h] at hn
    obtain ⟨n,hn,rfl⟩ := hn
    intro r hr
    exact congrArg Subtype.val ((mem_center_iff.mp hn) ⟨r,hr⟩)

end ThreeSpaceData
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
