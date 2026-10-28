module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.EndpointBounds
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import Theory.GroupAction.FourElementTwoAction
public import Theory.Representation.BinaryOffender.QuadraticDualOffender
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Excluding three invariant cubic support planes

Every two-group action on a binary plane is quadratic and has a fixed
line. The literal support-sum map therefore makes every two-subgroup act
quadratically with fixed codimension at most three. Cubic ratio two forces
a Sylow two-subgroup to have order two. Its unique involution class and
generation by the starred actors then force an involution to move all
three support planes. Its displacement has rank three, contradicting the
chosen rank-two involution.

This proves the three-factor exclusion in Aschbacher--Smith, D.2.25,
printed p.190, using the original representation and support factors.
-/

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree

private theorem two_group_plane_data
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) A W)
    (hA : IsPGroup 2 A) (hdim : Module.finrank (ZMod 2) W = 2) :
    IsQuadratic σ ⊤ ∧ 1 ≤ Module.finrank (ZMod 2) (fixedSpace σ ⊤) := by
  let := Representation.BinaryGroupAction.action σ
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hc : Nat.card (Multiplicative W) = 4 := by
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hdim]
    rfl
  have hq := two_group_action_on_four_is_quadratic hA hc
  have hquad : IsQuadratic σ ⊤ := by
    intro a _ b _ w
    let v := Multiplicative.ofAdd w
    have hd : v⁻¹ * b • v ∈ commutatorAction A (Multiplicative W) :=
      subset_closure ⟨b,v,mem_top _,rfl⟩
    have hdd : (v⁻¹ * b • v)⁻¹ * a • (v⁻¹ * b • v) ∈
        commutatorAction₂ A (Multiplicative W) :=
      subset_closure ⟨a,_,hd,rfl⟩
    rw [hq,mem_bot] at hdd
    have he := inv_mul_eq_one.mp hdd
    have hh := congrArg Multiplicative.toAdd he
    change -w + σ b w = σ a (-w + σ b w) at hh
    simpa only [← sub_eq_neg_add] using hh.symm
  refine ⟨hquad,?_⟩
  obtain ⟨v,hv,hne⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := Multiplicative W) (by rw [hc]; decide)
    (a := (1 : Multiplicative W)) (by intro a; exact smul_one a)
  have hfix : v.toAdd ∈ fixedSpace σ ⊤ := by
    intro a
    exact congrArg Multiplicative.toAdd (hv a.val)
  have hnon : Nontrivial (fixedSpace σ ⊤) := by
    apply nontrivial_of_ne (⟨v.toAdd,hfix⟩ : fixedSpace σ ⊤) 0
    intro he
    apply hne
    exact (congrArg Multiplicative.ofAdd (congrArg Subtype.val he)).symm
  let := hnon
  exact Module.finrank_pos

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {P : Subgroup G} {s : ℕ} (d : FittingConfigurations.SupportFactors ρ P s)

omit [Finite G] in
/-- Any two-subgroup preserving the support planes acts quadratically and
has fixed codimension at most the number of those planes. -/
public theorem supportFactors_two_group_data (S : Subgroup G) (hS : IsPGroup 2 S)
    (hn : ∀ i, S ≤ normalizer (d.ambient i : Set G)) :
    IsQuadratic ρ S ∧ fixedCodim ρ S ≤ s := by
  classical
  let U (i : Fin s) := subspaceCommutator ρ ⊤ (d.ambient i)
  have hs (i : Fin s) : S ≤ subspaceStabilizer ρ (U i) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) (hn i)
  let σ (i : Fin s) : Representation (ZMod 2) S (U i) :=
    (stabilizerRepresentation ρ (U i)).comp (inclusion (hs i))
  have hdata (i : Fin s) := two_group_plane_data (σ i) hS (d.support_dim i)
  have hquad : IsQuadratic ρ S := by
    intro a ha b hb v
    obtain ⟨w,rfl⟩ := d.add_bijective.2 v
    rw [map_sum, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg Subtype.val ((hdata i).1 ⟨a,ha⟩ (mem_top _) ⟨b,hb⟩ (mem_top _) (w i))
  let F : ((i : Fin s) → fixedSpace (σ i) ⊤) →ₗ[ZMod 2] fixedSpace ρ S :=
    { toFun := fun w => ⟨∑ i, ((w i : U i) : V),by
        intro a
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg Subtype.val ((w i).property ⟨a,mem_top _⟩)⟩
      map_add' := by intro w z; apply Subtype.ext; simp [Finset.sum_add_distrib]
      map_smul' := by intro c w; apply Subtype.ext; simp [Finset.smul_sum] }
  have hFi : Function.Injective F := by
    intro w z he
    have hh := d.add_bijective.1 (congrArg Subtype.val he)
    funext i
    exact Subtype.ext (congrFun hh i)
  have hlow : s ≤ Module.finrank (ZMod 2) (fixedSpace ρ S) := by
    calc
      s = ∑ i : Fin s, 1 := by simp
      _ ≤ ∑ i : Fin s, Module.finrank (ZMod 2) (fixedSpace (σ i) ⊤) :=
        Finset.sum_le_sum fun i _ => (hdata i).2
      _ = Module.finrank (ZMod 2) ((i : Fin s) → fixedSpace (σ i) ⊤) :=
        (Module.finrank_pi_fintype (R := ZMod 2)).symm
      _ ≤ _ := LinearMap.finrank_le_finrank_of_injective hFi
  have hfull := d.finrank_eq ρ
  have hdim := fixedCodim_add_finrank ρ S
  exact ⟨hquad,by omega⟩


private theorem plane_involution_fixed_line
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) A W)
    (hdim : Module.finrank (ZMod 2) W = 2) (t : A) (ht : t^2=1)
    (hne : σ t ≠ 1) : Module.finrank (ZMod 2) (fixedSpace σ (zpowers t)) = 1 := by
  have hle : (σ t - 1).range ≤ (σ t - 1).ker := by
    rintro _ ⟨v,rfl⟩
    exact sub_eq_zero.mpr (involution_fixes_displacement σ
      (by simpa only [pow_two] using ht) v)
  have hpos : Module.finrank (ZMod 2) (σ t - 1).range ≠ 0 := by
    intro hz
    exact hne (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  have hsum := (σ t - 1).finrank_range_add_finrank_ker
  have hbound := Submodule.finrank_mono hle
  have he : fixedSpace σ (zpowers t) = (σ t - 1).ker := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero.symm
  rw [he]
  omega

/-- The three globally invariant support planes are impossible at cubic
ratio two when the starred actors generate the original group. -/
public theorem not_three_invariant_supports
    (hf : Function.Injective ρ) (d : FittingConfigurations.SupportFactors ρ P 3)
    (hn : ∀ g : G, ∀ i, g ∈ normalizer (d.ambient i : Set G))
    (hgen : Jhat ρ = ⊤) (hratio : cubicRatio ρ = 2)
    (t : G) (ht : IsInvolution t)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2) : False := by
  classical
  let T := zpowers t
  have hT : IsPGroup 2 T := IsPGroup.of_card
    (show Nat.card T = 2^1 by rw [Nat.card_zpowers,orderOf_eq_prime ht.2 ht.1]; rfl)
  obtain ⟨S,hTS⟩ := hT.exists_le_sylow
  have htS : t ∈ (S : Subgroup G) := hTS (mem_zpowers t)
  obtain ⟨hquad,hcodim⟩ := supportFactors_two_group_data ρ d (S : Subgroup G)
    S.isPGroup' (fun i g _ => hn g i)
  have hSe : IsElementaryTwo (S : Subgroup G) :=
    ⟨by intro he; rw [he,mem_bot] at htS; exact ht.1 htS,
      elementary_of_faithful_quadratic ρ hf _ hquad⟩
  have hratioS : (2 : ℝ≥0∞) ≤ actionRatio ρ (S : Subgroup G) := by
    rw [← hratio]
    exact iInf_le_of_le _ (iInf_le_of_le ⟨hSe,isCubic_of_isQuadratic hquad⟩ le_rfl)
  have hmul : 2 * rank (S : Subgroup G) ≤ fixedCodim ρ (S : Subgroup G) := by
    rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl (by
      exact_mod_cast (Nat.ne_of_gt hSe.rank_pos))) (Or.inr (by simp))] at hratioS
    exact_mod_cast hratioS
  have hSr : rank (S : Subgroup G) = 1 := by have := hSe.rank_pos; omega
  have hScard : Nat.card S = 2 := by rw [hSe.card_eq_two_pow_rank,hSr]; rfl
  let : IsCyclic S := isCyclic_of_prime_card hScard
  have hconj (a : G) (ha : orderOf a = 2) : IsConj a t := by
    obtain ⟨b,hb⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ha)
    have hbo : orderOf b = 2 := by
      rw [← Subgroup.orderOf_coe]
      obtain ⟨g,hg⟩ := isConj_iff.mp hb
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq a).trans ha
    have hto : orderOf (⟨t,htS⟩ : S) = 2 := by
      rw [Subgroup.orderOf_mk,orderOf_eq_prime ht.2 ht.1]
    have he := IsCyclic.eq_of_orderOf_eq_two hbo hto
    simpa only [he] using hb
  let U (i : Fin 3) := subspaceCommutator ρ ⊤ (d.ambient i)
  have hs (i : Fin 3) : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (U i) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) (fun g _ => hn g i)
  let σ (i : Fin 3) : Representation (ZMod 2) G (U i) :=
    (stabilizerRepresentation ρ (U i)).comp
      { toFun := fun g => ⟨g,hs i (mem_top g)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  have hnon (i : Fin 3) : σ i t ≠ 1 := by
    intro he
    have het : (σ i).asGroupHom t = 1 := Units.ext he
    have hkill : Jhat ρ ≤ (σ i).asGroupHom.ker := by
      apply sSup_le
      intro A hA a ha
      by_cases ha1 : a = 1
      · exact ha1 ▸ (σ i).asGroupHom.ker.one_mem
      let : IsElementaryAbelian 2 A := hA.1.2.1.2
      have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
      have hh := (σ i).asGroupHom.map_isConj (hconj a (orderOf_eq_prime ha2 ha1))
      rw [het] at hh
      exact isConj_one_left.mp hh
    have htriv (a : G) : σ i a = 1 := by
      have hh := hkill (hgen.symm ▸ mem_top a)
      exact congrArg Units.val hh
    have hfixed : U i ≤ fixedSpace ρ (d.ambient i) := by
      intro v hv a
      exact congrArg Subtype.val (LinearMap.congr_fun (htriv a.val) ⟨v,hv⟩)
    have hPi : Nat.card (d.ambient i) = 3 :=
      (card_map_of_injective P.subtype_injective).trans (d.card_factor i)
    have hc := FittingConfigurations.odd_fixed_moved_complement ρ
      (show Odd (Nat.card (d.ambient i)) by rw [hPi]; decide)
    have hb : U i = ⊥ := by
      exact (inf_eq_left.mpr hfixed).symm.trans hc.disjoint.eq_bot
    have hd := d.support_dim i
    change Module.finrank (ZMod 2) (U i) = 2 at hd
    rw [hb,finrank_bot] at hd
    omega
  have hfixed (i : Fin 3) : Module.finrank (ZMod 2)
      (U i ⊓ fixedSpace ρ T : Submodule (ZMod 2) V) = 1 := by
    have hd := plane_involution_fixed_line (σ i) (d.support_dim i) t ht.2 (hnon i)
    have hm : (fixedSpace (σ i) T).map (U i).subtype = U i ⊓ fixedSpace ρ T := by
      ext v
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨w.property,fun a => congrArg Subtype.val (hw a)⟩
      · rintro ⟨hv,hvfix⟩
        exact ⟨⟨v,hv⟩,fun a => Subtype.ext (hvfix a),rfl⟩
    rw [← hm,Submodule.finrank_map_subtype_eq]
    exact hd
  have hd := d.fixedCodim_eq_of_fixed_lines ρ T (fun i g _ => hs i (mem_top g)) hfixed
  have hh : fixedCodim ρ T ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact hsmall
  omega

end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
