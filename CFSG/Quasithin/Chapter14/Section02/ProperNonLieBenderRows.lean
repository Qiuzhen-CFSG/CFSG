module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleFixed
public import Theory.Mathieu.M11.Properties.Centralizer
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.Definitions


/-!
# Non-Lie quotient exclusions for the marked paired residual

A subgroup of cubic rank at least two, fixed by the actual two-central action
on a quasisimple component, retains that rank through its central two-core
quotient. Its image would force nine to divide the corresponding involution
centralizer. The native Mathieu and Hall--Janko orders exclude this.

The last theorem uses the literal residual maps of the proper branch. Pair
placement and cubic rank remain explicit: they are supplied only by the later
binary-pair packet and must not be used to infer the earlier containing-row
selection, which also permits Suzuki factors.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986, the paired-residual
contradiction after containing-row selection and the later A.3.18 packet.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter14.Section02
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_pair_false
    (L K : Subgroup G) (z : G) (a : MulAut L)
    (ha : ∀ x : L, (a x : G) = z * (x : G) * z⁻¹)
    [IsQuasisimple L] (hinner : TwoCentralInner a)
    {H : Type*} [Group H] [Finite H] (hz : center H = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* H)
    (hbound : ∀ t : H, orderOf t = 2 → TwoCentral t →
      ¬ 9 ∣ Nat.card (centralizer ({t} : Set H)))
    (hKL : K ≤ L) (hKC : K ≤ centralizer ({z} : Set G))
    (hr : 2 ≤ primeRank 3 K) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hcentral : f.ker ≤ center L := by
    rw [hk]
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    exact (le_solvableRadical (pCore 2 L) inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  obtain ⟨P,hP⟩ := hinner.2.2
  obtain ⟨t,ht,htc,heq⟩ := MulAut.exists_twoCentral_model_of_central_cover f hf
    hcentral hz a hinner.1 hinner.2.1 P (fun x hx => hP ⟨x,hx⟩)
  let g : K →* centralizer ({t} : Set H) :=
    (f.comp (inclusion hKL)).codRestrict _ (fun x => by
      change f (inclusion hKL x) ∈ centralizer ({t} : Set H)
      rw [←MulAut.fixedSubgroup_conj,MulAut.mem_fixedSubgroup,←heq]
      apply congrArg f
      apply Subtype.ext
      rw [ha]
      change z * (x : G) * z⁻¹ = (x : G)
      have hc := mem_centralizer_singleton_iff.mp (hKC x.property)
      rw [←hc,mul_inv_cancel_right])
  let j : g.ker →* f.ker := {
    toFun x := ⟨inclusion hKL x.val, congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun v : f.ker => ((v : L) : G)) h)
  have hgk : IsPGroup 2 g.ker :=
    (show IsPGroup 2 f.ker from hk ▸ pCore_isPGroup).of_injective j hj
  obtain ⟨m,hm⟩ := hgk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hr' : 2 ≤ primeRank 3 (centralizer ({t} : Set H)) :=
    hr.trans (primeRank_le_of_coprime_ker 3 g hcop)
  apply hbound t ht htc
  obtain ⟨E,_,hEc⟩ := exists_elementaryAbelian_card_primeRank
    (G := centralizer ({t} : Set H)) (p := 3)
  exact (show 3 ^ 2 ∣ Nat.card E from hEc ▸ Nat.pow_dvd_pow 3 hr').trans
    E.card_subgroup_dvd_card

private theorem m11_centralizer_not_nine (t : Sporadic.Mathieu.M11)
    (ht : orderOf t = 2) : ¬ 9 ∣ Nat.card (centralizer ({t} : Set _)) := by
  rw [card_centralizer_eq_of_isConj _ _
    (Sporadic.Mathieu.m11_involution_isConj_generatorA t ht)]
  change ¬ 9 ∣ Nat.card Sporadic.Mathieu.m11InvolutionCentralizer
  rw [Sporadic.Mathieu.m11_involutionCentralizer_card]
  decide

private theorem m23_centralizer_not_nine (t : Sporadic.Mathieu.M23)
    (ht : orderOf t = 2) : ¬ 9 ∣ Nat.card (centralizer ({t} : Set _)) := by
  obtain ⟨e⟩ := Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.centralizer_equiv_representative ht
  rw [Nat.card_congr e.toEquiv]
  change ¬ 9 ∣ Nat.card (centralizer ({Sporadic.Mathieu.M23Geometry.involutionRepresentative} : Set _))
  rw [Sporadic.Mathieu.M23Geometry.involutionRepresentative_centralizer_card]
  decide

/-- None of the five Mathieu quotient models can contain the literal
paired residual fixed by the marked two-central action. -/
theorem proper_mathieu_marked_pair_false
    (L K : Subgroup G) (z : G) (a : MulAut L)
    (ha : ∀ x : L, (a x : G) = z * (x : G) * z⁻¹)
    [IsQuasisimple L] (hinner : TwoCentralInner a)
    {name : SporadicName}
    (hname : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24)
    (e : (L ⧸ pCore 2 L) ≃* name.Carrier)
    (hKL : K ≤ L) (hKC : K ≤ centralizer ({z} : Set G))
    (hr : 2 ≤ primeRank 3 K) : False := by
  rcases hname with rfl | rfl | rfl | rfl | rfl
  · exact fixed_pair_false L K z a ha hinner Sporadic.Mathieu.m11_center_eq_bot e
      (fun t ht _ => m11_centralizer_not_nine t ht) hKL hKC hr
  · apply fixed_pair_false L K z a ha hinner Sporadic.Mathieu.m12_center_eq_bot e
      ?_ hKL hKC hr
    intro t ht htc
    rw [Sporadic.Mathieu.M12Involutions.card_centralizer_of_twoCentral t ht htc]
    decide
  · apply fixed_pair_false L K z a ha hinner Sporadic.Mathieu.m22_center_eq_bot e
      ?_ hKL hKC hr
    intro t ht _
    rw [Sporadic.Mathieu.M22FourNormalizers.involution_centralizer_card t ht]
    decide
  · exact fixed_pair_false L K z a ha hinner
      Sporadic.Mathieu.M23Geometry.m23_center_eq_bot e
      (fun t ht _ => m23_centralizer_not_nine t ht) hKL hKC hr
  · apply fixed_pair_false L K z a ha hinner
      Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot e ?_ hKL hKC hr
    intro t ht htc
    rw [Sporadic.Mathieu.M24InvolutionCentralizers.card_centralizer_of_twoCentral t ht htc]
    decide

private theorem j2_center_eq_bot : center Sporadic.LeechRelated.J2.Carrier = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction.inner_conj_injective
  apply MulEquiv.ext
  intro y
  change x * y * x⁻¹ = 1 * y * 1⁻¹
  rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]
  simp

private theorem j2_centralizer_not_nine (t : Sporadic.LeechRelated.J2.Carrier)
    (ht : orderOf t = 2) : ¬ 9 ∣ Nat.card (centralizer ({t} : Set _)) := by
  have ho : orderOf (MulAut.conj t) = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot j2_center_eq_bot) t).trans ht
  rw [←MulAut.fixedSubgroup_conj]
  rcases Sporadic.LeechRelated.J2.InnerInvolutionCores.inner_fixed_representatives
    (MulAut.conj t) ho ⟨t,rfl⟩ with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr Sporadic.LeechRelated.J2.InnerInvolutionCores.a_centralizer_equiv.toEquiv,
      Nat.card_prod, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Sporadic.LeechRelated.J2.InnerInvolutionCores.E4,
      Sporadic.LeechRelated.J2.InnerInvolutionCores.C2, Nat.card_fun, Nat.factorial]
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    change ¬ 9 ∣ Nat.card Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁]
    decide

/-- The paired three-rank also excludes both actual Hall--Janko involution
centralizers, including the two-central class selected by 1.1.5. -/
theorem proper_janko_two_marked_pair_false
    (L K : Subgroup G) (z : G) (a : MulAut L)
    (ha : ∀ x : L, (a x : G) = z * (x : G) * z⁻¹)
    [IsQuasisimple L] (hinner : TwoCentralInner a)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.LeechRelated.J2.Carrier)
    (hKL : K ≤ L) (hKC : K ≤ centralizer ({z} : Set G))
    (hr : 2 ≤ primeRank 3 K) : False :=
  fixed_pair_false L K z a ha hinner j2_center_eq_bot e
    (fun t ht _ => j2_centralizer_not_nine t ht) hKL hKC hr

/-- The containing-row sieve applied to the literal paired residual
`O²(H)` and canonical solvable residual of the original overgroup `X`.
The placement and rank inputs are supplied by `ProperBinaryPairTerminal`. -/
theorem source_proper_paired_quotient_not_mathieu_janko_two
    (X H : Subgroup G) (z : G)
    (a : MulAut ((solvableResidual X).map X.subtype))
    (ha : ∀ x : (solvableResidual X).map X.subtype,
      (a x : G) = z * (x : G) * z⁻¹)
    (hq : IsQuasisimple ((solvableResidual X).map X.subtype))
    (hinner : TwoCentralInner a)
    {name : SporadicName}
    (e : (((solvableResidual X).map X.subtype) ⧸
      pCore 2 ((solvableResidual X).map X.subtype)) ≃* name.Carrier)
    (hpair : (pResidual 2 H).map H.subtype ≤ (solvableResidual X).map X.subtype)
    (hfixed : (pResidual 2 H).map H.subtype ≤ centralizer ({z} : Set G))
    (hr : 2 ≤ primeRank 3 ((pResidual 2 H).map H.subtype)) :
    name ≠ .m11 ∧ name ≠ .m12 ∧ name ≠ .m22 ∧ name ≠ .m23 ∧
      name ≠ .m24 ∧ name ≠ .j2 := by
  let := hq
  have hn (hm : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24) :
      False := proper_mathieu_marked_pair_false _ _ z a ha hinner hm e hpair hfixed hr
  refine ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr (Or.inl h)),
    fun h => hn (Or.inr (Or.inr (Or.inl h))),
    fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))),
    fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))), ?_⟩
  intro h
  subst name
  exact proper_janko_two_marked_pair_false _ _ z a ha hinner e hpair hfixed hr

end CFSG.Quasithin.Chapter14.Section02
