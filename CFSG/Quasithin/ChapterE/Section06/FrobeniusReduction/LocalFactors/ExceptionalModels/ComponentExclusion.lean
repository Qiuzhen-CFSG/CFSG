module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.SymplecticFixed

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.BorelEightFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics

/-!
# The corank-three component exclusion in E.6.25

The symplectic alternative of E.6.8 retains the actual root action of V.
Consequently the involution selected from U acts by a nonidentity element
of that root group. Its fixed group is a root centralizer over the same
field, and the explicit natural extension makes its relative C-component
an L₂(2ⁿ) block. No automorphism-classification or involution-table premise
is needed for this source action.

For the actual two-factor enlargement, the Borel alternatives at corank
three have solvable involution fixed groups. The remaining symplectic
alternative forces the original seed to be an L₂(8) block, incompatible
with either a quasisimple seed or an L₂(4) block. The sufficient model
split uses only the earlier Borel and symplectic records and the corank
bound in the other alternatives; no universal fixed-space equality is
added to the adequate E.6.8 route.

Source: Aschbacher–Smith, E.6.8, pp.247–248, and the exceptional two-factor
argument in E.6.25, p.256 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
open Components
variable {G : Type*} [Group G] {J V : Subgroup G}

/-- The actual root-action involution has the root centralizer’s natural extension. -/
theorem root_action_fixed_naturalExtension {n : ℕ}
    (hn : 1 < n) (hroot : SymplecticRootAction J V n)
    {t : G} (ht : t ∈ V) (a : MulAut J) (ha : orderOf a = 2)
    (hact : ∀ x : J, (a x : G) = t * (x : G) * t⁻¹) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ ∃ (Q : Subgroup a.fixedSubgroup) (_ : Q.Normal),
        Nonempty (NaturalExtension (F := F) Q) := by
  obtain ⟨hVN, F, hF, hfin, hcard, e, r, he⟩ := hroot
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_eq_of_lt (by decide : 2 = 2 ^ 1)
      (Nat.pow_lt_pow_right (by decide) hn)
  have hta : J.normalizerMonoidHom ⟨t, hVN ht⟩ = a := by
    ext x
    exact (hact x).symm
  have haimage : a ∈ (inducedAutomizer J V).map (Automizer J).subtype := by
    refine ⟨J.normalizerMonoidHom.rangeRestrict ⟨t,hVN ht⟩, ?_, hta⟩
    exact ⟨⟨t,hVN ht⟩,ht,rfl⟩
  have har : MulAut.congr e a ∈
      (RootSubgroup.group (F := F) r).map (MulAut.conjNormal (H := commutator (Sp F))) := by
    change _ ∈ (closure (Set.range (rootElement (K := F) r))).map
      (MulAut.conjNormal (H := commutator (Sp F)))
    rw [← he]
    exact mem_map_of_mem _ haimage
  obtain ⟨g,hg,hga⟩ := har
  obtain ⟨s,hs⟩ := (RootSubgroup.mem_group_iff r g).mp hg
  have hsn : s ≠ 0 := by
    intro hz
    have hg1 : g = 1 := by rw [← hs,hz,RootSubgroup.element_zero]
    have haa : a = 1 := (map_eq_one_iff _ (MulAut.congr e).injective).mp
      (by simpa only [hg1, map_one] using hga.symm)
    simp [haa] at ha
  have hgr : InvolutionTypes.IsRootElement g :=
    ⟨1,r,s,hsn,by simpa using hs.symm⟩
  let d := derivedEquivFull_of_card_gt_two hq
  let ef := e.trans d
  have hag : MulAut.congr ef a = MulAut.conj g := by
    apply MulEquiv.ext
    intro x
    have hz := congrArg (fun b : MulAut (commutator (Sp F)) =>
      (b (e (ef.symm x)) : Sp F)) hga
    change g * ((e (ef.symm x) : commutator (Sp F)) : Sp F) * g⁻¹ =
      ((e (a (e.symm (e (ef.symm x)))) : commutator (Sp F)) : Sp F) at hz
    rw [e.symm_apply_apply] at hz
    have hdx : ((e (ef.symm x) : commutator (Sp F)) : Sp F) = x :=
      by simpa only [ef, MulEquiv.trans_apply, d, derivedEquivFull_of_card_gt_two_apply]
        using ef.apply_symm_apply x
    rw [hdx] at hz
    change d (e (a (ef.symm x))) = g * x * g⁻¹
    simpa only [d, derivedEquivFull_of_card_gt_two_apply] using hz.symm
  have hfix : (MulAut.congr ef a).fixedSubgroup = centralizer ({g} : Set (Sp F)) := by
    rw [hag, MulAut.fixedSubgroup_conj]
  let c := (MulAut.fixedSubgroupCongr ef a).trans (MulEquiv.subgroupCongr hfix)
  obtain ⟨Q,hQ,⟨dQ⟩⟩ := InvolutionCentralizers.root_centralizer_naturalExtension hcard hn g hgr
  let := hQ
  exact ⟨F,inferInstance,inferInstance,inferInstance,hcard,Q.comap c.toMonoidHom,
    inferInstance,⟨dQ.comap c⟩⟩


variable [Finite G]

/-- Recognize the original relative C-component over the same field. -/
theorem root_action_cComponent_isL2EvenBlock {L : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hroot : SymplecticRootAction J V n)
    {t : G} (ht : t ∈ V) (a : MulAut J) (ha : orderOf a = 2)
    (hact : ∀ x : J, (a x : G) = t * (x : G) * t⁻¹)
    (hLJ : L ≤ J)
    (hL : L ∈ Chapter1.cComponentsIn (J ⊓ centralizer ({t} : Set G)))
    (hf : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J) :
    ChapterC.IsL2EvenBlock L n := by
  obtain ⟨F, hF, hfin, hc, hcard, Q, hQ, ⟨dQ⟩⟩ :=
    root_action_fixed_naturalExtension hn hroot ht a ha hact
  let := hQ
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_eq_of_lt (by decide : 2 = 2 ^ 1)
      (Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨hBfix,hB⟩ := cComponent_in_fixedSubgroup hL hf
  have heB : L.subgroupOf J = a.fixedSubgroup :=
    le_antisymm hBfix (subgroupOf_eq_top.mp (dQ.cComponent_eq_top hq hB))
  let eL := (subgroupOfEquivOfLe hLJ).symm.trans (MulEquiv.subgroupCongr heB)
  exact isL2EvenBlock_of_naturalExtension (dQ.comap eL) hn hcard

private theorem not_quasisimple_of_short {B : Type*} [Group B]
    [IsQuasisimple B] (h : ChapterC.IsShort B) : False := by
  let := h.finite
  have hc : ChapterC.blockU B ≤ center B :=
    ChapterC.blockU_le_core.trans (IsQuasisimple.pCore_le_center 2)
  exact h.irreducible.1.ne (inf_eq_left.mpr hc)

/-- The constructed corank-three enlargement forces the seed to have parameter three. -/
theorem TwoCentralEnlargement.seed_isL2EvenBlock_three
    {M U L W : Subgroup G}
    (d : TwoCentralEnlargement M V U L W J) (hUV : U ≤ V)
    (hmodels : (∃ n, BorelAlternative M V W J n) ∨
      (∃ n, SymplecticAlternative M V W J n) ∨ actionCorank V J ≤ 2) :
    ChapterC.IsL2EvenBlock L 3 := by
  obtain ⟨t,ht,_,_,_,_,hL,a,ha,hact,⟨S,hS⟩,hf⟩ := d.action
  rcases hmodels with ⟨n,hb⟩ | ⟨n,hs⟩ | hsmall
  · have hn : n = 3 := hb.dimension.trans d.corank
    subst n
    exact (fixedSubgroup_not_solvable hL hf
      (BorelEightFixed.fixedSubgroup_solvable hb.model a ha S hS)).elim
  · rcases hs.local_structure with ⟨_, ⟨hd,_⟩ | ⟨_,hd⟩⟩ | ⟨_,hroot,hd⟩
    · have hr := d.corank
      change actionCorank V J = 3 at hr
      omega
    · have hr := d.corank
      change actionCorank V J = 3 at hr
      omega
    · have hn : n = 3 := hd.symm.trans d.corank
      rw [hn] at hroot
      exact root_action_cComponent_isL2EvenBlock (by decide) hroot (hUV ht)
        a ha hact d.proper.le hL hf
  · have hr := d.corank
    change actionCorank V J = 3 at hr
    omega

/-- The two kinds of seeds remaining in the exceptional E.6.25 argument are excluded. -/
theorem TwoCentralEnlargement.not_quasisimple_or_field_four_seed
    {M U L W : Subgroup G}
    (d : TwoCentralEnlargement M V U L W J) (hUV : U ≤ V)
    (hmodels : (∃ n, BorelAlternative M V W J n) ∨
      (∃ n, SymplecticAlternative M V W J n) ∨ actionCorank V J ≤ 2)
    (hseed : IsQuasisimple L ∨ ChapterC.IsL2EvenBlock L 2) : False := by
  have hb := d.seed_isL2EvenBlock_three hUV hmodels
  rcases hseed with hq | htwo
  · let := hq
    exact not_quasisimple_of_short hb.2.1
  · have he : 2 = 3 := l2_parameter_eq_of_module_card htwo hb.module_card
    omega


/-- Apply the exclusion to the literal full E.6.8 output, preserving its old API. -/
theorem TwoCentralEnlargement.not_component_alternatives
    {M U L W Q : Subgroup G}
    (d : TwoCentralEnlargement M V U L W J) (hUV : U ≤ V)
    (hmodels : ComponentAlternatives M V W Q J)
    (hseed : IsQuasisimple L ∨ ChapterC.IsL2EvenBlock L 2) : False := by
  apply d.not_quasisimple_or_field_four_seed hUV ?_ hseed
  rcases hmodels with hb | hs | hl | ha | ho
  · exact Or.inl hb
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (by rw [hl.dimension]; decide))
  · exact Or.inr (Or.inr ha.dimension)
  · exact Or.inr (Or.inr (by rw [ho.dimension]; decide))

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
