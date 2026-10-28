module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalFixedLine
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSixPointDisplacement
public import Theory.GroupTheory.PResidual.RelativeCoreCommutator
public import Theory.Representation.BinaryPermutation.SixNaturalPointQuotient

/-!
# The selected A₆ component in the original mixed reciprocal pair

The original short augmentation component supplies a one-layer cubic budget
on the actual common A₄ residual. The selected component's two-core
normalizes that residual and centralizes its moved omega-orbit. The orbit
uses the entire budget, identifying it with U(K)=[O₂(K),K] in both the
natural and augmentation rows.

At a weight-four original point, the elementary residual eight-group P
satisfies [P,O₂(J)]=⟨z⟩. Elementary point displacement puts z in U(K),
so the fixed-free natural A₆ row is impossible. In the augmentation row,
the literal KT core commutator gives shortness. The central-cover bound
and the actual fixed line imply |Z(K)|≤4.

The final theorem applies these facts to the original mixed pair, deriving
shortness and weight four from the SAME conjugator and BOTH reciprocal
radical containments. It removes the nonzero-fixed-space premise from the
previous fixed-line placement and quotient-center lower bound. It keeps
J=O^{3′}(C_L(z)), P=[V,J] and F=C_V(L) on their original carriers.

The separate bound |Z(O₂(J)/⟨z⟩)|≤4 is still required to finish this branch;
|Z(K)|≤4 alone does not imply it. Product reciprocity, both graph vertex
types, point fusion and the final offender contradiction remain with this
owner. All genuine earlier-source inputs retain their existing producers
and final discharge with qt-d-1341-fixed-core-source, including universal
nonsolvability, both distinct amalgam inputs and independent LargeDistanceInput
in final assembly. This module does not reconstruct those universal inputs.
Source: Aschbacher–Smith 13.4.13(1) and 13.4.15, printed pp.910–912,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V U : Subgroup G}

private theorem symmetricFour_cubic_residual :
    primeToResidual 3 (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  rw [←twoResidual_eq_primeToResidual_three,Theory.SpecificGroups.SymmetricFourResidual.residual_eq]
  rw [IsPiGroup_iff]
  intro p hp
  rw [Nat.card_perm,Nat.card_fin] at hp
  have hh : p.val ∣ 2 ^ 3 * 3 := hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp hh with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

private theorem residual_alternatingFour (C J Q : Subgroup G)
    (hJ : (primeToResidual 3 C).map C.subtype = J)
    (q : C →* Equiv.Perm (Fin 4)) (hq : Function.Surjective q)
    (hqk : q.ker = Q.subgroupOf C) :
    ∃ f : J →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = Q.subgroupOf J := by
  let R := primeToResidual 3 C
  have hJC : J ≤ C := hJ ▸ map_subtype_le R
  have hr : R.map q = alternatingGroup (Fin 4) :=
    (map_primeToResidual_of_surjective 3 q hq).trans symmetricFour_cubic_residual
  let f : J →* alternatingGroup (Fin 4) :=
    (q.comp (inclusion hJC)).codRestrict _ (fun j => by
      rw [←hr]
      have hj := hJ.ge j.property
      obtain ⟨c,hc,he⟩ := hj
      have he' : c = inclusion hJC j := Subtype.ext he
      exact mem_map_of_mem q (he' ▸ hc))
  refine ⟨f,?_,?_⟩
  · intro a
    have ha : a.val ∈ R.map q := hr.symm ▸ a.property
    obtain ⟨c,hc,hca⟩ := ha
    exact ⟨⟨c.val,hJ.le (mem_map_of_mem C.subtype hc)⟩,Subtype.ext hca⟩
  · ext j
    change f j = 1 ↔ j.val ∈ Q
    rw [Subtype.ext_iff]
    change inclusion hJC j ∈ q.ker ↔ _
    rw [hqk]
    rfl

private theorem reciprocal_core_layer
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzL : z.val ∉ centralizer (L : Set G))
    (DK : ChosenModule T K U)
    {F : Type*} [Group F] [IsSimpleGroup F]
    (q : K →* F) (hq : Function.Surjective q) (hqk : q.ker = pCore 2 K)
    (hpK : IsPPerfect 2 K)
    (hCU : K ⊓ centralizer (U : Set G) = K.pCoreIn 2)
    (hJK : Solvable.firstCentralizerResidual L z.val ≤ K)
    (hQJ : K.pCoreIn 2 ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G))
    (f : Solvable.firstCentralizerResidual L z.val →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f)
    (hfk : f.ker = (K.pCoreIn 2).subgroupOf (Solvable.firstCentralizerResidual L z.val)) :
    (ChapterC.blockU K).map K.subtype = U := by
  let J := Solvable.firstCentralizerResidual L z.val
  let Q := K.pCoreIn 2
  obtain ⟨fL,hfL,_⟩ := core_firstResidual_alternatingFour D m eL z hzL
  have hd : 3 ∣ Nat.card J := by
    apply dvd_trans (b := Nat.card (alternatingGroup (Fin 4)))
    · rw [nat_card_alternatingGroup]; norm_num
    · exact card_dvd_of_surjective fL hfL
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hd
  let A := zpowers (a : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,J.orderOf_coe a,ha]
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hAJ : A ≤ J := zpowers_le.mpr a.property
  have hAK : A ≤ K := hAJ.trans hJK
  have hKQ : K ≤ normalizer (Q : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hQK : Q ≤ K := pCoreIn_le 2 K
  have hker : f.ker.map J.subtype = Q ⊓ J := by
    rw [hfk]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨ha,a.property⟩
    · rintro ⟨hx,hj⟩
      exact ⟨⟨x,hj⟩,hx,rfl⟩
  have hbudget : conjugationCubicLength A Q ≤ 1 := by
    have hh := core_firstResidual_cubic_kernel_le_one D m hb eL z hzL f hf
      (by rw [hfk]; exact (isPGroup_pCoreIn 2 K).comap_subtype) A hA hAJ
    rw [hker,CubicComparison.intersection_length_eq A Q J hA3
      (isPGroup_pCoreIn 2 K) hAJ hQJ (hJK.trans hKQ)] at hh
    exact hh
  have hnot : ¬ A ≤ Q := by
    intro hh
    have hA2 : IsPGroup 2 A := (isPGroup_pCoreIn 2 K).to_le hh
    have he := (IsPGroup.coprime_card_of_ne 2 3 (by decide) A A hA2 hA3).gcd_eq_one
    rw [Nat.gcd_self,hA] at he
    omega
  let Ui := U.subgroupOf K
  let Ai := A.subgroupOf K
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer DK.normalizes
  have hUQ : Ui ≤ pCore 2 K := by
    intro x hx
    exact (mem_map_iff_mem K.subtype_injective).mp (DK.le_componentCore hx)
  have hUi : ⁅Ui,(⊤ : Subgroup K)⁆ = Ui := by
    apply map_injective K.subtype_injective
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le DK.le_component]
    exact DK.eq_commutator.symm
  have himage : Ai.map q ≠ ⊥ := by
    intro hh
    have hi := (map_eq_bot_iff Ai).mp hh
    rw [hqk] at hi
    apply hnot
    intro x hx
    exact mem_map_of_mem K.subtype (hi (show (⟨x,hAK hx⟩ : K) ∈ Ai from hx))
  have hmove : ⁅Ui,Ai⁆ ≠ ⊥ := by
    intro hh
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
    apply hnot
    intro x hx
    apply hCU.le
    refine ⟨hAK hx,?_⟩
    intro v hv
    exact congrArg Subtype.val (hc (show (⟨x,hAK hx⟩ : K) ∈ Ai from hx)
      ⟨v,DK.le_component hv⟩ hv)
  have hbi : conjugationCubicLength Ai (pCore 2 K) ≤ 1 := by
    have he := CubicComparison.length_subgroupOf A Q K hAK hQK
    have heQ : Q.subgroupOf K = pCore 2 K :=
      comap_map_eq_self_of_injective K.subtype_injective _
    rw [heQ] at he
    exact he.trans_le hbudget
  have hi := CubicComparison.core_commutator_eq_of_one_cubic_layer q hq hqk hpK Ui Ai
    hUQ hUi hA3.comap_subtype himage hmove hbi
  change (⁅pCore 2 K,(⊤ : Subgroup K)⁆).map K.subtype = U
  rw [hi,map_subgroupOf_eq_of_le DK.le_component]

/-- The actual selected augmentation component has its entire intrinsic
core commutator equal to its moved omega-orbit, and is short. -/
theorem original_augmentation_component_core_layer
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsShort L)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    (ChapterC.blockU K).map K.subtype = U ∧
      ⁅(K ⊔ (T : Subgroup G)).pCoreIn 2,K⁆ = U ∧ ChapterC.IsShort K := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let H := centralizer ({z.val} : Set G)
  let J := Solvable.firstCentralizerResidual L z.val
  let Q := K.pCoreIn 2
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,_⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hH := (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed
    hindex hM z hzT hzL hK hHN hKM hfK eK).1
  have hCU := (ordinary_six_full_action_kernels h₀ h structural modules D m h1332 fixed
    hindex hM z hzT hzL hK hHN hKM hfK eK).1
  have hQH : Q ≤ H.pCoreIn 2 := by
    change H = _ at hH
    rw [hH]
    exact pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer hTK)
  have hQK : Q ≤ K := pCoreIn_le 2 K
  have hCK : K ⊓ centralizer (U : Set G) = Q := by
    apply le_antisymm
    · intro x hx
      exact inf_pCoreIn_le_of_le 2 hK.1 ⟨hx.1,hCU.le ⟨hK.1 hx.1,hx.2⟩⟩
    · exact le_inf hQK (fun x hx => (hCU.symm.le (hQH hx)).2)
  have hsplit : conjugateSpanBy Z K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 hTK
    rw [component_full_fixed_line h structural z.val hz1 hzT hindex K hK.1 hKM,
      sup_eq_left.mpr (show zpowers z.val ≤ U from hfix.symm ▸ inf_le_left)] at hh
    exact hh
  have hdU : m.constant.val ∈ U := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hrec := component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
    hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
  have hJK : J ≤ K := (component_residual_of_ordinary_six h₀ hzT hz1 hK hHN
    (component_quotient_quasisimple h1332 hfK) eK).2
  have hQd : Q ≤ centralizer ({m.constant.val} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hCK.symm.le hx).2 _ hdU).symm
  have hQJ : Q ≤ normalizer (J : Set G) := by
    change Q ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G)
    rw [←hrec,Solvable.firstCentralizerResidual_eq]
    let C := K ⊓ centralizer ({m.constant.val} : Set G)
    exact (le_inf hQK hQd).trans
      (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C)))
  have hfdata := core_firstResidual_alternatingFour DK mK eK ⟨m.constant.val,hdU⟩ hdK
  rw [hrec] at hfdata
  obtain ⟨f,hf,hfk⟩ := hfdata
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have hfaith := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hU := reciprocal_core_layer D m hb eL z hzL DK q
    (eK.surjective.comp (QuotientGroup.mk'_surjective _)) hk hfaith.2.1.2.1 hCK hJK hQJ f hf hfk
  have hcomm : ⁅(K ⊔ (T : Subgroup G)).pCoreIn 2,K⁆ = U := by
    rw [commutator_pCoreIn_eq_intrinsic_of_subnormal K _ le_sup_left hfK.1.1.subnormal
      hfaith.2.1.2.1]
    change ⁅(pCore 2 K).map K.subtype,K⁆ = U
    simpa only [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hU
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223 ⟨hstar,hfaith.2⟩
    (component_quotient_quasisimple h1332 hfK)
  exact ⟨hU,hcomm,(original_augmentation_short_of_core_commutator hK12 DK mK hcomm).1⟩
/-- In the selected augmentation A₆ row the literal component center has
order at most four. This retains the possible extra central-cover layer. -/
theorem original_augmentation_component_center_card
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsShort L)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) : Nat.card (center K) ≤ 4 := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨hU,_,hshort⟩ := original_augmentation_component_core_layer h₀ h structural modules
    D m h1332 fixed hindex eL hb hM z hzT hzL hK hHN hKM hfK eK hfixed
  change (ChapterC.blockU K).map K.subtype = U at hU
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨DK,⟨mK⟩,_,_,_,_,_⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have he : (ChapterC.blockU K ⊓ center K).map K.subtype = U ⊓ centralizer (K : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨hU.le (mem_map_of_mem K.subtype ha.1),?_⟩
      intro k hk
      exact congrArg Subtype.val ((mem_center_iff.mp ha.2) ⟨k,hk⟩)
    · rintro ⟨hx,hc⟩
      obtain ⟨a,ha,hax⟩ := hU.ge hx
      refine ⟨a,⟨ha,?_⟩,hax⟩
      apply mem_center_iff.mpr
      intro k
      apply Subtype.ext
      change k.val * a.val = a.val * k.val
      change a.val = x at hax
      rw [hax]
      exact hc k.val k.property
  have hcard : Nat.card (ChapterC.blockU K ⊓ center K : Subgroup K) = 2 := by
    rw [←card_map_of_injective K.subtype_injective,he]
    exact mK.card_fixed
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hfK.1.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).surjective
  have hh := hshort.alternatingSix_center_card_le eK
  rwa [hcard] at hh
/-- The natural A₆ row has the same one-layer intrinsic core calculation,
with the literal natural point-centralizer quotient. -/
theorem original_natural_six_component_core_layer
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsShort L)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) = ⊥) :
    (ChapterC.blockU K).map K.subtype =
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let H := centralizer ({z.val} : Set G)
  let J := Solvable.firstCentralizerResidual L z.val
  let Q := K.pCoreIn 2
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  obtain ⟨DK,q,e,he,_,_,_,_⟩ := ordinary_six_component_marking
    h₀ h structural modules D m h1332 hindex z hzT hzL hK.1 hHN hKM hfK eK hfixed
  have hH := (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed
    hindex hM z hzT hzL hK hHN hKM hfK eK).1
  have hCU := (ordinary_six_full_action_kernels h₀ h structural modules D m h1332 fixed
    hindex hM z hzT hzL hK hHN hKM hfK eK).1
  have hQH : Q ≤ H.pCoreIn 2 := by
    change H = _ at hH
    rw [hH]
    exact pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer hTK)
  have hQK : Q ≤ K := pCoreIn_le 2 K
  have hCK : K ⊓ centralizer (U : Set G) = Q := by
    apply le_antisymm
    · intro x hx
      exact inf_pCoreIn_le_of_le 2 hK.1 ⟨hx.1,hCU.le ⟨hK.1 hx.1,hx.2⟩⟩
    · exact le_inf hQK (fun x hx => (hCU.symm.le (hQH hx)).2)
  have hQd : Q ≤ centralizer ({m.constant.val} : Set G) := by
    intro x hx
    have hc := (component_seed_action_kernel h₀ hzT hz1 hK.1 hTK).ge
      ⟨mem_sup_left (hQK hx),(hCK.symm.le hx).2⟩
    exact mem_centralizer_singleton_iff.mpr
      (hc.2 _ (le_conjugateSpanBy _ _ (m.constant_mem_central_four h structural).2)).symm
  have hrec := component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
    hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
  have hJK : J ≤ K := (component_residual_of_ordinary_six h₀ hzT hz1 hK hHN
    (component_quotient_quasisimple h1332 hfK) eK).2
  have hQJ : Q ≤ normalizer (J : Set G) := by
    change Q ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G)
    rw [←hrec,Solvable.firstCentralizerResidual_eq]
    let C := K ⊓ centralizer ({m.constant.val} : Set G)
    exact (le_inf hQK hQd).trans
      (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C)))
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hK.1 hTK hKM
  obtain ⟨p,hp,hpk⟩ := BinaryPermutation.six_natural_point_centralizer K U DK.normalizes q e he w hw
  rw [Solvable.firstCentralizerResidual_eq,hC] at hrec
  obtain ⟨f,hf,hfk⟩ := residual_alternatingFour _ J Q hrec p hp hpk
  let fK := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : fK.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have hfaith := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact reciprocal_core_layer D m hb eL z hzL DK fK
    (eK.surjective.comp (QuotientGroup.mk'_surjective _)) hk hfaith.2.1.2.1 hCK hJK hQJ f hf hfk
/-- The weight-four point cannot have a selected natural A₆ component
once the original augmentation component is short. The elementary residual
three-space forces the point into the fixed-free natural component layer. -/
theorem original_weight_four_natural_six_component_false
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsShort L)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) = ⊥) (hw : m.weight z = 4) : False := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  let P := ⁅V,J⁆
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hU := original_natural_six_component_core_layer h₀ h structural modules D m
    h1332 fixed hindex eL hb hM z hzT hzL hK hHN hKM hfK eK hfixed
  obtain ⟨DK,q,e,he,_,_,_,_⟩ := ordinary_six_component_marking
    h₀ h structural modules D m h1332 hindex z hzT hzL hK.1 hHN hKM hfK eK hfixed
  have hJK := (component_residual_of_ordinary_six h₀ hzT hz1 hK hHN
    (component_quotient_quasisimple h1332 hfK) eK).2
  have hrec := component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
    hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
  obtain ⟨w,hw1,hC⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hK.1 hTK hKM
  obtain ⟨p,hp,hpk⟩ := BinaryPermutation.six_natural_point_centralizer K U DK.normalizes q e he w hw1
  rw [Solvable.firstCentralizerResidual_eq,hC] at hrec
  obtain ⟨f,hf,hfk⟩ := residual_alternatingFour _ J (K.pCoreIn 2) hrec p hp hpk
  have hPJ := (original_weight_four_residual_sixteen D m eL z hzL hw).1
  have hdouble := (original_weight_four_residual_geometry D m eL z hzL hw).2.2
  have hPK : P ≤ K := hPJ.trans ((pCoreIn_le 2 J).trans hJK)
  have hPV : P ≤ V := le_normalizer_iff_commutator_le_left.mp
    ((Solvable.firstCentralizerResidual_le L z.val).trans (inf_le_left.trans D.normalizes))
  let Ji := J.subgroupOf K
  let Pi := P.subgroupOf K
  let a : Ji ≃* J := subgroupOfEquivOfLe hJK
  let fJ := f.comp a.toMonoidHom
  have hfkJ : fJ.ker = (pCore 2 K).subgroupOf Ji := by
    ext x
    change a x ∈ f.ker ↔ x.val ∈ pCore 2 K
    rw [hfk]
    exact mem_map_iff_mem K.subtype_injective
  let := D.elementary
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_le hPV
  let : IsElementaryAbelian 2 Pi := IsElementaryAbelian.comap_of_injective
    K.subtype K.subtype_injective P
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hfK.1.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).surjective
  have hPi : Pi ≤ Ji.pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 J K hJK]
    exact subgroupOf_mono K hPJ
  have hdisp := ChapterC.alternatingSix_elementary_point_displacement eK Ji Pi hPi fJ
    (hf.comp a.surjective) hfkJ
  have hd := map_mono (f := K.subtype) hdisp
  rw [map_commutator,map_subgroupOf_eq_of_le hPK,
    pCoreIn_subgroupOf 2 J K hJK,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 J).trans hJK),hU] at hd
  have hzU : z.val ∈ U := hd (hdouble.ge (mem_zpowers z.val))
  apply hz1
  have hzfix : z.val ∈ U ⊓ centralizer (K : Set G) :=
    ⟨hzU,fun k hk => mem_centralizer_singleton_iff.mp (hK.1 hk)⟩
  have hzbot : z.val ∈ (⊥ : Subgroup G) := hfixed ▸ hzfix
  exact hzbot

open Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

/-- The original mixed A₆ pair selects the augmentation row, identifies its
intrinsic block layer, bounds its component center, and supplies the literal
sixteen-group and quotient-center lower bound without a fixed-space premise. -/
theorem original_linear_pair_mixed_six_center_bounds
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    let J := Solvable.firstCentralizerResidual L z.val
    let P := ⁅V,J⁆
    let F := V ⊓ centralizer (L : Set G)
    let Q := J.pCoreIn 2
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
        Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥ ∧
      ChapterC.IsShort K ∧ Nat.card (center K) ≤ 4 ∧
      (ChapterC.blockU K).map K.subtype =
        ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ∧
      F ≤ J ∧ P ⊔ F ≤ Q ∧ Nat.card (P ⊔ F : Subgroup G) = 16 ∧
        ⁅P ⊔ F,Q⁆ = zpowers z.val ∧
        ∃ hn : ((zpowers z.val).subgroupOf Q).Normal,
          letI := hn
          8 ≤ Nat.card (center (Q ⧸ (zpowers z.val).subgroupOf Q)) := by
  dsimp only
  intro g h₁ h₂ hm
  obtain ⟨_,_,hw,_,_⟩ := original_linear_pair_mixed_weight_four
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion z hzT hzL hAz g h₁ h₂ hm
  obtain ⟨_,_,_,_,hshort,_,_⟩ := original_linear_pair_mixed_blocks
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion g h₁ h₂ hm
  have hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥ := by
    intro hf
    exact original_weight_four_natural_six_component_false h₀ h structural modules D m
      h1332 fixed hindexL eL hshort hM z hzT hzL hK hHN hKM hfK eK hf hw
  obtain ⟨hU,_,hshortK⟩ := original_augmentation_component_core_layer h₀ h structural modules
    D m h1332 fixed hindexL eL hshort hM z hzT hzL hK hHN hKM hfK eK hfixed
  have hcK := original_augmentation_component_center_card h₀ h structural modules D m
    h1332 fixed hindexL eL hshort hM z hzT hzL hK hHN hKM hfK eK hfixed
  have hF := original_weight_four_reciprocal_fixed_line h₀ h structural D m h1332 fixed
    hindexL eL z hzT hzL hw hK hHN hKM hfK eK hfixed
  obtain ⟨_,_,hc,hd,hPQ⟩ := original_weight_four_residual_sixteen D m eL z hzL hw
  exact ⟨hfixed,hshortK,hcK,hU,hF,hPQ hF,hc,hd,
    original_weight_four_residual_center_lower D m eL z hzL hw hF⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
