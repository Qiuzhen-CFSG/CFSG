module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearModuleAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearWholeAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNaturalResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedBlocks
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedConstituents
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightFourResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedBlocks
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearGeometry
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.OneLayerCore
public import Theory.GroupTheory.PCoreRestriction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.LinearThreePointDisplacement

/-!
# Reciprocal core control and the selected linear-three mixed exclusion: structure at the original group

The original short augmentation component bounds the cubic length in the
reciprocal A₄ residual kernel by one. The selected component's two-core
normalizes that residual: it centralizes the full omega-orbit and hence the
original fixed-line generator. Intersecting with the residual therefore
preserves cubic length. The marked natural module moves under a cubic,
exhausting this bound and giving U(K)=[Ω₁Z(T)^K,K] on the original carrier.

For a weight-four point, P=[V,L₁] is the elementary residual eight-group
already constructed in WeightFourResidual. Its exact commutator with
O₂(L₁) is ⟨z⟩. The elementary point-displacement theorem places that
commutator in U(K), even if the perfect central quotient initially has an
extra double-cover layer. But z centralizes K and U(K) is fixed-free.
This excludes the selected L₃(2) row. The final theorem applies it to the
original mixed pair, deriving augmentation shortness and weight four from
the actual reciprocal radical containments and the same conjugator.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ReciprocalCore` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V U : Subgroup G}

private theorem symmetricFour_cubic_residual_at :
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

private theorem residual_alternatingFour_at (C J Q : Subgroup G)
    (hJ : (primeToResidual 3 C).map C.subtype = J)
    (q : C →* Equiv.Perm (Fin 4)) (hq : Function.Surjective q)
    (hqk : q.ker = Q.subgroupOf C) :
    ∃ f : J →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = Q.subgroupOf J := by
  let R := primeToResidual 3 C
  have hJC : J ≤ C := hJ ▸ map_subtype_le R
  have hr : R.map q = alternatingGroup (Fin 4) :=
    (map_primeToResidual_of_surjective 3 q hq).trans symmetricFour_cubic_residual_at
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

private theorem reciprocal_core_layer_at
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

/-- The original short augmentation component forces the selected linear
component's whole two-core commutator to be its actual moved omega-orbit. -/
theorem original_linear_component_core_layer_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsShort L)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    (ChapterC.blockU K).map K.subtype =
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  let Q := K.pCoreIn 2
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  obtain ⟨DK,q,e,he,_,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨hJK,hrec,_⟩ := ordinary_linear_component_residuals_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK eL
  obtain ⟨_,hCU,hseed,_,_⟩ := linear_component_whole_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hQH : Q ≤ H.pCoreIn 2 := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le K.le_normalizer hTK)
  have hQd : Q ≤ centralizer ({m.constant.val} : Set G) := by
    intro x hx
    have hc := (hseed.symm.le (hQH hx)).2
    exact mem_centralizer_singleton_iff.mpr
      (hc m.constant.val (le_conjugateSpanBy _ _ (m.constant_mem_central_four_at h structural).2)).symm
  let C := K ⊓ centralizer ({m.constant.val} : Set G)
  have hQJ : Q ≤ normalizer (J : Set G) := by
    change Q ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G)
    rw [←hrec,Solvable.firstCentralizerResidual_eq]
    exact (le_inf (pCoreIn_le 2 K) hQd).trans
      (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C)))
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point_at h₀ h structural m hzT hz1 hKz hTK hKM
  obtain ⟨p,hp,hpk⟩ := BinaryLinearThree.natural_point_centralizer K U DK.normalizes q e he w hw
  rw [Solvable.firstCentralizerResidual_eq,hC] at hrec
  obtain ⟨f,hf,hfk⟩ := residual_alternatingFour_at _ J Q hrec p hp hpk
  let fK := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hker : fK.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ q.injective,QuotientGroup.ker_mk']
  have hCK : K ⊓ centralizer (U : Set G) = Q := by
    apply le_antisymm
    · intro x hx
      have hxH : x ∈ H.pCoreIn 2 := hCU.le ⟨mem_sup_left hx.1,hx.2⟩
      exact inf_pCoreIn_le_of_le 2 (show K ≤ H from le_sup_left) ⟨hx.1,hxH⟩
    · exact le_inf (pCoreIn_le 2 K) (fun x hx => (hCU.symm.le (hQH hx)).2)
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup BinaryLinearThree.Group := Matrix.PSL3Two.equiv.isSimpleGroup
  have hfaith := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK
  exact reciprocal_core_layer_at D m hb eL z hzL DK fK
    (q.surjective.comp (QuotientGroup.mk'_surjective _)) hker hfaith.2.1.2.1
    hCK hJK hQJ f hf hfk


/-- The weight-four point cannot have the selected linear-three component
once the original augmentation component is short. The elementary residual
three-space forces the point into the fixed-free natural component layer. -/
theorem original_weight_four_linear_component_false_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsShort L)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (hw : m.weight z = 4) : False := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  let P := ⁅V,J⁆
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hU := original_linear_component_core_layer_at hl h₀ h structural modules D m
    h1332 fixed hindex eL hb z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨DK,q,e,he,hfix,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨hJK,hrec,_⟩ := ordinary_linear_component_residuals_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK eL
  obtain ⟨w,hw1,hC⟩ := component_fixed_generator_point_at h₀ h structural m hzT hz1 hKz hTK hKM
  obtain ⟨p,hp,hpk⟩ := BinaryLinearThree.natural_point_centralizer K U DK.normalizes q e he w hw1
  rw [Solvable.firstCentralizerResidual_eq,hC] at hrec
  obtain ⟨f,hf,hfk⟩ := residual_alternatingFour_at _ J (K.pCoreIn 2) hrec p hp hpk
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
  have hdisp := ChapterC.linearThree_elementary_point_displacement eK Ji Pi hPi fJ
    (hf.comp a.surjective) hfkJ
  have hd := map_mono (f := K.subtype) hdisp
  rw [map_commutator,map_subgroupOf_eq_of_le hPK,
    pCoreIn_subgroupOf 2 J K hJK,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 J).trans hJK),hU] at hd
  have hzU : z.val ∈ U := hd (hdouble.ge (mem_zpowers z.val))
  apply hz1
  have hzfix : z.val ∈ U ⊓ centralizer (K : Set G) :=
    ⟨hzU,fun k hk => mem_centralizer_singleton_iff.mp (hKz hk)⟩
  have hzbot : z.val ∈ (⊥ : Subgroup G) := hfix ▸ hzfix
  exact hzbot

variable {A B : Subgroup G}
/-- Mixed reciprocal containment gives commutation when the original point
centralizer has the selected linear-three component. Both literal radical
containments, the original conjugator and all earlier-source inputs are retained. -/
theorem original_linear_pair_mixed_commute_of_selected_linear_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ = ⊥ := by
  dsimp only
  intro g h₁ h₂
  by_contra hm
  obtain ⟨_,_,_,_,hshort,_,_⟩ := original_linear_pair_mixed_blocks_at
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion g h₁ h₂ hm
  obtain ⟨_,_,hw,_,_⟩ := original_linear_pair_mixed_weight_four_at
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion z hzT hzL hAz g h₁ h₂ hm
  exact original_weight_four_linear_component_false_at hl h₀ h structural modules D m
    h1332 fixed hindexL eL hshort z hzT hzL hKz hHN hKM hfK eK hw

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
