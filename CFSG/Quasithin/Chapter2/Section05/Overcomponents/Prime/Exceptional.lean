module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusions
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Source
public import Theory.SpecificGroups.Tits.InvolutoryTwoComponents
public import Theory.SpecificGroups.SU3.TernaryInvolutoryTwoComponents
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRanks
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.AtlasPort.LinearGroups.G2.PSL3TwoParabolics
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.OuterComponents
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallFourExistence
/-!
# Exceptional prime-component exclusions in source 2.5.19

The original component has dihedral or semidihedral Sylow two-subgroups
with noncommuting involutions, and its order is divisible by three. Full
G₂ and Ree parabolics project, modulo a two-group, onto even SL₂ or Suzuki
carriers. Perfectness kills their scalar characters and simplicity makes
the relevant projection faithful, contradicting those source properties.
For outer G₂ actors the actual fixed component is a smaller derived G₂;
its three-rank is at least two, whereas prime-field PSL₂ has three-rank at
most one. This includes the binary fixed-field endpoint.

The Tits and binary derived G₂ endpoints have solvable involutory fixed
groups. The binary derived symplectic endpoint is A₆, whose six-letter
action excludes the prime characteristic of the original PSL₂ component.
All arguments retain the actual actor and fixed component. In particular,
no nonnormality premise is required, so these exclusions also feed the
later prime-core persistence argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
2.5.19, printed pp.560–562, and 2.5.21, pp.566–567. The imported G₂ root
calculations are from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime

private theorem fixed_solvable_of_equiv {E D : Type*} [Group E] [Group D]
    (e : E ≃* D) (hD : ∀ a : MulAut D, orderOf a = 2 → Group.IsSolvable a.fixedSubgroup)
    (a : MulAut E) (ha : orderOf a = 2) : Group.IsSolvable a.fixedSubgroup := by
  let : Group.IsSolvable (MulAut.congr e a).fixedSubgroup :=
    hD _ (((MulAut.congr e).orderOf_eq a).trans ha)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (MulAut.fixedSubgroupCongr e a).toMonoidHom)
    (MulAut.fixedSubgroupCongr e a).injective

private theorem no_component_of_solvable {E : Type*} [Group E] [Group.IsSolvable E]
    (B : Subgroup E) (hB : IsComponent E B) : False := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  exact Group.IsPerfect.not_isSolvable B inferInstance

theorem tits_fixed_solvable {E : Type*} [Group E] (e : E ≃* Tits.ParrottGroup)
    (a : MulAut E) (ha : orderOf a = 2) : Group.IsSolvable a.fixedSubgroup := by
  apply fixed_solvable_of_equiv e _ a ha
  intro b hb
  obtain ⟨P,hP,_,hle⟩ := Tits.InvolutionRootGeometry.involution_fixed_parabolic b hb
  let : Group.IsSolvable P := Tits.InvolutionRootGeometry.isRootParabolic_solvable P hP
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem not_tits_fixed_component {E : Type*} [Group E] (e : E ≃* Tits.ParrottGroup)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) : False := by
  let : Group.IsSolvable a.fixedSubgroup := tits_fixed_solvable e a ha
  exact no_component_of_solvable B hB

theorem g2_derived_fixed_solvable {E : Type*} [Group E]
    (e : E ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (a : MulAut E) (ha : orderOf a = 2) : Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨d⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (ABG.PSU3 3 1 (by decide)) := d.symm.isSimpleGroup
  exact fixed_solvable_of_equiv (e.trans d) Matrix.SU3.ternary_fixed_solvable a ha

theorem not_g2_derived_fixed_component {E : Type*} [Group E]
    (e : E ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) : False := by
  let : Group.IsSolvable a.fixedSubgroup := g2_derived_fixed_solvable e a ha
  exact no_component_of_solvable B hB

theorem prime_threeRank_le_one {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (e : K ≃* PSL(2,ZMod p)) :
    primeRank 3 K ≤ 1 := by
  rw [primeRank_equiv 3 e]
  let P : Sylow 3 PSL(2,ZMod p) := default
  apply P.primeRank_le_one_of_isCyclic
  exact GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (ZMod p)
    (p := p) (f := 1) (by simp) (by simpa using hp) 3 (by decide)
    (by rw [Nat.card_zmod]; exact (Nat.coprime_primes Nat.prime_three
      (Fact.out : p.Prime)).mpr (by omega)) P


private theorem injective_comp_of_two_kernel {K U V : Type*}
    [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    [Group U] [Group V] (q : U →* V) (hq : IsPGroup 2 q.ker)
    (f : K →* U) (hf : Function.Injective f) : Function.Injective (q.comp f) := by
  rcases (inferInstance : (q.comp f).ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact (q.comp f).ker_eq_bot_iff.mp hb
  · let j : K →* q.ker := f.codRestrict q.ker (fun x => by
      have hx : x ∈ (q.comp f).ker := ht ▸ mem_top x
      exact hx)
    have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
    have hp : IsPGroup 2 K := hq.of_injective j hj
    let : Group.IsNilpotent K := hp.isNilpotent
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim

private theorem perfect_character_trivial {K A : Type*} [Group K] [Group.IsPerfect K]
    [CommGroup A] (f : K →* A) (x : K) : f x = 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict x) 1)

private theorem injective_first_of_perfect_two_kernel {K U L A : Type*}
    [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    [Group U] [Group L] [CommGroup A]
    (q : U →* L × A) (hq : IsPGroup 2 q.ker)
    (f : K →* U) (hf : Function.Injective f) :
    Function.Injective ((MonoidHom.fst L A).comp (q.comp f)) := by
  have hi := injective_comp_of_two_kernel q hq f hf
  intro x y h
  apply hi
  apply Prod.ext h
  exact (perfect_character_trivial ((MonoidHom.snd L A).comp (q.comp f)) x).trans
    (perfect_character_trivial ((MonoidHom.snd L A).comp (q.comp f)) y).symm

private theorem sylow_commutative_SL {K F : Type*}
    [Group K] [Finite K] [Field F] [Finite F] [CharP F 2]
    (f : K →* SL(2,F)) (hf : Function.Injective f) (P : Sylow 2 K) :
    IsMulCommutative P :=
  Theory.PSL2.binary_sylow_commutative_of_injective
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL.toMonoidHom.comp f)
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL.injective.comp hf) P

open Atlas.G2 Atlas.G2.LieParabolicSetup in
private theorem g2_parabolic_sylow_commutative {K F : Type*}
    [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    [Field F] [Finite F] [CharP F 2]
    (j : K →* Model F) (hj : Function.Injective j)
    (hle : j.range ≤ parabolic₁ ∨ j.range ≤ parabolic₂) (P : Sylow 2 K) :
    IsMulCommutative P := by
  rcases hle with hle | hle
  · let f : K →* shortPlaneStabilizer (F := F) :=
      j.codRestrict _ (fun x => parabolic₁_le_shortPlaneStabilizer (hle ⟨x,rfl⟩))
    have hlocal (x : K) : j x ∈ local₁ (F := F) := by
      rw [local₁_eq_shortSpecial]
      exact ⟨f x, show shortDet (f x) = 1 from congrArg Units.val
        (perfect_character_trivial (shortDet.toHomUnits.comp f) x), rfl⟩
    let l := j.codRestrict local₁ hlocal
    have hl : Function.Injective l := fun x y h => hj (congrArg Subtype.val h)
    exact sylow_commutative_SL (shortSLHom.comp l)
      (injective_comp_of_two_kernel shortSLHom
        (by rw [shortSLHom_ker]; exact radical₁_isTwoGroup.comap_subtype) l hl) P
  · let f : K →* pointStabilizer (K := F) :=
      j.codRestrict _ (fun x => parabolic_le_pointStabilizer (hle ⟨x,rfl⟩))
    have hlocal (x : K) : j x ∈ local₂ (F := F) := by
      rw [local₂_eq_fixingFirstVector]
      have hx : f x ∈ (lineScalarHom (K := F)).ker :=
        perfect_character_trivial (lineScalarHom.comp f) x
      rwa [lineScalarHom_kernel] at hx
    let l := j.codRestrict local₂ hlocal
    have hl : Function.Injective l := fun x y h => hj (congrArg Subtype.val h)
    exact sylow_commutative_SL (longSLHom.comp l)
      (injective_comp_of_two_kernel longSLHom
        (by rw [longSLHom_ker]; exact radical₂_isTwoGroup.comap_subtype) l hl) P

open Atlas.G2 Atlas.G2.LieParabolicSetup in
private theorem g2_inner_sylow_commutative {K F : Type*}
    [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (a : MulAut (Model F)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup (Model F))
    (f : K →* a.fixedSubgroup) (hf : Function.Injective f) (P : Sylow 2 K) :
    IsMulCommutative P := by
  obtain ⟨x,hx⟩ := hi
  have ho : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot
      (LieAutomorphismExtensions.model_center_eq_bot hF) x).symm.trans
      ((congrArg orderOf hx).trans ha)
  change MulAut.conj x = a at hx
  have hR : zpowers x ≠ ⊥ := by
    intro h
    have hx1 := zpowers_eq_bot.mp h
    simp [hx1] at ho
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,ho,pow_one])
  obtain ⟨g,hcover⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    (zpowers x) hR hp
  have hCN : a.fixedSubgroup ≤ normalizer (zpowers x : Set (Model F)) := by
    rw [←hx,MulAut.fixedSubgroup_conj]
    rw [←centralizer_closure ({x} : Set (Model F)),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  let j : K →* Model F := (MulAut.conj g).toMonoidHom.comp (a.fixedSubgroup.subtype.comp f)
  have hj : Function.Injective j :=
    (MulAut.conj g).injective.comp (a.fixedSubgroup.subtype_injective.comp hf)
  apply g2_parabolic_sylow_commutative j hj _ P
  have hrange : j.range ≤ (normalizer (zpowers x : Set (Model F))).map
      (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨k,rfl⟩
    exact mem_map_of_mem _ (hCN (f k).property)
  exact hcover.imp (hrange.trans ·) (hrange.trans ·)

private theorem g2_derived_threeRank_lower {F : Type*} [Field F] [Finite F] [CharP F 2] :
    2 ≤ primeRank 3 (commutator (Atlas.G2.Model F)) := by
  by_cases hlarge : 2 < Nat.card F
  · let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hlarge
    rw [Group.IsPerfect.commutator_eq_top, primeRank_equiv 3 Subgroup.topEquiv]
    exact Atlas.G2.EvenThreeRank.two_le_primeRank
  · have hcard : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    let e := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv hcard)
    let d : commutator (Atlas.G2.Model F) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
      (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
        rfl))
    rw [primeRank_equiv 3 d]
    exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived

open ComponentRefinement ComponentSelection

theorem source_not_g2_fixed_component {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (eP : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E] [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At E (2^n))
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B) :
    False := by
  obtain ⟨F,hField,hFinite,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let b := MulAut.congr e a
  have hb2 : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  let ef := MulAut.fixedSubgroupCongr e a
  let C := B.map ef.toMonoidHom
  have hC : IsComponent b.fixedSubgroup C := hB.map_equiv ef
  let d : K ≃* C := eK.trans (ef.subgroupMap B)
  have hs := MathieuSourceSetup.small_source_structure c hG hempty hgen hb
  let : IsSimpleGroup K := hs.2.1
  let : IsQuasisimple K :=
    (show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
  by_cases hi : b ∈ MulAut.innerSubgroup (Atlas.G2.Model F)
  · let P : Sylow 2 K := default
    have hP := hs.1.sylowTwoShape P
    let f : K →* b.fixedSubgroup := ef.toMonoidHom.comp (B.subtype.comp eK.toMonoidHom)
    have hf : Function.Injective f := ef.injective.comp (B.subtype_injective.comp eK.injective)
    have hlarge : 2 < Nat.card F := by
      rw [hcard]
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
      omega
    let : IsMulCommutative P := g2_inner_sylow_commutative hlarge b hb2 hi f hf P
    exact hP.rank_and_involutions.2 (fun x y _ _ => Commute.all x y)
  · obtain ⟨σ,m,hmpos,_,_,hfm,_,_,j,_,_,⟨f⟩,_⟩ :=
      Atlas.G2.EvenFieldFixedResidual.outer_fixed_component_descent_of_equiv
        (MulEquiv.refl (Atlas.G2.Model F)) hn hcard b hb2
        (fun g hg => hi ⟨g,hg.symm⟩) C hC
    have hlo := g2_derived_threeRank_lower
      (F := Atlas.G2.EvenFieldFixedResidual.fixedField σ)
    have hup := prime_threeRank_le_one hp eP
    rw [primeRank_equiv 3 (d.trans f)] at hup
    omega

open ReeF4 ReeF4.ConverseParabolics in
private theorem ree_fixed_embeds_parabolic {E : Type*} [Group E]
    [IsSimpleGroup E] [Group.IsPerfect E] {m : ℕ} (hm : 1 ≤ m)
    (e : E ≃* Model m) (a : MulAut E) (ha : orderOf a = 2) :
    ∃ s : ReeF4.LargeLocalSeeds.Side, ∃ f : a.fixedSubgroup →* parabolic m s, Function.Injective f := by
  let : IsSimpleGroup (Model m) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Model m) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hz : center (Model m) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Model m)) inferInstance with h | h
    · exact h
    · let : IsMulCommutative (Model m) := center_eq_top_iff.mp h
      exact (Group.IsPerfect.not_isSolvable (Model m) inferInstance).elim
  let b := MulAut.congr e a
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  obtain ⟨x,hx⟩ := Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one hm b
    (by simpa only [hb] using pow_orderOf_eq_one b)
  have ho : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot hz x).symm.trans ((congrArg orderOf hx).trans hb)
  have hR : zpowers x ≠ ⊥ := by
    intro h
    have hx1 := zpowers_eq_bot.mp h
    simp [hx1] at ho
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,ho,pow_one])
  obtain ⟨g,s,hcover⟩ := normalizer_cover hm (zpowers x) hR hp
  have hCN : b.fixedSubgroup ≤ normalizer (zpowers x : Set (Model m)) := by
    rw [←hx,MulAut.fixedSubgroup_conj]
    rw [←centralizer_closure ({x} : Set (Model m)),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  let j : b.fixedSubgroup →* parabolic m s :=
    ((MulAut.conj g).toMonoidHom.comp b.fixedSubgroup.subtype).codRestrict _
      (fun y => hcover (mem_map_of_mem _ (hCN y.property)))
  have hj : Function.Injective j := fun x y h => Subtype.ext
    ((MulAut.conj g).injective (congrArg Subtype.val h))
  exact ⟨s,j.comp (MulAut.fixedSubgroupCongr e a).toMonoidHom,
    hj.comp (MulAut.fixedSubgroupCongr e a).injective⟩

private theorem source_not_ree_model_fixed_component {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [IsSimpleGroup E] [Group.IsPerfect E]
    {m : ℕ} (hm : 1 ≤ m) (e : E ≃* ReeF4.Model m)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (eK : K ≃* B) : False := by
  have hs := MathieuSourceSetup.small_source_structure c hG hempty hgen hb
  let : IsSimpleGroup K := hs.2.1
  let : IsQuasisimple K :=
    (show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
  obtain ⟨s,f,hf⟩ := ree_fixed_embeds_parabolic hm e a ha
  let j := f.comp (B.subtype.comp eK.toMonoidHom)
  have hj : Function.Injective j := hf.comp (B.subtype_injective.comp eK.injective)
  cases s with
  | linear =>
      let q := ReeF4.ConverseParabolics.linearProjection hm
      have hi := injective_first_of_perfect_two_kernel q
        (ReeF4.ConverseParabolics.linearProjection_ker_isPGroup hm) j hj
      let P : Sylow 2 K := default
      let : IsMulCommutative P := sylow_commutative_SL _ hi P
      exact (hs.1.sylowTwoShape P).rank_and_involutions.2 (fun x y _ _ => Commute.all x y)
  | suzuki =>
      let q := ReeF4.ConverseParabolics.suzukiProjection hm
      have hi := injective_first_of_perfect_two_kernel q
        (ReeF4.ConverseParabolics.suzukiProjection_ker_isPGroup hm) j hj
      exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
        (hs.1.three_dvd_card.trans (Subgroup.card_dvd_of_injective _ hi))

/-- The literal Ree model predicate from the original catalogue supplies the
actual canonical-carrier equivalence used by the parabolic argument. -/
theorem source_not_ree_fixed_component {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [IsSimpleGroup E] [Group.IsPerfect E]
    {m : ℕ} (hm : 1 ≤ m) (hmodel : Chapter1.Section02.LocalModels.IsReeF4At E m)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (eK : K ≃* B) : False := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  exact source_not_ree_model_fixed_component c hG hempty hgen hb hm
    (e.trans d.modelEquiv) a ha B eK

/-- The binary derived symplectic endpoint is A₆; its six-letter action
cannot contain a prime-field PSL₂ of characteristic at least seven. -/
theorem not_symplectic_derived_fixed_component
    {K : Type*} [Group K] {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (eP : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E]
    (e : E ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (a : MulAut E) (B : Subgroup a.fixedSubgroup) (eK : K ≃* B) : False := by
  let d := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  let f : PSL(2,ZMod p) →* Equiv.Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp
      (d.toMonoidHom.comp (a.fixedSubgroup.subtype.comp
        (B.subtype.comp (eK.toMonoidHom.comp eP.symm.toMonoidHom))))
  have hf : Function.Injective f :=
    (alternatingGroup (Fin 6)).subtype_injective.comp (d.injective.comp
      (a.fixedSubgroup.subtype_injective.comp (B.subtype_injective.comp
        (eK.injective.comp eP.symm.injective))))
  exact prime_pslTwo_no_injective_small_fixed (Fact.out : p.Prime) hp
    (Or.inr (Or.inr (Or.inl (by rw [Nat.card_perm]; norm_num)))) f hf

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
